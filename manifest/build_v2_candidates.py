#!/usr/bin/env python3
"""Build the initial v2 candidate list and non-gold review batches.

The v2 scope is deliberately narrower than all Formal Conjectures declarations:

* keep every current bundled gold task;
* keep current deferred formal-proof candidates as internet-enabled non-gold
  tasks;
* add `category research solved` declarations without bundled oracles;
* add paired prove/refute tasks for `category research open` declarations whose
  statements do not use `answer(sorry)`;
* exclude `answer(sorry)` statements.
"""

from __future__ import annotations

import argparse
import csv
import datetime as dt
import importlib.util
import json
import re
import sys
from pathlib import Path


BUCKET_GOLD = "gold_solution"
BUCKET_DEFERRED = "deferred_formal_candidate"
BUCKET_INFORMAL = "informal_proof"
BUCKET_OPEN = "open_problem"

OPEN_PROVE = "prove"
OPEN_REFUTE = "refute"


def load_build_manifest_module():
    path = Path(__file__).with_name("build_manifest.py")
    spec = importlib.util.spec_from_file_location("formal_conjectures_bench_build_manifest", path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"Could not load {path}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


bm = load_build_manifest_module()


def normalized_header_has_answer_sorry(header: str) -> bool:
    return "answer(sorry" in re.sub(r"\s+", "", header)


def has_research_solved(category: list[str]) -> bool:
    return "research" in category and "solved" in category


def has_research_open(category: list[str]) -> bool:
    return "research" in category and "open" in category


def select_formal_proof(formal_proofs: list[dict]) -> dict | None:
    selected = next(
        (p for p in formal_proofs if p["kind"] == "formal_conjectures" and p["url"]),
        None,
    )
    selected = selected or next((p for p in formal_proofs if p["kind"] == "lean4" and p["url"]), None)
    selected = selected or next((p for p in formal_proofs if p["url"]), None)
    selected = selected or (formal_proofs[0] if formal_proofs else None)
    return selected


def selected_oracle(formal_proofs: list[dict]) -> dict:
    selected = select_formal_proof(formal_proofs)
    if selected is None:
        return {
            "kind": "none",
            "formal_proof_kind": None,
            "url": "",
            "licence_status": "not_applicable",
            "redistribution_status": "not_applicable",
        }
    return {
        "kind": bm.classify_oracle(selected["kind"], selected["url"]),
        "formal_proof_kind": selected["kind"],
        "url": selected["url"],
        "licence_status": "unreviewed",
        "redistribution_status": "unreviewed",
    }


def current_manifest_maps(path: Path) -> tuple[dict[str, dict], dict[tuple[str, str], dict], dict[str, dict]]:
    manifest = json.loads(path.read_text(encoding="utf-8"))
    by_name = {item["theorem_name"]: item for item in manifest["instances"]}
    by_source_local = {
        (item["source_file"], item["local_declaration_name"]): item
        for item in manifest["instances"]
    }
    by_id = {item["instance_id"]: item for item in manifest["instances"]}
    return by_name, by_source_local, by_id


def base_instance_id(source_file: str, theorem_name: str) -> str:
    path_part = source_file.removeprefix("FormalConjectures/").removesuffix(".lean")
    return f"{bm.slugify(path_part)}-{bm.slugify(theorem_name.split('.')[-1])}"


def allocate_instance_id(
    *,
    source_file: str,
    theorem_name: str,
    current: dict | None,
    used_ids: set[str],
) -> str:
    if current is not None:
        used_ids.add(current["instance_id"])
        return current["instance_id"]

    base = base_instance_id(source_file, theorem_name)
    candidate = base
    suffix = 2
    while candidate in used_ids:
        candidate = f"{base}-{suffix}"
        suffix += 1
    used_ids.add(candidate)
    return candidate


def record_from_source(
    *,
    source_file: str,
    lines: list[str],
    block,
    current_by_name: dict[str, dict],
    current_by_source_local: dict[tuple[str, str], dict],
    used_ids: set[str],
) -> dict | None:
    declaration = bm.find_declaration(lines, block.end_line)
    if declaration is None:
        return None

    declaration_line, declaration_kind, local_name = declaration
    namespaces = bm.namespace_stack_before(lines, declaration_line)
    theorem_name = ".".join([*namespaces, local_name]) if namespaces else local_name
    header = bm.extract_header(lines, declaration_line)
    formal_proofs = [
        {"kind": match.group(1), "url": match.group(2)}
        for match in bm.FORMAL_PROOF_RE.finditer(block.text)
        if match.group(1) in {"lean4", "formal_conjectures"}
    ]
    current = current_by_name.get(theorem_name) or current_by_source_local.get((source_file, local_name))
    category = bm.parse_category(block.text)
    instance_id = allocate_instance_id(
        source_file=source_file,
        theorem_name=theorem_name,
        current=current,
        used_ids=used_ids,
    )

    if current is not None:
        instance = dict(current)
        instance["instance_id"] = instance_id
        if current.get("inclusion_status") != "included":
            instance["theorem_name"] = theorem_name
            instance["namespace"] = namespaces
        instance["local_declaration_name"] = local_name
        instance["declaration_kind"] = declaration_kind
        instance["source_file"] = source_file
        instance["attribute_line"] = block.start_line
        instance["declaration_line"] = declaration_line
        instance["theorem_header"] = header
        instance["category"] = instance.get("category") or category
        instance["ams_tags"] = instance.get("ams_tags") or bm.parse_ams(block.text)
        return instance

    contains_answer_elaborator = "answer(" in header
    uses_answer_sorry = normalized_header_has_answer_sorry(header)
    return {
        "instance_id": instance_id,
        "theorem_name": theorem_name,
        "local_declaration_name": local_name,
        "declaration_kind": declaration_kind,
        "source_file": source_file,
        "attribute_line": block.start_line,
        "declaration_line": declaration_line,
        "namespace": namespaces,
        "theorem_header": header,
        "formal_proofs": formal_proofs,
        "selected_oracle": selected_oracle(formal_proofs),
        "category": category,
        "ams_tags": bm.parse_ams(block.text),
        "contains_answer_elaborator": contains_answer_elaborator,
        "uses_answer_sorry": uses_answer_sorry,
        "inclusion_status": "candidate",
        "exclusion_reason": None,
    }


def v2_instance(instance: dict, bucket: str) -> dict:
    result = dict(instance)
    result["benchmark_bucket"] = bucket
    result["allow_internet"] = bucket != BUCKET_GOLD
    if bucket == BUCKET_GOLD:
        result["oracle_status"] = "bundled"
    elif bucket == BUCKET_DEFERRED:
        result["oracle_status"] = "known_external"
    else:
        result["oracle_status"] = "none"
    return result


def open_problem_task_id(base: str, polarity: str, used_ids: set[str]) -> str:
    candidate = f"{base}-{polarity}"
    suffix = 2
    while candidate in used_ids:
        candidate = f"{base}-{polarity}-{suffix}"
        suffix += 1
    used_ids.add(candidate)
    return candidate


def theorem_name_in_namespace(namespace: list[str], local_name: str) -> str:
    return ".".join([*namespace, local_name]) if namespace else local_name


def open_problem_pair(record: dict, used_ids: set[str]) -> tuple[list[dict], dict]:
    source_instance_id = record["instance_id"]
    pair_id = f"open-problem/{source_instance_id}"
    namespace = record.get("namespace", [])
    source_theorem_name = record["theorem_name"]

    prove = v2_instance(record, BUCKET_OPEN)
    prove["instance_id"] = open_problem_task_id(source_instance_id, OPEN_PROVE, used_ids)
    prove["open_problem_pair_id"] = pair_id
    prove["open_problem_polarity"] = OPEN_PROVE
    prove["source_instance_id"] = source_instance_id
    prove["source_theorem_name"] = source_theorem_name

    refute = v2_instance(record, BUCKET_OPEN)
    refute["instance_id"] = open_problem_task_id(source_instance_id, OPEN_REFUTE, used_ids)
    refute["open_problem_pair_id"] = pair_id
    refute["open_problem_polarity"] = OPEN_REFUTE
    refute["source_instance_id"] = source_instance_id
    refute["source_theorem_name"] = source_theorem_name
    refute["source_local_declaration_name"] = record["local_declaration_name"]
    refute["local_declaration_name"] = "formal_conjectures_bench_refutation"
    refute["declaration_kind"] = "theorem"
    refute["theorem_name"] = theorem_name_in_namespace(
        namespace,
        refute["local_declaration_name"],
    )

    pair = {
        "pair_id": pair_id,
        "source_instance_id": source_instance_id,
        "source_theorem_name": source_theorem_name,
        "source_file": record["source_file"],
        "declaration_line": record["declaration_line"],
        "prove_task_id": prove["instance_id"],
        "refute_task_id": refute["instance_id"],
        "benchmark_bucket": BUCKET_OPEN,
        "allow_internet": True,
    }
    return [prove, refute], pair


def exclusion_row(instance: dict, reason: str, detail: str = "") -> dict[str, str]:
    return {
        "instance_id": instance.get("instance_id", ""),
        "theorem_name": instance.get("theorem_name", ""),
        "source_file": instance.get("source_file", ""),
        "declaration_line": str(instance.get("declaration_line", "")),
        "category": " ".join(instance.get("category", [])),
        "reason": reason,
        "detail": detail,
    }


def extract_category_records(
    source: Path,
    current_by_name: dict[str, dict],
    current_by_source_local: dict[tuple[str, str], dict],
    used_ids: set[str],
) -> list[dict]:
    root = source / "FormalConjectures"
    records: list[dict] = []
    for file_path in sorted(root.rglob("*.lean")):
        rel = file_path.relative_to(source).as_posix()
        if rel.startswith("FormalConjectures/Util/") or rel.startswith("FormalConjectures/Subsets/"):
            continue
        lines = bm.read_text(file_path).splitlines()
        for block in bm.collect_attribute_blocks(lines):
            if not bm.parse_category(block.text):
                continue
            try:
                record = record_from_source(
                    source_file=rel,
                    lines=lines,
                    block=block,
                    current_by_name=current_by_name,
                    current_by_source_local=current_by_source_local,
                    used_ids=used_ids,
                )
            except Exception as exc:  # Keep extraction auditable instead of aborting the whole run.
                records.append(
                    {
                        "instance_id": "",
                        "theorem_name": "",
                        "source_file": rel,
                        "declaration_line": "",
                        "category": [],
                        "_extract_error": str(exc),
                    }
                )
                continue
            if record is not None:
                records.append(record)
    return records


def build_v2_instances(
    source: Path,
    current_manifest: Path,
) -> tuple[list[dict], list[dict[str, str]], dict, list[dict]]:
    current = json.loads(current_manifest.read_text(encoding="utf-8"))
    current_by_name, current_by_source_local, current_by_id = current_manifest_maps(current_manifest)
    used_ids = set(current_by_id)
    selected_by_id: dict[str, dict] = {}
    exclusions: list[dict[str, str]] = []
    open_pairs: list[dict] = []

    for instance in current["instances"]:
        if instance.get("inclusion_status") == "included":
            selected_by_id[instance["instance_id"]] = v2_instance(instance, BUCKET_GOLD)
        elif instance.get("inclusion_status") == "candidate" and instance.get("v1_0_0_status") == "deferred":
            source_file = instance.get("source_file", "")
            if source_file.startswith(("FormalConjectures/Util/", "FormalConjectures/Subsets/")):
                exclusions.append(exclusion_row(instance, "support_file", "deferred candidate"))
            elif instance.get("uses_answer_sorry"):
                exclusions.append(exclusion_row(instance, "answer_sorry", "deferred formal candidate"))
            else:
                selected_by_id[instance["instance_id"]] = v2_instance(instance, BUCKET_DEFERRED)

    for record in extract_category_records(source, current_by_name, current_by_source_local, used_ids):
        if record.get("_extract_error"):
            exclusions.append(exclusion_row(record, "extract_error", record["_extract_error"]))
            continue
        if record["instance_id"] in selected_by_id:
            continue
        category = record.get("category", [])
        if record.get("uses_answer_sorry"):
            exclusions.append(exclusion_row(record, "answer_sorry"))
        elif has_research_open(category):
            tasks, pair = open_problem_pair(record, used_ids)
            for task in tasks:
                selected_by_id[task["instance_id"]] = task
            open_pairs.append(pair)
        elif has_research_solved(category):
            selected_by_id[record["instance_id"]] = v2_instance(record, BUCKET_INFORMAL)
        else:
            exclusions.append(exclusion_row(record, "out_of_scope_category"))

    bucket_order = {BUCKET_GOLD: 0, BUCKET_DEFERRED: 1, BUCKET_INFORMAL: 2, BUCKET_OPEN: 3}
    instances = sorted(
        selected_by_id.values(),
        key=lambda item: (
            bucket_order.get(item["benchmark_bucket"], 99),
            item["source_file"],
            item["declaration_line"],
            item.get("open_problem_polarity", ""),
            item["instance_id"],
        ),
    )
    source_metadata = dict(current["source"])
    source_metadata["v2_generated_at"] = dt.datetime.now(dt.UTC).replace(microsecond=0).isoformat()
    source_metadata["v2_instance_count"] = len(instances)
    source_metadata["v2_exclusion_count"] = len(exclusions)
    source_metadata["v2_open_problem_pair_count"] = len(open_pairs)
    return instances, exclusions, source_metadata, open_pairs


def write_json(path: Path, data: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(data, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")


def write_exclusions(path: Path, rows: list[dict[str, str]]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    fieldnames = ["instance_id", "theorem_name", "source_file", "declaration_line", "category", "reason", "detail"]
    with path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=fieldnames, lineterminator="\n")
        writer.writeheader()
        writer.writerows(rows)


def write_batch_if_changed(path: Path, payload: dict) -> None:
    if path.exists():
        current = json.loads(path.read_text(encoding="utf-8"))
        if current.get("instance_ids") == payload.get("instance_ids"):
            return
    write_json(path, payload)


def write_batch_chunks(
    path: Path,
    instances: list[dict],
    batch_size: int,
    source_metadata: dict,
    start_batch_no: int,
) -> int:
    batch_no = start_batch_no
    for index in range(0, len(instances), batch_size):
        chunk = instances[index : index + batch_size]
        write_batch_if_changed(
            path / f"batch-{batch_no:03d}.json",
            {
                "schema_version": 1,
                "batch_id": f"batch-{batch_no:03d}",
                "batch_size": len(chunk),
                "source": source_metadata,
                "instance_ids": [item["instance_id"] for item in chunk],
            },
        )
        batch_no += 1
    return batch_no


def write_batches(path: Path, instances: list[dict], batch_size: int, source_metadata: dict) -> None:
    path.mkdir(parents=True, exist_ok=True)
    known_non_gold = [
        item
        for item in instances
        if item["benchmark_bucket"] not in {BUCKET_GOLD, BUCKET_OPEN}
    ]
    open_problem_tasks = [item for item in instances if item["benchmark_bucket"] == BUCKET_OPEN]
    next_batch_no = write_batch_chunks(path, known_non_gold, batch_size, source_metadata, 1)
    write_batch_chunks(path, open_problem_tasks, batch_size, source_metadata, next_batch_no)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--source", type=Path, required=True)
    parser.add_argument("--current-manifest", type=Path, default=Path("manifest/manifest.json"))
    parser.add_argument("--out", type=Path, default=Path("manifest/v2_candidates.json"))
    parser.add_argument("--batches-dir", type=Path, default=Path("manifest/v2_batches"))
    parser.add_argument("--exclusions", type=Path, default=Path("manifest/v2_exclusions.csv"))
    parser.add_argument("--open-pairs", type=Path, default=Path("manifest/v2_open_pairs.json"))
    parser.add_argument("--batch-size", type=int, default=100)
    args = parser.parse_args()

    instances, exclusions, source_metadata, open_pairs = build_v2_instances(
        args.source.resolve(),
        args.current_manifest,
    )
    counts: dict[str, int] = {}
    for instance in instances:
        counts[instance["benchmark_bucket"]] = counts.get(instance["benchmark_bucket"], 0) + 1

    write_json(
        args.out,
        {
            "schema_version": 2,
            "source": source_metadata,
            "v2_scope": {
                "included_buckets": [BUCKET_GOLD, BUCKET_DEFERRED, BUCKET_INFORMAL, BUCKET_OPEN],
                "excluded_statement_shapes": ["answer(sorry)"],
                "excluded_categories": ["API", "test", "textbook"],
            },
            "bucket_counts": counts,
            "open_problem_pairs": open_pairs,
            "instances": instances,
        },
    )
    write_json(
        args.open_pairs,
        {
            "schema_version": 1,
            "source": source_metadata,
            "pair_count": len(open_pairs),
            "scoring": {
                "pass_condition": "at least one of prove_task_id or refute_task_id passes",
                "flag_condition": "both prove_task_id and refute_task_id pass",
            },
            "pairs": open_pairs,
        },
    )
    write_exclusions(args.exclusions, exclusions)
    write_batches(args.batches_dir, instances, args.batch_size, source_metadata)
    print(f"Wrote {args.out} with {len(instances)} v2 instance(s): {counts}")
    print(f"Wrote {args.open_pairs} with {len(open_pairs)} open-problem pair(s)")
    print(f"Wrote {args.exclusions} with {len(exclusions)} exclusion row(s)")
    print(f"Wrote batches in {args.batches_dir}")


if __name__ == "__main__":
    main()
