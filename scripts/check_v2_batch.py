#!/usr/bin/env python3
"""Cheap structural checks for generated v2 task batches."""

from __future__ import annotations

import argparse
import json
import shutil
import subprocess
import sys
import tempfile
import tomllib
from pathlib import Path


TARGET_MARKER = "-- FORMAL_CONJECTURES_BENCH_TARGET_BEGIN"


def normalized_contains_answer_sorry(text: str) -> bool:
    normalized = "".join(text.split())
    return "answer(sorry" in normalized


def fail(issues: list[str]) -> None:
    print("v2 batch check failed:", file=sys.stderr)
    for issue in issues:
        print(f"- {issue}", file=sys.stderr)
    sys.exit(1)


def load_ids(path: Path) -> list[str]:
    data = json.loads(path.read_text(encoding="utf-8"))
    if isinstance(data, list):
        return [str(item) for item in data]
    if isinstance(data, dict) and "instance_ids" in data:
        return [str(item) for item in data["instance_ids"]]
    if isinstance(data, dict) and "instances" in data:
        return [str(item["instance_id"]) for item in data["instances"]]
    raise ValueError(f"Could not read instance ids from {path}")


def read_toml(path: Path) -> dict:
    return tomllib.loads(path.read_text(encoding="utf-8"))


def rewrite_dependency_paths(root: Path, formal_conjectures_source: Path) -> None:
    replacement = str(formal_conjectures_source.resolve())
    for path in [root / "lakefile.toml", root / "lake-manifest.json"]:
        text = path.read_text(encoding="utf-8")
        path.write_text(text.replace("/opt/formal-conjectures", replacement), encoding="utf-8")


def lean_smoke(task_dir: Path, formal_conjectures_source: Path, timeout: int) -> str | None:
    with tempfile.TemporaryDirectory(prefix="formal-conjectures-bench-v2-smoke-") as temp_dir:
        project = Path(temp_dir)
        shutil.copytree(task_dir / "environment" / "data", project, dirs_exist_ok=True)
        shutil.rmtree(project / "checker", ignore_errors=True)
        rewrite_dependency_paths(project, formal_conjectures_source)
        result = subprocess.run(
            ["lake", "build", "+FormalConjecturesBench.Target"],
            cwd=project,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            timeout=timeout,
        )
    if result.returncode != 0:
        return result.stdout
    return None


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--manifest", type=Path, required=True)
    parser.add_argument("--batch", type=Path, required=True)
    parser.add_argument("--tasks-dir", type=Path, required=True)
    parser.add_argument("--formal-conjectures-source", type=Path, default=Path(".cache/formal-conjectures"))
    parser.add_argument("--lean-smoke", type=int, default=0, help="Build the first N generated placeholder targets")
    parser.add_argument("--lean-timeout-sec", type=int, default=180)
    args = parser.parse_args()

    manifest = json.loads(args.manifest.read_text(encoding="utf-8"))
    by_id = {item["instance_id"]: item for item in manifest["instances"]}
    pair_by_task_id = {}
    for pair in manifest.get("open_problem_pairs", []):
        pair_by_task_id[pair.get("prove_task_id")] = (pair, "prove")
        pair_by_task_id[pair.get("refute_task_id")] = (pair, "refute")
    ids = load_ids(args.batch)
    id_set = set(ids)
    issues: list[str] = []
    counts: dict[str, int] = {}

    for index, instance_id in enumerate(ids):
        instance = by_id.get(instance_id)
        if instance is None:
            issues.append(f"{instance_id}: missing from manifest")
            continue
        bucket = instance.get("benchmark_bucket")
        counts[bucket] = counts.get(bucket, 0) + 1
        expected_internet = bool(instance.get("allow_internet"))
        task_dir = args.tasks_dir / instance_id
        task_toml = task_dir / "task.toml"
        target = task_dir / "environment" / "data" / "FormalConjecturesBench" / "Target.lean"
        solution_target = task_dir / "solution" / "Target.lean"

        if not task_dir.exists():
            issues.append(f"{instance_id}: missing generated task directory")
            continue
        if not task_toml.exists():
            issues.append(f"{instance_id}: missing task.toml")
            continue
        if not target.exists():
            issues.append(f"{instance_id}: missing environment Target.lean")
            continue

        task_data = read_toml(task_toml)
        metadata = task_data.get("metadata", {})
        environment = task_data.get("environment", {})
        if metadata.get("benchmark_bucket") != bucket:
            issues.append(
                f"{instance_id}: task.toml benchmark_bucket={metadata.get('benchmark_bucket')!r}, expected {bucket!r}"
            )
        if bool(environment.get("allow_internet")) != expected_internet:
            issues.append(
                f"{instance_id}: allow_internet={environment.get('allow_internet')!r}, expected {expected_internet!r}"
            )
        if bucket == "open_problem":
            pair_id = instance.get("open_problem_pair_id")
            polarity = instance.get("open_problem_polarity")
            if not pair_id or polarity not in {"prove", "refute"}:
                issues.append(f"{instance_id}: open_problem task is missing pair metadata")
            pair_info = pair_by_task_id.get(instance_id)
            if pair_info is None:
                issues.append(f"{instance_id}: missing from manifest open_problem_pairs")
            else:
                pair, expected_polarity = pair_info
                if polarity != expected_polarity:
                    issues.append(
                        f"{instance_id}: open_problem_polarity={polarity!r}, expected {expected_polarity!r}"
                    )
                counterpart = (
                    pair.get("refute_task_id")
                    if expected_polarity == "prove"
                    else pair.get("prove_task_id")
                )
                if counterpart not in id_set:
                    issues.append(f"{instance_id}: paired task {counterpart} is not in this batch")

        text = target.read_text(encoding="utf-8")
        if TARGET_MARKER not in text:
            issues.append(f"{instance_id}: target marker missing")
            proof_region = text
        else:
            proof_region = text.split(TARGET_MARKER, 1)[1]
        if normalized_contains_answer_sorry(proof_region):
            issues.append(f"{instance_id}: target theorem region still contains answer(sorry)")
        if bucket == "open_problem" and instance.get("open_problem_polarity") == "refute":
            if "theorem formal_conjectures_bench_refutation :" not in proof_region:
                issues.append(f"{instance_id}: refutation task is missing the benchmark refutation theorem")
            if "¬ (" not in proof_region:
                issues.append(f"{instance_id}: refutation target does not negate the frozen statement")
        if bucket != "gold_solution" and solution_target.exists():
            issues.append(f"{instance_id}: non-gold task unexpectedly has solution/Target.lean")
        if bucket == "gold_solution" and not solution_target.exists():
            issues.append(f"{instance_id}: gold task is missing solution/Target.lean")
        if args.lean_smoke and index < args.lean_smoke:
            try:
                output = lean_smoke(task_dir, args.formal_conjectures_source, args.lean_timeout_sec)
            except subprocess.TimeoutExpired:
                issues.append(f"{instance_id}: Lean smoke timed out after {args.lean_timeout_sec}s")
            else:
                if output is not None:
                    issues.append(f"{instance_id}: Lean smoke failed\n{output[-4000:]}")

    if issues:
        fail(issues)
    smoke_note = f"; Lean-smoked first {args.lean_smoke}" if args.lean_smoke else ""
    print(f"Checked {len(ids)} v2 batch task(s): {counts}{smoke_note}")


if __name__ == "__main__":
    main()
