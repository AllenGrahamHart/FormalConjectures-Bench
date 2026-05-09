#!/usr/bin/env python3
"""Generate public release artifacts for FormalConjectures-Bench gold."""

from __future__ import annotations

import argparse
import csv
import json
import tomllib
from pathlib import Path


def read_json(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def read_toml(path: Path) -> dict:
    return tomllib.loads(path.read_text(encoding="utf-8"))


def licence_rows(path: Path) -> dict[str, dict[str, str]]:
    with path.open(newline="", encoding="utf-8") as handle:
        return {row["instance_id"]: row for row in csv.DictReader(handle)}


def included_instances(manifest_path: Path) -> dict[str, dict]:
    manifest = read_json(manifest_path)
    return {
        instance["instance_id"]: instance
        for instance in manifest.get("instances", [])
        if instance.get("inclusion_status") == "included"
    }


def task_ids(tasks_dir: Path) -> list[str]:
    ids = []
    for path in sorted(tasks_dir.iterdir()):
        if not path.is_dir():
            continue
        if not (path / "task.toml").is_file():
            continue
        ids.append(path.name)
    return ids


def build_registry(
    *,
    dataset_name: str,
    version: str,
    description: str,
    git_url: str,
    git_commit_id: str,
    tasks_dir: Path,
    ids: list[str],
) -> list[dict]:
    return [
        {
            "name": dataset_name,
            "version": version,
            "description": description,
            "tasks": [
                {
                    "name": task_id,
                    "git_url": git_url,
                    "git_commit_id": git_commit_id,
                    "path": str(tasks_dir / task_id),
                }
                for task_id in ids
            ],
        }
    ]


def build_hf_rows(
    *,
    ids: list[str],
    tasks_dir: Path,
    instances: dict[str, dict],
    reviews: dict[str, dict[str, str]],
) -> list[dict]:
    rows = []
    for task_id in ids:
        task_dir = tasks_dir / task_id
        task_toml = read_toml(task_dir / "task.toml")
        metadata = task_toml["metadata"]
        environment = task_toml["environment"]
        instance = instances.get(task_id, {})
        review = reviews.get(task_id, {})
        rows.append(
            {
                "task_id": task_id,
                "harbor_task_name": task_toml["task"]["name"],
                "harbor_task_path": str(task_dir),
                "theorem_name": metadata["theorem_name"],
                "theorem_header": instance.get("theorem_header"),
                "source": metadata["source"],
                "source_file": metadata["source_file"],
                "benchmark_bucket": metadata["benchmark_bucket"],
                "oracle_status": metadata["oracle_status"],
                "licence_status": review.get("licence_status"),
                "redistribution_status": review.get("redistribution_status"),
                "formal_conjectures_commit": metadata["formal_conjectures_commit"],
                "lean_toolchain": metadata["lean_toolchain"],
                "mathlib_commit": metadata["mathlib_commit"],
                "allow_internet": environment["allow_internet"],
                "agent_timeout_sec": task_toml["agent"]["timeout_sec"],
                "verifier_timeout_sec": task_toml["verifier"]["timeout_sec"],
                "environment_build_timeout_sec": environment["build_timeout_sec"],
            }
        )
    return rows


def write_json(path: Path, payload: object) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")


def write_jsonl(path: Path, rows: list[dict]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", encoding="utf-8") as handle:
        for row in rows:
            handle.write(json.dumps(row, ensure_ascii=False) + "\n")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--tasks-dir", type=Path, default=Path("tasks"))
    parser.add_argument("--manifest", type=Path, default=Path("manifest/manifest.json"))
    parser.add_argument(
        "--licence-review",
        type=Path,
        default=Path("manifest/licence_review.csv"),
    )
    parser.add_argument("--registry-out", type=Path, default=Path("registry.json"))
    parser.add_argument(
        "--hf-tasks-out",
        type=Path,
        default=Path("huggingface/formal-conjectures-gold/tasks.jsonl"),
    )
    parser.add_argument("--dataset-name", default="formal-conjectures-gold")
    parser.add_argument("--version", default="1.3.0")
    parser.add_argument(
        "--description",
        default=(
            "76 offline Lean 4 theorem-proving tasks from FormalConjectures-Bench "
            "with bundled oracle solutions."
        ),
    )
    parser.add_argument(
        "--git-url",
        default="https://github.com/AllenGrahamHart/FormalConjectures-Bench",
    )
    parser.add_argument("--git-commit-id", required=True)
    args = parser.parse_args()

    ids = task_ids(args.tasks_dir)
    instances = included_instances(args.manifest)
    reviews = licence_rows(args.licence_review)

    missing_manifest = sorted(set(ids) - set(instances))
    if missing_manifest:
        raise SystemExit(f"Task ids missing from manifest: {missing_manifest}")

    missing_reviews = sorted(set(ids) - set(reviews))
    if missing_reviews:
        raise SystemExit(f"Task ids missing from licence review: {missing_reviews}")

    registry = build_registry(
        dataset_name=args.dataset_name,
        version=args.version,
        description=args.description,
        git_url=args.git_url,
        git_commit_id=args.git_commit_id,
        tasks_dir=args.tasks_dir,
        ids=ids,
    )
    rows = build_hf_rows(
        ids=ids,
        tasks_dir=args.tasks_dir,
        instances=instances,
        reviews=reviews,
    )

    write_json(args.registry_out, registry)
    write_jsonl(args.hf_tasks_out, rows)
    print(f"Wrote {args.registry_out} with {len(ids)} task(s)")
    print(f"Wrote {args.hf_tasks_out} with {len(rows)} row(s)")


if __name__ == "__main__":
    main()
