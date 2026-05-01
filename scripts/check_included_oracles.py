#!/usr/bin/env python3
"""Check that included tasks have local, pinned oracle artifacts."""

from __future__ import annotations

import argparse
import csv
import json
import sys
import tomllib
from pathlib import Path


REQUIRED_ORACLE_FILES = ("Target.lean", "Submission.lean")
REQUIRED_METADATA_KEYS = (
    "formal_conjectures_commit",
    "lean_toolchain",
    "mathlib_commit",
)


def read_toml(path: Path) -> dict:
    return tomllib.loads(path.read_text(encoding="utf-8"))


def fail(issues: list[str]) -> None:
    print("Included-oracle check failed:", file=sys.stderr)
    for issue in issues:
        print(f"- {issue}", file=sys.stderr)
    sys.exit(1)


def regular_file(path: Path, issues: list[str], description: str) -> bool:
    if not path.exists():
        issues.append(f"Missing {description}: {path}")
        return False
    if path.is_symlink() or not path.is_file():
        issues.append(f"{description} must be a regular file: {path}")
        return False
    if path.stat().st_size == 0:
        issues.append(f"{description} is empty: {path}")
        return False
    return True


def included_instances(manifest_path: Path) -> list[dict]:
    manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    return [
        instance
        for instance in manifest.get("instances", [])
        if instance.get("inclusion_status") == "included"
    ]


def licence_rows(path: Path) -> dict[str, dict[str, str]]:
    with path.open(newline="", encoding="utf-8") as handle:
        return {row["instance_id"]: row for row in csv.DictReader(handle)}


def lean_files(root: Path) -> dict[str, Path]:
    if not root.exists():
        return {}
    return {path.name: path for path in sorted(root.glob("*.lean")) if path.is_file()}


def check_task(
    instance: dict,
    *,
    oracles_dir: Path,
    tasks_dir: Path,
    pinned: dict,
    reviews: dict[str, dict[str, str]],
    issues: list[str],
) -> None:
    instance_id = instance["instance_id"]
    oracle_dir = oracles_dir / instance_id
    task_dir = tasks_dir / instance_id
    solution_dir = task_dir / "solution"

    review = reviews.get(instance_id)
    if review is None:
        issues.append(f"{instance_id}: missing licence review row")
    else:
        if review.get("redistribution_status") != "bundled":
            issues.append(f"{instance_id}: licence review is not marked bundled")
        if review.get("licence_status", "").lower() in {"", "unreviewed"}:
            issues.append(f"{instance_id}: licence status is not reviewed")

    for filename in REQUIRED_ORACLE_FILES:
        regular_file(oracle_dir / filename, issues, f"{instance_id} oracle {filename}")

    task_toml = task_dir / "task.toml"
    if regular_file(task_toml, issues, f"{instance_id} task.toml"):
        data = read_toml(task_toml)
        metadata = data.get("metadata", {})
        environment = data.get("environment", {})
        if metadata.get("oracle_status") != "bundled":
            issues.append(f"{instance_id}: task metadata oracle_status is not bundled")
        if environment.get("allow_internet") is not False:
            issues.append(f"{instance_id}: task environment allow_internet must be false")
        for key in REQUIRED_METADATA_KEYS:
            if metadata.get(key) != pinned.get(key):
                issues.append(
                    f"{instance_id}: task metadata {key}={metadata.get(key)!r} "
                    f"does not match pinned {pinned.get(key)!r}"
                )

    oracle_files = lean_files(oracle_dir)
    solution_files = lean_files(solution_dir)
    if set(oracle_files) != set(solution_files):
        issues.append(
            f"{instance_id}: solution Lean files {sorted(solution_files)} "
            f"do not match oracle files {sorted(oracle_files)}"
        )
        return

    for name, oracle_path in oracle_files.items():
        solution_path = solution_files[name]
        if oracle_path.read_bytes() != solution_path.read_bytes():
            issues.append(f"{instance_id}: solution/{name} differs from oracles/{instance_id}/{name}")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--manifest", type=Path, default=Path("manifest/manifest.json"))
    parser.add_argument("--pinned", type=Path, default=Path("manifest/pinned_versions.toml"))
    parser.add_argument("--licence-review", type=Path, default=Path("manifest/licence_review.csv"))
    parser.add_argument("--oracles-dir", type=Path, default=Path("oracles"))
    parser.add_argument("--tasks-dir", type=Path, default=Path("tasks"))
    args = parser.parse_args()

    pinned = read_toml(args.pinned)
    reviews = licence_rows(args.licence_review)
    instances = included_instances(args.manifest)

    seen: set[str] = set()
    issues: list[str] = []
    for instance in instances:
        instance_id = instance["instance_id"]
        if instance_id in seen:
            issues.append(f"Duplicate included instance id: {instance_id}")
            continue
        seen.add(instance_id)
        check_task(
            instance,
            oracles_dir=args.oracles_dir,
            tasks_dir=args.tasks_dir,
            pinned=pinned,
            reviews=reviews,
            issues=issues,
        )

    if issues:
        fail(issues)

    print(f"Checked {len(instances)} included task(s); bundled oracle artifacts are present.")


if __name__ == "__main__":
    main()
