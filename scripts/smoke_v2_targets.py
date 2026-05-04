#!/usr/bin/env python3
"""Lean-smoke generated v2 target statements with a reusable Lake project."""

from __future__ import annotations

import argparse
import json
import shutil
import subprocess
import sys
import tempfile
import time
from pathlib import Path

from check_v2_batch import load_ids, rewrite_dependency_paths


def batch_ids(batch_paths: list[Path]) -> list[tuple[Path, list[str]]]:
    result = []
    for path in batch_paths:
        result.append((path, load_ids(path)))
    return result


def build_project(project: Path, timeout: int) -> tuple[bool, str]:
    try:
        result = subprocess.run(
            ["lake", "build", "+FormalConjecturesBench.Target"],
            cwd=project,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            timeout=timeout,
        )
    except subprocess.TimeoutExpired as err:
        output = err.stdout or ""
        if isinstance(output, bytes):
            output = output.decode("utf-8", errors="replace")
        return False, f"timed out after {timeout}s\n{output}"

    return result.returncode == 0, result.stdout


def clear_target_artifacts(project: Path) -> None:
    build_dir = project / ".lake" / "build"
    if not build_dir.exists():
        return
    for path in build_dir.glob("**/FormalConjecturesBench/Target.*"):
        if path.is_file():
            path.unlink()


def prepare_project(first_task_dir: Path, formal_conjectures_source: Path) -> tempfile.TemporaryDirectory:
    temp_dir = tempfile.TemporaryDirectory(prefix="formal-conjectures-bench-v2-full-smoke-")
    project = Path(temp_dir.name)
    shutil.copytree(first_task_dir / "environment" / "data", project, dirs_exist_ok=True)
    shutil.rmtree(project / "checker", ignore_errors=True)
    rewrite_dependency_paths(project, formal_conjectures_source)
    return temp_dir


def smoke_target(task_dir: Path, project: Path, timeout: int) -> tuple[bool, str]:
    source = task_dir / "environment" / "data" / "FormalConjecturesBench" / "Target.lean"
    target = project / "FormalConjecturesBench" / "Target.lean"
    shutil.copyfile(source, target)
    clear_target_artifacts(project)
    return build_project(project, timeout)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--tasks-dir", type=Path, default=Path("tasks-v2"))
    parser.add_argument("--formal-conjectures-source", type=Path, default=Path(".cache/formal-conjectures"))
    parser.add_argument("--batch", type=Path, action="append", required=True)
    parser.add_argument("--lean-timeout-sec", type=int, default=600)
    parser.add_argument("--progress-every", type=int, default=1)
    parser.add_argument("--fail-fast", action="store_true")
    args = parser.parse_args()

    batches = batch_ids(args.batch)
    all_ids = [instance_id for _, ids in batches for instance_id in ids]
    if not all_ids:
        print("No task ids to smoke.", file=sys.stderr)
        sys.exit(2)

    first_task_dir = args.tasks_dir / all_ids[0]
    failures: list[tuple[str, str]] = []
    start = time.monotonic()
    completed = 0
    total = len(all_ids)

    with prepare_project(first_task_dir, args.formal_conjectures_source) as temp_dir:
        project = Path(temp_dir)
        for batch_path, ids in batches:
            batch_start = time.monotonic()
            print(f"== {batch_path.stem}: smoke {len(ids)} tasks ==", flush=True)
            for instance_id in ids:
                completed += 1
                task_start = time.monotonic()
                task_dir = args.tasks_dir / instance_id
                ok, output = smoke_target(task_dir, project, args.lean_timeout_sec)
                elapsed = time.monotonic() - task_start
                if ok:
                    if args.progress_every and (
                        completed == 1 or completed == total or completed % args.progress_every == 0
                    ):
                        print(f"[{completed}/{total}] ok {instance_id} ({elapsed:.1f}s)", flush=True)
                    continue

                failures.append((instance_id, output[-4000:]))
                print(f"[{completed}/{total}] FAIL {instance_id} ({elapsed:.1f}s)", flush=True)
                print(output[-4000:], flush=True)
                if args.fail_fast:
                    break
            batch_elapsed = time.monotonic() - batch_start
            print(f"== {batch_path.stem}: done in {batch_elapsed:.1f}s ==", flush=True)
            if failures and args.fail_fast:
                break

    elapsed_total = time.monotonic() - start
    if failures:
        print(f"Lean-smoked {completed}/{total} task(s) in {elapsed_total:.1f}s; failures: {len(failures)}")
        for instance_id, output in failures:
            print(f"\n--- {instance_id} ---\n{output}")
        sys.exit(1)

    print(f"Lean-smoked {completed}/{total} task(s) successfully in {elapsed_total:.1f}s")


if __name__ == "__main__":
    main()
