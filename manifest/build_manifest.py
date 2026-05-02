#!/usr/bin/env python3
"""Extract formally proved Formal Conjectures instances into a manifest.

The extractor is deliberately conservative. It records candidates and metadata;
it does not decide whether an instance is benchmark-ready. Promotion to
`included` happens only after licence and oracle canary review.
"""

from __future__ import annotations

import argparse
import datetime as dt
import json
import re
import subprocess
import tomllib
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable


FORMAL_PROOF_RE = re.compile(
    r"formal_proof\s+using\s+(lean4|formal_conjectures)\s+at\s+\"([^\"]*)\"",
    re.MULTILINE,
)
DECL_RE = re.compile(
    r"^\s*(?:(?:noncomputable|private|protected)\s+)*(theorem|lemma)\s+([^\s:{(\[]+)"
)
AMS_RE = re.compile(r"\bAMS\s+([0-9\s]+)")
CATEGORY_RE = re.compile(r"\bcategory\s+([^,\]]+)")


@dataclass(frozen=True)
class AttributeBlock:
    start_line: int
    end_line: int
    text: str


class CommentStripper:
    """Small Lean comment stripper for namespace tracking."""

    def __init__(self) -> None:
        self.depth = 0

    def strip_line(self, line: str) -> str:
        out: list[str] = []
        i = 0
        while i < len(line):
            if self.depth:
                if line.startswith("-/", i):
                    self.depth -= 1
                    i += 2
                else:
                    i += 1
                continue
            if line.startswith("/-", i):
                self.depth += 1
                i += 2
                continue
            if line.startswith("--", i):
                break
            out.append(line[i])
            i += 1
        return "".join(out)


def run_git(path: Path, *args: str) -> str:
    return subprocess.check_output(["git", "-C", str(path), *args], text=True).strip()


def read_text(path: Path) -> str:
    return path.read_text(encoding="utf-8")


def collect_attribute_blocks(lines: list[str]) -> Iterable[AttributeBlock]:
    i = 0
    while i < len(lines):
        if "@[" not in lines[i]:
            i += 1
            continue

        start = i
        text_parts = [lines[i]]
        balance = lines[i].count("[") - lines[i].count("]")
        i += 1
        while i < len(lines) and balance > 0:
            text_parts.append(lines[i])
            balance += lines[i].count("[") - lines[i].count("]")
            i += 1

        yield AttributeBlock(start_line=start + 1, end_line=i, text="\n".join(text_parts))


def find_declaration(lines: list[str], start_index: int) -> tuple[int, str, str] | None:
    for idx in range(start_index, min(len(lines), start_index + 25)):
        match = DECL_RE.match(lines[idx])
        if match:
            return idx + 1, match.group(1), match.group(2)
    return None


def namespace_stack_before(lines: list[str], one_based_line: int) -> list[str]:
    stripper = CommentStripper()
    namespaces: list[str] = []
    blocks: list[tuple[str, str | None]] = []

    for raw in lines[: max(0, one_based_line - 1)]:
        line = stripper.strip_line(raw).strip()
        if not line:
            continue

        match = re.match(r"^namespace\s+([A-Za-z0-9_'.]+)\b", line)
        if match:
            name = match.group(1)
            blocks.append(("namespace", name))
            namespaces.append(name)
            continue

        match = re.match(r"^(?:noncomputable\s+)?section(?:\s+([A-Za-z0-9_'.]+))?\b", line)
        if match:
            blocks.append(("section", match.group(1)))
            continue

        match = re.match(r"^end(?:\s+([A-Za-z0-9_'.]+))?\b", line)
        if match and blocks:
            kind, name = blocks.pop()
            if kind == "namespace" and namespaces:
                namespaces.pop()

    return namespaces


def declaration_body_col(line: str) -> int | None:
    by_match = re.search(r":=\s*by\b", line)
    if by_match:
        return by_match.start()

    for match in re.finditer(r":=", line):
        before = line[: match.start()]
        if re.search(r"\blet\s+[^:=]*\Z", before):
            continue
        return match.start()
    return None


def extract_header(lines: list[str], declaration_line: int) -> str:
    header_lines: list[str] = []
    for raw in lines[declaration_line - 1 :]:
        col = declaration_body_col(raw)
        if col is not None:
            header_lines.append(raw[:col].rstrip())
            break
        header_lines.append(raw.rstrip())
    return "\n".join(header_lines).strip()


def parse_ams(attr_text: str) -> list[str]:
    match = AMS_RE.search(attr_text)
    if not match:
        return []
    return [token for token in match.group(1).split() if token.isdigit()]


def parse_category(attr_text: str) -> list[str]:
    match = CATEGORY_RE.search(attr_text)
    if not match:
        return []
    raw = match.group(1)
    raw = re.split(r"\b(?:AMS|formal_proof)\b", raw, maxsplit=1)[0]
    return [token for token in raw.split() if token]


def classify_oracle(kind: str, url: str) -> str:
    if kind == "formal_conjectures":
        return "formal_conjectures"
    lowered = url.lower()
    if "plby/lean-proofs" in lowered:
        return "lean_proofs_repo"
    if "mathlib4" in lowered:
        return "mathlib"
    if "github.com" in lowered or "gist.github" in lowered:
        return "external_lean4"
    if not url:
        return "unavailable"
    return "external"


def slugify(value: str) -> str:
    value = value.lower()
    value = re.sub(r"[^a-z0-9]+", "-", value)
    value = re.sub(r"-+", "-", value).strip("-")
    return value or "instance"


def unique_instance_id(source_file: str, theorem_name: str, seen: dict[str, int]) -> str:
    path_part = source_file.removeprefix("FormalConjectures/").removesuffix(".lean")
    base = f"{slugify(path_part)}-{slugify(theorem_name.split('.')[-1])}"
    count = seen.get(base, 0) + 1
    seen[base] = count
    return base if count == 1 else f"{base}-{count}"


def mathlib_info(source: Path) -> tuple[str | None, str | None]:
    input_rev: str | None = None
    commit: str | None = None

    lakefile = source / "lakefile.toml"
    if lakefile.exists():
        data = tomllib.loads(read_text(lakefile))
        for req in data.get("require", []):
            if req.get("name") == "mathlib":
                input_rev = req.get("rev")
                break

    manifest = source / "lake-manifest.json"
    if manifest.exists():
        data = json.loads(read_text(manifest))
        for package in data.get("packages", []):
            if package.get("name") == "mathlib":
                commit = package.get("rev")
                input_rev = input_rev or package.get("inputRev")
                break

    return input_rev, commit


def extract_instances(source: Path) -> tuple[list[dict], dict]:
    source = source.resolve()
    root = source / "FormalConjectures"
    seen: dict[str, int] = {}
    instances: list[dict] = []

    for file_path in sorted(root.rglob("*.lean")):
        rel = file_path.relative_to(source).as_posix()
        lines = read_text(file_path).splitlines()
        for block in collect_attribute_blocks(lines):
            formal_proofs = [
                {"kind": match.group(1), "url": match.group(2)}
                for match in FORMAL_PROOF_RE.finditer(block.text)
                if match.group(1) in {"lean4", "formal_conjectures"}
            ]
            if not formal_proofs:
                continue

            declaration = find_declaration(lines, block.end_line)
            if declaration is None:
                continue
            declaration_line, declaration_kind, local_name = declaration
            namespaces = namespace_stack_before(lines, declaration_line)
            full_name = ".".join([*namespaces, local_name]) if namespaces else local_name
            header = extract_header(lines, declaration_line)
            selected = next(
                (p for p in formal_proofs if p["kind"] == "formal_conjectures" and p["url"]),
                None,
            )
            selected = selected or next((p for p in formal_proofs if p["kind"] == "lean4" and p["url"]), None)
            selected = selected or next((p for p in formal_proofs if p["url"]), None)
            selected = selected or formal_proofs[0]
            contains_answer_elaborator = "answer(" in header
            uses_answer_sorry = "answer(sorry)" in header.replace(" ", "")
            if uses_answer_sorry:
                inclusion_status = "excluded"
                exclusion_reason = "theorem statement contains answer(sorry)"
            elif not selected["url"]:
                inclusion_status = "excluded"
                exclusion_reason = "selected formal_proof URL is empty"
            else:
                inclusion_status = "candidate"
                exclusion_reason = None

            instance_id = unique_instance_id(rel, full_name, seen)
            instances.append(
                {
                    "instance_id": instance_id,
                    "theorem_name": full_name,
                    "local_declaration_name": local_name,
                    "declaration_kind": declaration_kind,
                    "source_file": rel,
                    "attribute_line": block.start_line,
                    "declaration_line": declaration_line,
                    "namespace": namespaces,
                    "theorem_header": header,
                    "formal_proofs": formal_proofs,
                    "selected_oracle": {
                        "kind": classify_oracle(selected["kind"], selected["url"]),
                        "formal_proof_kind": selected["kind"],
                        "url": selected["url"],
                        "licence_status": "unreviewed",
                        "redistribution_status": "unreviewed",
                    },
                    "category": parse_category(block.text),
                    "ams_tags": parse_ams(block.text),
                    "contains_answer_elaborator": contains_answer_elaborator,
                    "uses_answer_sorry": uses_answer_sorry,
                    "inclusion_status": inclusion_status,
                    "exclusion_reason": exclusion_reason,
                }
            )

    lean_toolchain = read_text(source / "lean-toolchain").strip() if (source / "lean-toolchain").exists() else None
    mathlib_input_rev, mathlib_commit = mathlib_info(source)
    metadata = {
        "formal_conjectures_commit": run_git(source, "rev-parse", "HEAD"),
        "formal_conjectures_remote": run_git(source, "config", "--get", "remote.origin.url"),
        "lean_toolchain": lean_toolchain,
        "mathlib_input_rev": mathlib_input_rev,
        "mathlib_commit": mathlib_commit,
        "generated_at": dt.datetime.now(dt.UTC).replace(microsecond=0).isoformat(),
        "candidate_count": len(instances),
        "excluded_count": sum(1 for item in instances if item["inclusion_status"] == "excluded"),
    }
    return instances, metadata


def write_pinned_versions(path: Path, metadata: dict) -> None:
    lines = [
        "# Generated by manifest/build_manifest.py",
        f'formal_conjectures_commit = "{metadata.get("formal_conjectures_commit", "")}"',
        f'formal_conjectures_remote = "{metadata.get("formal_conjectures_remote", "")}"',
        f'lean_toolchain = "{metadata.get("lean_toolchain", "")}"',
        f'mathlib_input_rev = "{metadata.get("mathlib_input_rev", "")}"',
        f'mathlib_commit = "{metadata.get("mathlib_commit", "")}"',
        f'generated_at = "{metadata.get("generated_at", "")}"',
        f'candidate_count = {metadata.get("candidate_count", 0)}',
        f'excluded_count = {metadata.get("excluded_count", 0)}',
        "",
    ]
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("\n".join(lines), encoding="utf-8")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--source", required=True, type=Path, help="Formal Conjectures checkout")
    parser.add_argument("--out", default=Path("manifest/manifest.json"), type=Path)
    parser.add_argument("--pinned-out", default=Path("manifest/pinned_versions.toml"), type=Path)
    args = parser.parse_args()

    instances, metadata = extract_instances(args.source)
    manifest = {
        "schema_version": 1,
        "source": metadata,
        "instances": instances,
    }

    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    write_pinned_versions(args.pinned_out, metadata)
    print(f"Wrote {len(instances)} candidate instances to {args.out}")


if __name__ == "__main__":
    main()
