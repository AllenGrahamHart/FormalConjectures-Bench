---
pretty_name: FormalConjectures-Bench Gold
language:
- code
tags:
- lean4
- theorem-proving
- formal-mathematics
- harbor
license: other
size_categories:
- n<1K
---

# FormalConjectures-Bench Gold

FormalConjectures-Bench Gold v1.1.0 is a set of 74 offline Lean 4
theorem-proving tasks with bundled oracle solutions. The executable benchmark is
distributed as a Harbor dataset; this Hugging Face dataset is the metadata and
discovery mirror.

The benchmark is intended for evaluation or RL. Benchmark target files and
oracle solutions should not be included in training corpora.

## Running

Install Harbor and run the registry-backed dataset:

```bash
uv tool install harbor

harbor run \
  --dataset formal-conjectures-gold@1.1.0 \
  --registry-url https://raw.githubusercontent.com/AllenGrahamHart/FormalConjectures-Bench/v1.1.0/registry.json \
  --agent terminus-2 \
  --model <provider/model>
```

Run a single task:

```bash
harbor run \
  --dataset formal-conjectures-gold@1.1.0 \
  --registry-url https://raw.githubusercontent.com/AllenGrahamHart/FormalConjectures-Bench/v1.1.0/registry.json \
  --task-name erdosproblems-399-erdos-399 \
  --agent terminus-2 \
  --model <provider/model>
```

The release defaults are intentionally generous: 24 hours for agent execution,
2 hours for verification, and 4 hours for environment builds. Use Harbor's
timeout multiplier to scale them:

```bash
harbor run \
  --dataset formal-conjectures-gold@1.1.0 \
  --registry-url https://raw.githubusercontent.com/AllenGrahamHart/FormalConjectures-Bench/v1.1.0/registry.json \
  --timeout-multiplier 0.25
```

## Files

- `tasks.jsonl` contains one metadata row per task.
- The executable task directories live in the GitHub repository.
- `registry.json` in the GitHub repository is the Harbor dataset registry.

## Versions

- Dataset: `formal-conjectures-gold@1.1.0`
- Task source commit:
  `a3674901510f2f8d8a8c1de0c28c568fcd48828e`
- Lean toolchain: `leanprover/lean4:v4.27.0`
- Mathlib commit: `a3a10db0e9d66acbebf76c5e6a135066525ac900`
- Formal Conjectures commit:
  `233a10e857ef78e79fd9fe661d37db724089170a`

## Licensing

The task statements derive from Google DeepMind's Formal Conjectures project.
Bundled oracle metadata is recorded per task in `tasks.jsonl`; the source
repository also includes `manifest/licence_review.csv`.
