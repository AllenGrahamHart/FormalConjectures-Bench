# FormalConjectures-Bench

FormalConjectures-Bench is a Harbor dataset for Lean 4 theorem-proving tasks
derived from the formally proved subset of Google DeepMind's Formal
Conjectures project.

The benchmark is intentionally Harbor-native: each conjecture becomes a static
Harbor task generated from `manifest/manifest.json`, and the dataset is defined
by `dataset.toml`. We do not fork Terminal-Bench 3.0; we borrow its review
discipline where useful.

## Current State

This repository contains the benchmark scaffolding:

- `manifest/build_manifest.py` extracts candidate formally proved conjectures.
- `generators/generate_tasks.py` turns reviewed manifest entries into Harbor
  task directories.
- `oracles/` is reserved for licence-reviewed canonical proofs.
- `tasks/` is generated output and should not be hand-edited.

The v1 release policy is conservative: include only instances whose oracle is
fetchable, licence-compatible, offline-buildable, and verifier-clean.

The generated verifier is modelled on the hardened Takens task in the local TB3
worktree: it rebuilds a hidden golden project and overlays only the editable
Lean subtree before checking axioms.

## Workflow

Clone Formal Conjectures at the commit you want to benchmark:

```bash
mkdir -p .cache
git clone https://github.com/google-deepmind/formal-conjectures.git .cache/formal-conjectures
```

Build the candidate manifest:

```bash
python3 manifest/build_manifest.py \
  --source .cache/formal-conjectures \
  --out manifest/manifest.json \
  --pinned-out manifest/pinned_versions.toml
```

Build the shared Lean base image once:

```bash
make base-image
```

Generated tasks inherit from `formal-conjectures-bench-base:v4.27.0-fc233a10e`.
The image itself is not stored in git; only its Dockerfile is committed.

After licence and oracle review, mark selected entries as `included` in the
manifest and place their canonical proof files under `oracles/<instance_id>/`.
Then generate tasks:

```bash
make generate
```

For pilot work before review, pass `--include-candidates --only <instance_id>`.
Those generated tasks are for harness development only; the bundled oracle run
will only work after proof files have been added under `oracles/<instance_id>/`.

Generated task directories are checked in so Harbor can consume the dataset as
static tasks, but they should be treated as build artifacts. To verify that
`tasks/` still matches `manifest/`, `generators/templates/`, and `oracles/`,
run:

```bash
make check-generated
```

For a pilot candidate, use:

```bash
make check-pilot-generated ONLY=<instance_id>
```

The repository currently includes two generated tasks with bundled oracle
solutions: `tasks/erdosproblems-370-erdos-370` as the initial verifier pilot,
and `tasks/erdosproblems-741-i` as a harder proof-ability probe. They are useful
for reviewing task shape, verifier structure, and model behavior before scaling
to the rest of the reviewed manifest.

## Verification Model

Each task verifier checks that:

- the frozen prefix and theorem header are unchanged;
- the submitted proof is rebuilt in a fresh hidden golden project;
- the editable proof body does not contain banned escape hatches;
- `lake build` succeeds in the pinned Lean environment;
- `#print axioms` for the target theorem contains only allowed axioms;
- a local `sorry` canary is detected by the axiom-audit path.

Trial-time internet access is disabled for generated tasks. Docker image builds
may fetch pinned dependencies, but the agent and verifier run offline.
