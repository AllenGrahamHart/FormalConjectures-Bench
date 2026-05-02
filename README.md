# FormalConjectures-Bench

FormalConjectures-Bench is a Harbor benchmark of Lean 4 theorem-proving tasks
derived from the formally proved subset of Google DeepMind's Formal
Conjectures project.

Version `1.0.0` freezes a conservative set of 71 tasks. Each included task has
a static Harbor task directory under `tasks/`, a bundled local oracle under
`oracles/`, and a generated verifier that checks the submitted Lean proof in a
hidden golden project.

This repository is Harbor-native. It is not a Terminal-Bench 3.0 fork, although
the verifier design borrows hardening lessons from Terminal-Bench task review.

## Benchmark Card

| Field | Value |
| --- | --- |
| Version | `1.0.0` |
| Release date | 2026-05-02 |
| Included tasks | 71 |
| Reviewed candidate pool | 101 generated candidates; 30 deferred for later repair |
| Upstream extraction exclusions | 5 entries excluded before task generation |
| Language | Lean 4 |
| Lean toolchain | `leanprover/lean4:v4.27.0` |
| Mathlib | `v4.27.0`, commit `a3a10db0e9d66acbebf76c5e6a135066525ac900` |
| Formal Conjectures commit | `233a10e857ef78e79fd9fe661d37db724089170a` |
| Runtime internet | Disabled in generated task metadata |
| Oracle policy | Included tasks use committed local oracle files; proof URLs are provenance only |
| Verifier policy | Hidden golden project, theorem-header lock, banned escape hatches, axiom audit, and `sorry` canary |

Included tasks cover:

| Source area | Tasks |
| --- | ---: |
| `ErdosProblems` | 46 |
| `Paper` | 11 |
| `Wikipedia` | 6 |
| `GreensOpenProblems` | 4 |
| `Mathoverflow` | 2 |
| `OpenQuantumProblems` | 2 |

See [docs/benchmark-card.md](docs/benchmark-card.md) for the same release card
with notes on the v1 boundary.

## Repository Layout

- `manifest/manifest.json` is the source of truth for task inclusion.
- `oracles/<instance_id>/` stores bundled canonical Lean oracle files for
  included tasks.
- `generators/generate_tasks.py` renders Harbor task directories from the
  manifest, templates, and oracle files.
- `tasks/<instance_id>/` contains generated Harbor tasks. Treat these as build
  artifacts and do not hand-edit them.
- `docs/remaining-failures-matrix.md` records why the remaining 30 generated
  candidates are deferred from v1.0.0.
- `docs/reproducibility.md` records the current reproducibility invariants and
  remaining archival-hardening work.

## Checking The Release

The lightweight release checks are:

```bash
make check
```

This validates that:

- `manifest/manifest.json` is valid JSON;
- every included task has bundled local oracle files;
- bundled oracle metadata records redistribution as local/bundled;
- generated `solution/` files match `oracles/`;
- generated task metadata records the pinned Lean/FormalConjectures/Mathlib
  versions; and
- checked-in included tasks match the generator output.

For the individual checks:

```bash
make check-oracles
make check-generated
```

## Regenerating Tasks

Clone the pinned Formal Conjectures dependency if it is not already present:

```bash
mkdir -p .cache
git clone https://github.com/google-deepmind/formal-conjectures.git .cache/formal-conjectures
git -C .cache/formal-conjectures checkout 233a10e857ef78e79fd9fe661d37db724089170a
```

Then regenerate the included task set:

```bash
make generate
```

For exploratory work on a deferred candidate, pass
`--include-candidates --only <instance_id>` through the pilot Make targets:

```bash
make generate-pilot ONLY=<instance_id>
make check-pilot-generated ONLY=<instance_id>
```

Pilot-generated candidate artifacts are not part of the v1.0.0 release unless
the manifest entry is promoted to `included` and bundled oracle files are added.

## Running With Harbor

Harbor can consume the checked-in task directory as a local dataset path:

```bash
harbor run -p tasks
```

Use Harbor's usual agent/model flags to choose the solver. On a clean checkout
of tag `v1.0.0`, `tasks/` contains only the 71 included release tasks.

## Verification Model

Each generated task verifier checks that:

- the frozen prefix and theorem header are unchanged;
- the submitted proof is rebuilt in a fresh hidden golden project;
- the editable Lean subtree does not contain banned escape hatches;
- `lake build` succeeds in the pinned Lean environment;
- `#print axioms` for the target theorem contains only allowed axioms; and
- a local `sorry` canary is detected by the axiom-audit path.

Generated tasks set `allow_internet = false`. Docker image builds may fetch
pinned dependencies, but the agent and verifier run offline.

## Release Boundary

The v1.0.0 line is intentionally conservative. The 30 deferred candidates are
documented in [docs/remaining-failures-matrix.md](docs/remaining-failures-matrix.md)
and marked in the manifest with `v1_0_0_status = "deferred"`. They are left as
future work because they require statement bridges, substantial Lean porting,
dependency decisions, axiom elimination, or replacement proof sources.

See [docs/reproducibility.md](docs/reproducibility.md) for the archival
hardening plan that should be completed before a paper-grade immutable release.
