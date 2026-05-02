# Benchmark Card

Version: `1.0.0`

Release date: 2026-05-02

## Summary

FormalConjectures-Bench v1.0.0 contains 71 Harbor tasks generated from the
formally proved subset of Google DeepMind's Formal Conjectures project. The
release boundary is conservative: every included task has committed local Lean
oracle files and passes the repository's generated-artifact and oracle-presence
checks.

## Scope

| Field | Value |
| --- | --- |
| Included tasks | 71 |
| Reviewed generated candidates | 101 |
| Deferred generated candidates | 30 |
| Upstream extraction exclusions | 5 |
| Runtime internet | Disabled |
| Oracle artifacts | Bundled under `oracles/<instance_id>/` |
| Generated task artifacts | Committed under `tasks/<instance_id>/` |

## Pinning

| Component | Pin |
| --- | --- |
| Lean | `leanprover/lean4:v4.27.0` |
| Mathlib input | `v4.27.0` |
| Mathlib commit | `a3a10db0e9d66acbebf76c5e6a135066525ac900` |
| Formal Conjectures commit | `233a10e857ef78e79fd9fe661d37db724089170a` |
| Base image tag | `formal-conjectures-bench-base:v4.27.0-fc233a10e` |

## Included Areas

| Source area | Tasks |
| --- | ---: |
| `ErdosProblems` | 46 |
| `Paper` | 11 |
| `Wikipedia` | 6 |
| `GreensOpenProblems` | 4 |
| `Mathoverflow` | 2 |
| `OpenQuantumProblems` | 2 |

## Verifier

The generated verifier rebuilds the submitted theorem in a hidden golden Lean
project. It locks the target theorem header and frozen prefix, rejects common
escape hatches and parser/metaprogramming extensions, audits `#print axioms`,
and runs a local canary to ensure `sorryAx` would be detected.

## Deferred Candidates

The remaining 30 generated candidates are marked in `manifest/manifest.json`
with `v1_0_0_status = "deferred"`. Their issue categories are tracked in
`docs/remaining-failures-matrix.md`; they are not part of v1.0.0 because they
require substantial proof repair, statement bridging, dependency decisions, or
replacement proof sources.

## Known Reproducibility Limitation

The Lean statements, generated task files, and oracle files are committed
locally. Fresh image builds still depend on live infrastructure such as apt,
GitHub, elan, and the Lake cache. The archival hardening plan is tracked in
`docs/reproducibility.md`.
