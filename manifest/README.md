# Manifest

`manifest.json` is the source of truth for generated tasks. Raw extraction only
marks entries as `candidate`; a human or validation script must promote an entry
to `included` after licence review, oracle availability review, and oracle
canary verification.

For the v1.0.0 release, entries left as `candidate` are explicitly marked with
`v1_0_0_status = "deferred"` plus a short triage bucket and note. They remain
available for future repair work, but they are not emitted by the default task
generator and are not part of the v1.0.0 benchmark.

`pinned_versions.toml` records the upstream Formal Conjectures commit, Lean
toolchain, and Mathlib revision used for the extraction.
