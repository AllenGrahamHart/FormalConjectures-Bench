# Manifest

`manifest.json` is the source of truth for generated tasks. Raw extraction only
marks entries as `candidate`; a human or validation script must promote an entry
to `included` after licence review, oracle availability review, and oracle
canary verification.

`pinned_versions.toml` records the upstream Formal Conjectures commit, Lean
toolchain, and Mathlib revision used for the extraction.
