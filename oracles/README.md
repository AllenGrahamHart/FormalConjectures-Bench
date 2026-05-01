# Oracles

This directory is the source of truth for included oracle solutions. External
proof URLs in the manifest are provenance only; generated tasks and verifier
runs must use the local files copied here.

Place licence-reviewed canonical proof files here:

```text
oracles/<instance_id>/Target.lean
oracles/<instance_id>/Submission.lean
```

The generated `solution/solve.sh` copies bundled Lean files into the editable
task module. Do not add oracle files until the proof source licence and
redistribution status are recorded in `manifest/licence_review.csv`.

For every manifest entry marked `included`, `make check-oracles` verifies that:

- the oracle files are present and non-empty;
- `manifest/licence_review.csv` marks redistribution as `bundled`;
- generated `tasks/<instance_id>/solution/*.lean` matches `oracles/<instance_id>/*.lean`;
- generated `task.toml` records the pinned Lean/FormalConjectures/Mathlib
  versions; and
- generated task metadata keeps `allow_internet = false`.
