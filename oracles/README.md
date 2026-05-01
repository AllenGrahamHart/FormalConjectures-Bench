# Oracles

Place licence-reviewed canonical proof files here:

```text
oracles/<instance_id>/Oracle.lean
```

The generated `solution/solve.sh` copies that file over the public target file
and runs `lake build`. Do not add oracle files until the proof source licence
and redistribution status are recorded in `manifest/licence_review.csv`.
