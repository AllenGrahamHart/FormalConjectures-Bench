# Erdős Problem 330 Formalization

This directory is for the proof-faithful Lean development of Erdős Problem 330.
It intentionally starts from the upper-density exact two-fold formulation in
`erdos330_formalisation_brief_v2.md`, rather than treating the existing
Formal Conjectures `answer(sorry)` statement as canonical.

The intended first target is:

```lean
∃ A : Set ℕ,
  IsAsymptoticBasisTwo A ∧
  0 < A.upperDensity ∧
  ∀ a ∈ A, 0 < (privateSet A a).upperDensity
```

Once this theorem is formalized, it can be promoted into a golden Harbor task
with the theorem statement and oracle proof generated from this development.
