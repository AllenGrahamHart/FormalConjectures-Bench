# Upstream Feedback Notes

Date: 2026-05-02

These notes track candidate issues to report upstream to Google DeepMind's
Formal Conjectures project after the v1 benchmark inclusion list stabilizes.
They are not yet an issue draft; they are working notes gathered while trying
to build verifier-clean oracle tasks.

The goal is to distinguish:

- Formal Conjectures statements that appear to have the wrong answer or target.
- Manifest/proof metadata that points to a non-implying proof source.
- Tasks where a proof source is real but an additional substantial bridge is
  needed before it proves the generated target.

## Current Candidates

| Instance | Category | Current assessment | Evidence / needed fix |
| --- | --- | --- | --- |
| `erdosproblems-678-erdos-678` | Possible wrong answer or target polarity | Fatal for the generated target as currently stated. | The selected source contains `not_erdos_678_fc`, proving the negation of the generated eventual-infinitude proposition using only standard Lean axioms. The positive triple-infinitude theorem in that source depends on an extra `pi_alt` PNT axiom and is not the generated target. |
| `erdosproblems-1071-i` | Wrong or non-implying proof source | Fatal for this selected proof source; not necessarily false mathematics. | The selected source proves a countably infinite set-based maximal collection of open unit segments. The generated target asks for a finite `Finset` maximal family of unit segments in the unit square. A different source proving the finite Danzer construction would be needed. |
| `oeis-6697-conjecture` | Missing substantial bridge theorem | Not verifier-ready; existing proof proves a nearby theorem. | The selected proof proves the generating function for a formula-defined sequence `a(n) = sum_i min(2^i, n-i+1)`. The generated target defines `a n` as the cardinality of actual subwords of the morphism fixed point. The missing bridge is the Allouche-Shallit subword-complexity formula. |
| `erdosproblems-1067-erdos-1067` | Substantial statement-alignment bridge | Probably salvageable, but not a minor metadata fix. | The source proof ports to Lean 4.27 after a one-line cardinal API repair, but it proves a custom induced-subgraph formulation using `uncountably_chromatic` and `finite_independent_paths`. The generated target uses `chromaticCardinal = aleph 1`, arbitrary subgraphs, and `InfinitelyConnected`. |

## Issue-Draft Shape

When the final benchmark list is known, a useful upstream issue should include:

- The exact Formal Conjectures commit and theorem names.
- A short table of affected declarations.
- For each case, whether the issue is statement polarity, proof metadata, or a
  missing theorem bridge.
- The verifier-clean evidence we have, such as a source theorem proving the
  negation or a successful port of the proof source to the pinned Lean version.
- A clear statement that these were found while building a benchmark and that
  exclusion from the benchmark does not by itself imply the mathematical claim is
  false.

## Open Questions

- Should `erdosproblems-678-erdos-678` be corrected by changing the answer,
  changing the theorem statement, or adding a different theorem for the
  triple-infinitude result?
- Does a formal proof of the finite Danzer construction exist for
  `erdosproblems-1071-i`, separate from the countably infinite construction?
- Is the Allouche-Shallit subword-complexity formula for `oeis-6697-conjecture`
  formalized anywhere, or should that target remain excluded?
- For `erdosproblems-1067-erdos-1067`, is the intended upstream target the
  `chromaticCardinal` statement or the custom induced-subgraph statement from
  the selected source?
