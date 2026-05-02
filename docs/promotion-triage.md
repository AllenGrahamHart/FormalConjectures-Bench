# Promotion Triage

Date: 2026-05-02

This is the v1.0.0 technical-readiness triage for the 101 generated candidate
tasks. License and redistribution review are a separate promotion gate.

## Summary

- Technically ready now: 71
- Promoted now: 71
- Promoted with no-explicit-license provenance note: 13
- Ready after a small generator change: 0
- Needs substantial changes before promotion: 30
- Total: 101

The v1.0.0 release boundary is frozen at the 71 promoted tasks. The remaining
30 generated candidates are marked as deferred in `manifest/manifest.json` and
tracked in `docs/remaining-failures-matrix.md`.

Evidence used:

- Parsed all Harbor `result.json` files and matched task ids from reward trial
  ids as well as job paths.
- Fixed theorem-header extraction for internal top-level `let ... := ...` and
  `letI ... := by ...` binders in theorem result types.
- Ran repository checks for the promoted set and targeted generator checks for
  the repaired first-tier candidates.
- Ran Modal oracle validation for `greensopenproblems-57-z3-functional` and
  `erdosproblems-331-erdos-331`; both passed with reward `1.0` and zero errors.
- Ran local oracle validation for `erdosproblems-355-erdos-355`; it passed with
  reward `1.0` and zero errors after narrowing the oracle to Theorem 1 and its
  dependencies.
- Ran local oracle validation for `erdosproblems-1051-erdos-1051`; it passed
  with reward `1.0` and zero errors after adding a bridge from the Nat-valued
  proof to the integer-valued benchmark target.
- Ran local Harbor oracle validation for `erdosproblems-26-erdos-26`; it passed
  with reward `1.0` and zero errors after reusing the Apache-2.0 Tenenbaum
  counterexample and adding the bridge from natural density `1` to lower
  density `1`.
- Ran local verifier validation for `erdosproblems-229-erdos-229`; it passed
  after porting the Lean 4.24 `plby/lean-proofs` source to the pinned Lean
  4.27.0/mathlib environment.
- Ran first-pass local compiles for the six remaining Lean API/proof-port
  candidates; all six need substantial repair, so there are no additional quick
  v1 promotions in that bucket after `erdosproblems-229-erdos-229`.
- Reran `arxiv-0911-2077-conjecture6-3-conjecture6-3` after the header fix; it
  still fails because the bundled oracle was generated for the old truncated
  target and only proves the internal `letI` witness.

## Promoted Now

These tasks have a clean oracle result with reward `1.0`, zero errors,
are reproducible from the current generator, and are now marked `included` in
`manifest/manifest.json`.

- `erdosproblems-100-erdos-100-piepmeyer`
- `erdosproblems-1043-erdos-1043`
- `erdosproblems-1052-even-of-isunitaryperfect`
- `erdosproblems-1074-ehsnumbers-infinite`
- `erdosproblems-1082-ii`
- `erdosproblems-12-i`
- `erdosproblems-12-ii`
- `erdosproblems-12-isgood-example`
- `erdosproblems-125-erdos-125`
- `erdosproblems-125-positive-lower-density`
- `erdosproblems-138-difference`
- `erdosproblems-138-monoapnumber-two-one`
- `erdosproblems-138-monoapnumber-two-two`
- `erdosproblems-152-erdos-152`
- `erdosproblems-152-square`
- `erdosproblems-198-concrete`
- `erdosproblems-198-erdos-198`
- `erdosproblems-233-lower-bound`
- `erdosproblems-26-erdos-26`
- `erdosproblems-26-tenenbaum`
- `erdosproblems-263-ii`
- `erdosproblems-267-specialization-pow-two`
- `erdosproblems-316-erdos-316`
- `erdosproblems-350-erdos-350`
- `erdosproblems-370-erdos-370`
- `erdosproblems-379-erdos-379`
- `erdosproblems-397-erdos-397`
- `erdosproblems-399-erdos-399`
- `erdosproblems-741-i`
- `erdosproblems-741-ii`
- `erdosproblems-741-upper`
- `erdosproblems-828-phi-dvd-self-iff-pow2-pow3`
- `erdosproblems-846-erdos-846`
- `erdosproblems-978-allow-fixed-divisors`
- `greensopenproblems-57-green-57`
- `greensopenproblems-57-z3`
- `greensopenproblems-57-z3-functional`
- `greensopenproblems-94-green-94-outer-measure`
- `mathoverflow-10799-mathoverflow-10799`
- `mathoverflow-486451-exists-semiring-unique-left-right-maximal-ne`
- `openquantumproblems-13-mutuallyunbiasedbases-dim6-bounds`
- `openquantumproblems-35-ame-11-5-open`
- `paper-casasalvero-positive-char-counterexample`
- `paper-monochromaticquantumgraph-eqsystem-no-solution-even-ge4-d-eq-n-explicit`
- `paper-monochromaticquantumgraph-eqsystem10-no-solution-d10`
- `paper-monochromaticquantumgraph-eqsystem4-no-solution-d4`
- `paper-monochromaticquantumgraph-eqsystem4-no-solution-ge4`
- `paper-monochromaticquantumgraph-eqsystem4-no-solution-ge4-int`
- `paper-monochromaticquantumgraph-eqsystem4-no-solution-ge4-real`
- `paper-monochromaticquantumgraph-eqsystem4-no-solution-ge4-trinary-int`
- `paper-monochromaticquantumgraph-eqsystem6-no-solution-d6`
- `paper-monochromaticquantumgraph-eqsystem8-no-solution-d10`
- `wikipedia-agohgiuga-isweakgiuga-iff-prime-dvd`
- `wikipedia-eulerbrick-cuboidone`
- `wikipedia-legendreconjecture-bounded-gap-legendre`
- `wikipedia-perfectnumbers-euler-form`
- `wikipedia-wolstenholmeprime-wolstenholme-prime-16483`
- `wikipedia-wolstenholmeprime-wolstenholme-theorem`

## Promoted With No Explicit Upstream License

These also have clean oracle results and generator-clean artifacts. Their
selected proof source currently lacks an explicit license file or is a gist, but
the project owner accepted a bundle-and-takedown/rewrite policy. They are marked
`included`, with `licence_status = "no-explicit-license"` in
`manifest/licence_review.csv`.

- `erdosproblems-1051-erdos-1051`
- `erdosproblems-1080-erdos-1080`
- `erdosproblems-189-erdos-189`
- `erdosproblems-229-erdos-229`
- `erdosproblems-259-erdos-259`
- `erdosproblems-275-erdos-275`
- `erdosproblems-331-erdos-331`
- `erdosproblems-355-erdos-355`
- `erdosproblems-645-erdos-645`
- `erdosproblems-707-erdos-707`
- `erdosproblems-897-i`
- `erdosproblems-897-ii`
- `paper-claudescycles-cube-hamiltonian-arc-decomposition`

## Technical-Ready Pool

These tasks have a clean oracle result with reward `1.0`, zero errors, and
are reproducible from the current generator. This list includes the promoted
tasks and the license-pending tasks above.

- `erdosproblems-100-erdos-100-piepmeyer`
- `erdosproblems-1043-erdos-1043`
- `erdosproblems-1051-erdos-1051`
- `erdosproblems-1052-even-of-isunitaryperfect`
- `erdosproblems-1074-ehsnumbers-infinite`
- `erdosproblems-1080-erdos-1080`
- `erdosproblems-1082-ii`
- `erdosproblems-12-i`
- `erdosproblems-12-ii`
- `erdosproblems-12-isgood-example`
- `erdosproblems-125-erdos-125`
- `erdosproblems-125-positive-lower-density`
- `erdosproblems-138-difference`
- `erdosproblems-138-monoapnumber-two-one`
- `erdosproblems-138-monoapnumber-two-two`
- `erdosproblems-152-erdos-152`
- `erdosproblems-152-square`
- `erdosproblems-189-erdos-189`
- `erdosproblems-198-concrete`
- `erdosproblems-198-erdos-198`
- `erdosproblems-229-erdos-229`
- `erdosproblems-233-lower-bound`
- `erdosproblems-259-erdos-259`
- `erdosproblems-26-erdos-26`
- `erdosproblems-26-tenenbaum`
- `erdosproblems-263-ii`
- `erdosproblems-267-specialization-pow-two`
- `erdosproblems-275-erdos-275`
- `erdosproblems-316-erdos-316`
- `erdosproblems-331-erdos-331`
- `erdosproblems-350-erdos-350`
- `erdosproblems-355-erdos-355`
- `erdosproblems-370-erdos-370`
- `erdosproblems-379-erdos-379`
- `erdosproblems-397-erdos-397`
- `erdosproblems-399-erdos-399`
- `erdosproblems-645-erdos-645`
- `erdosproblems-707-erdos-707`
- `erdosproblems-741-i`
- `erdosproblems-741-ii`
- `erdosproblems-741-upper`
- `erdosproblems-828-phi-dvd-self-iff-pow2-pow3`
- `erdosproblems-846-erdos-846`
- `erdosproblems-897-i`
- `erdosproblems-897-ii`
- `erdosproblems-978-allow-fixed-divisors`
- `greensopenproblems-57-green-57`
- `greensopenproblems-57-z3`
- `greensopenproblems-57-z3-functional`
- `greensopenproblems-94-green-94-outer-measure`
- `mathoverflow-10799-mathoverflow-10799`
- `mathoverflow-486451-exists-semiring-unique-left-right-maximal-ne`
- `openquantumproblems-13-mutuallyunbiasedbases-dim6-bounds`
- `openquantumproblems-35-ame-11-5-open`
- `paper-casasalvero-positive-char-counterexample`
- `paper-claudescycles-cube-hamiltonian-arc-decomposition`
- `paper-monochromaticquantumgraph-eqsystem-no-solution-even-ge4-d-eq-n-explicit`
- `paper-monochromaticquantumgraph-eqsystem10-no-solution-d10`
- `paper-monochromaticquantumgraph-eqsystem4-no-solution-d4`
- `paper-monochromaticquantumgraph-eqsystem4-no-solution-ge4`
- `paper-monochromaticquantumgraph-eqsystem4-no-solution-ge4-int`
- `paper-monochromaticquantumgraph-eqsystem4-no-solution-ge4-real`
- `paper-monochromaticquantumgraph-eqsystem4-no-solution-ge4-trinary-int`
- `paper-monochromaticquantumgraph-eqsystem6-no-solution-d6`
- `paper-monochromaticquantumgraph-eqsystem8-no-solution-d10`
- `wikipedia-agohgiuga-isweakgiuga-iff-prime-dvd`
- `wikipedia-eulerbrick-cuboidone`
- `wikipedia-legendreconjecture-bounded-gap-legendre`
- `wikipedia-perfectnumbers-euler-form`
- `wikipedia-wolstenholmeprime-wolstenholme-prime-16483`
- `wikipedia-wolstenholmeprime-wolstenholme-theorem`

## Small Generator Change

No candidates remain in this category after the theorem-header extraction fix.
`arxiv-0911-2077-conjecture6-3-conjecture6-3` was reclassified under
substantial changes because its oracle proof is incomplete for the repaired
target.

## Substantial Changes

These require a real proof port, dependency decision, target/oracle alignment, or
substantial generator/source work before promotion.

For grouped tractability, work order, and next local actions, see
`docs/remaining-failures-matrix.md`.

- `arxiv-0911-2077-conjecture6-3-conjecture6-3`: theorem-header extraction is
  fixed, but the bundled oracle was generated for the old truncated target and
  only proves the internal `letI` witness; it needs a real import or port of the
  Logical Intelligence proof.
- `arxiv-1308-0994-boxdotconjecture-boxdotconjecture`: proof exists only inside a
  large Lean 4.29 Foundation modal-logic development with incompatible APIs.
- `arxiv-2602-05192-firstproof6-epsilon-light-subset-exists`: proof depends on
  multiple upstream auxiliary files; bridge to the generated target was not
  completed.
- `erdosproblems-1067-erdos-1067`: source proof ports after a one-line cardinal
  API repair, but it proves a custom induced-subgraph formulation using
  `uncountably_chromatic` and `finite_independent_paths`; the generated target
  uses `chromaticCardinal = ℵ_ 1`, arbitrary subgraphs, and
  `InfinitelyConnected`, so it needs substantial bridge lemmas.
- `erdosproblems-1071-i`: selected source proves a countably infinite set-based
  maximal collection of open unit segments, not the finite `Finset` maximal
  family required by the generated target.
- `erdosproblems-1141-erdos-1141`: proof depends on extra unproved axioms.
- `erdosproblems-1148-erdos-1148`: selected Lean-live proof requires an
  unavailable Duke theorem hypothesis.
- `erdosproblems-204-erdos-204`: selected proof is not narrow enough and has
  broad port failures.
- `erdosproblems-258-erdos-258`: proof depends on a `tao_teravainen` axiom.
- `erdosproblems-303-erdos-303`: decoded Lean 4.22 forum proof exists, but
  first compile shows broad `field_simp`, `ring`, list-sorting, and Ramsey
  finite-index failures throughout a homemade Ramsey development.
- `erdosproblems-347-erdos-347`: selected source proves a nearby
  `answer_is_yes` theorem rather than the generated target, and direct compile
  also has missing `List.get!` plus broad generated-proof failures.
- `erdosproblems-392-erdos-392`: missing Lean 4.28 project dependencies.
- `erdosproblems-418-erdos-418`: proof uses banned/native computation patterns
  and has API drift.
- `erdosproblems-427-erdos-427`: proof depends on an unproved Shiu theorem.
- `erdosproblems-434-ii`: proof depends on an axiom for theorem 2.
- `erdosproblems-457-erdos-457`: proof crashes in an asymptotic block.
- `erdosproblems-541-erdos-541`: first compile shows many independent generated
  proof-script, typeclass, and natural-order failures across the file.
- `erdosproblems-56-erdos-56`: source contains many `exact?` holes and pinned
  Lean crashes in `Mathlib.Meta.NormNum` deep recursion.
- `erdosproblems-659-erdos-659`: proof uses a custom `bernays` axiom.
- `erdosproblems-678-erdos-678`: source contains `not_erdos_678_fc`, proving the
  negation of the generated eventual-infinitude proposition with only standard
  Lean axioms; the positive triple-infinitude variant depends on the `pi_alt`
  PNT axiom, so there is no verifier-clean oracle bridge for the generated
  target.
- `erdosproblems-728-erdos-728`: selected file is a large auxiliary development,
  not a direct proof of the target.
- `erdosproblems-845-erdos-845`: direct compile has broad generated-proof
  failures and leaves the final theorem depending on `sorryAx` after failed
  elaboration; the theorem-header extraction issue is fixed.
- `erdosproblems-848-asymptotic`: source proof is very large and timed out or
  became CPU-bound.
- `erdosproblems-997-erdos-997`: proof depends on a `maynardTaoBFT` axiom.
- `oeis-357513-a357513-supercongruence`: short proof source exists, but direct
  compile fails on Lean 4.22 syntax/API drift and brittle arithmetic proof
  steps.
- `oeis-6697-conjecture`: selected proof proves the generating function for a
  formula-defined sequence `a`, not the target's subword-complexity definition;
  the missing bridge is the Allouche-Shallit formula for the actual word.
- `oeis-87719-a-formula`: frozen prefix contains `sorry`-based data used by the
  target definition.
- `util-attributes-basic-a-solved-problem-with-formal-proof`: selected URL is a
  placeholder that returns no proof.
- `util-attributes-basic-imo-2024-p6`: selected URL is the literal string
  `link`.
- `util-attributes-basic-imo-2024-p6-2`: selected URL is the literal string
  `link`.
