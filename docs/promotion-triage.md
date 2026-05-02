# Promotion Triage

Date: 2026-05-02

This is a technical-readiness triage for the 101 generated candidate tasks.
License and redistribution review are a separate promotion gate.

## Summary

- Technically ready now: 65
- Promoted now: 65
- Promoted with no-explicit-license provenance note: 9
- Ready after a small generator change: 3
- Needs substantial changes before promotion: 33
- Total: 101

Evidence used:

- Parsed all Harbor `result.json` files and matched task ids from reward trial
  ids as well as job paths.
- Ran generator consistency checks for all 101 tasks with `--include-candidates
  --check`; only `greensopenproblems-57-z3-functional` is stale relative to the
  generator.
- Ran parallel Modal oracle validation for the five validation-only tasks; all
  passed with reward `1.0` and zero errors.

## Promoted Now

These tasks have a clean Modal oracle result with reward `1.0`, zero errors,
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

These also have clean Modal oracle results and generator-clean artifacts. Their
selected proof source currently lacks an explicit license file or is a gist, but
the project owner accepted a bundle-and-takedown/rewrite policy. They are marked
`included`, with `licence_status = "no-explicit-license"` in
`manifest/licence_review.csv`.

- `erdosproblems-1080-erdos-1080`
- `erdosproblems-189-erdos-189`
- `erdosproblems-259-erdos-259`
- `erdosproblems-275-erdos-275`
- `erdosproblems-645-erdos-645`
- `erdosproblems-707-erdos-707`
- `erdosproblems-897-i`
- `erdosproblems-897-ii`
- `paper-claudescycles-cube-hamiltonian-arc-decomposition`

## Technical-Ready Pool

These tasks have a clean Modal oracle result with reward `1.0`, zero errors, and
are reproducible from the current generator. This list includes the promoted
tasks and the license-pending tasks above.

- `erdosproblems-100-erdos-100-piepmeyer`
- `erdosproblems-1043-erdos-1043`
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
- `erdosproblems-233-lower-bound`
- `erdosproblems-259-erdos-259`
- `erdosproblems-26-tenenbaum`
- `erdosproblems-263-ii`
- `erdosproblems-267-specialization-pow-two`
- `erdosproblems-275-erdos-275`
- `erdosproblems-316-erdos-316`
- `erdosproblems-350-erdos-350`
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

These are close to promotion, but should not be promoted as-is.

- `greensopenproblems-57-z3-functional`: clean Modal pass exists, but the task is
  hand-patched relative to the generator. Fix theorem-header extraction for
  `let ... := ...` in result types, regenerate, then rerun Modal.
- `arxiv-0911-2077-conjecture6-3-conjecture6-3`: oracle is bundled, but Modal
  reward is `0.0` because generated `Target.lean` is syntactically malformed at
  an internal `letI ... := by`. Fix manifest/header extraction and rerun.
- `erdosproblems-331-erdos-331`: oracle is bundled and local proof work was
  reported as passing, but Modal reward is `0.0` because the header check sees a
  changed target around an internal `let ... := ...`. Fix the same theorem-type
  extraction path and rerun.

## Substantial Changes

These require a real proof port, dependency decision, target/oracle alignment, or
substantial generator/source work before promotion.

- `arxiv-1308-0994-boxdotconjecture-boxdotconjecture`: proof exists only inside a
  large Lean 4.29 Foundation modal-logic development with incompatible APIs.
- `arxiv-2602-05192-firstproof6-epsilon-light-subset-exists`: proof depends on
  multiple upstream auxiliary files; bridge to the generated target was not
  completed.
- `erdosproblems-1051-erdos-1051`: standalone Nat-valued oracle compiles, but
  the benchmark target is integer-valued and needs a nontrivial bridge.
- `erdosproblems-1067-erdos-1067`: selected proof is a materially different
  formulation.
- `erdosproblems-1071-i`: selected proof targets a different finite/countable
  formulation.
- `erdosproblems-1141-erdos-1141`: proof depends on extra unproved axioms.
- `erdosproblems-1148-erdos-1148`: selected Lean-live proof requires an
  unavailable Duke theorem hypothesis.
- `erdosproblems-204-erdos-204`: selected proof is not narrow enough and has
  broad port failures.
- `erdosproblems-229-erdos-229`: selected proof is large Lean 4.24 code and the
  generated target is currently malformed by `letI` header extraction.
- `erdosproblems-258-erdos-258`: proof depends on a `tao_teravainen` axiom.
- `erdosproblems-26-erdos-26`: selected proof targets the non-thick variant;
  benchmark target requires `IsThick`.
- `erdosproblems-303-erdos-303`: Lean 4.22 proof exists, but port failures are
  spread through a homemade Ramsey development.
- `erdosproblems-347-erdos-347`: broad Lean 4.24 to 4.27 generated-proof port
  failures.
- `erdosproblems-355-erdos-355`: bundled, but no clean Modal result and earlier
  validation hit deep-recursion/NormNum failure.
- `erdosproblems-392-erdos-392`: missing Lean 4.28 project dependencies.
- `erdosproblems-418-erdos-418`: proof uses banned/native computation patterns
  and has API drift.
- `erdosproblems-427-erdos-427`: proof depends on an unproved Shiu theorem.
- `erdosproblems-434-ii`: proof depends on an axiom for theorem 2.
- `erdosproblems-457-erdos-457`: proof crashes in an asymptotic block.
- `erdosproblems-541-erdos-541`: broad Lean 4.24 to 4.27 port failures.
- `erdosproblems-56-erdos-56`: generated proof has many `exact?` gaps and
  recursion issues.
- `erdosproblems-659-erdos-659`: proof uses a custom `bernays` axiom.
- `erdosproblems-678-erdos-678`: oracle and benchmark statement have opposite or
  mismatched polarity.
- `erdosproblems-728-erdos-728`: selected file is a large auxiliary development,
  not a direct proof of the target.
- `erdosproblems-845-erdos-845`: large Lean 4.24 proof does not compile on the
  pinned environment and the generated checker is also malformed around an
  internal `let f := ...`.
- `erdosproblems-848-asymptotic`: source proof is very large and timed out or
  became CPU-bound.
- `erdosproblems-997-erdos-997`: proof depends on a `maynardTaoBFT` axiom.
- `oeis-357513-a357513-supercongruence`: Lean 4.22 proof has many Lean 4.27
  port errors.
- `oeis-6697-conjecture`: selected proof is for the wrong theorem and the
  generated checker is malformed.
- `oeis-87719-a-formula`: frozen prefix contains `sorry`-based data used by the
  target definition.
- `util-attributes-basic-a-solved-problem-with-formal-proof`: selected URL is a
  placeholder that returns no proof.
- `util-attributes-basic-imo-2024-p6`: selected URL is the literal string
  `link`.
- `util-attributes-basic-imo-2024-p6-2`: selected URL is the literal string
  `link`.
