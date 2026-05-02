# Remaining Failures Matrix

Date: 2026-05-02

This matrix tracks the 31 remaining candidates after 70 of the 101 generated
candidate tasks were promoted. The goal is to separate promising repair work
from cases that are blocked by missing proofs, unjustified axioms, or dependency
decisions.

## Work Order

1. **Statement alignment / bridge candidates**: highest expected yield. These
   resemble `erdosproblems-1051-erdos-1051`, where the proof may be correct but
   targets a nearby formulation.
2. **Lean API and porting candidates**: correct proof source likely exists, but
   the source needs Lean 4.22/4.24/4.28 to pinned Lean 4.27.0 repair.
3. **Large proof reduction / dependency import candidates**: try to isolate the
   theorem actually needed, as with `erdosproblems-355-erdos-355`.
4. **Verifier-rule conflicts**: decide whether a banned-computation proof can be
   rewritten into a verifier-clean proof.
5. **External dependency decisions**: likely not v1 unless we deliberately add
   and pin a new project.
6. **Axiom, unavailable theorem, or missing source cases**: defer until the
   promising groups are exhausted or an alternate complete proof is found.

## Summary By Bucket

| Bucket | Count | Expected yield | Recommended action |
| --- | ---: | --- | --- |
| Statement alignment / bridge | 1 | Low-medium | Develop semantic bridge lemmas only if the source theorem clearly implies the target. |
| Lean API / proof port | 7 | Medium | Port locally one at a time; prefer shared compatibility fixes for repeated `plby/lean-proofs` patterns. |
| Large proof reduction / import | 6 | Medium | Trim irrelevant sections or import required auxiliary files; validate locally before promotion. |
| Verifier-rule conflict | 1 | Low-medium | Determine whether banned native/computation steps are essential or replaceable. |
| External dependency decision | 2 | Low for v1 | Defer unless we accept new pinned dependencies. |
| Axiom / unavailable theorem | 7 | Low | Do not promote without replacing axioms by proofs or finding alternate proof sources. |
| Missing or placeholder proof source | 3 | Very low | Exclude or mark blocked unless a real proof URL is found. |
| Wrong answer / polarity mismatch | 1 | Very low | Exclude unless the upstream Formal Conjectures target is corrected or a different theorem is generated. |
| Wrong proof source / non-implication | 2 | Very low | Exclude or replace the selected proof source; the available theorem does not imply the generated target. |
| Source/generated target contains sorry dependency | 1 | Low | Requires source/generator redesign rather than oracle repair. |

Total: 31.

## Statement Alignment / Bridge

These are the first candidates to try. The likely repair is not a large proof
port but a bridge theorem from the available proof statement to the generated
benchmark statement.

| Task | Source | Current issue | Tractability | Next local step |
| --- | --- | --- | --- | --- |
| `erdosproblems-1067-erdos-1067` | `plby/lean-proofs`, Lean 4.24 | Source proof ports after a one-line cardinal API repair, but it proves a custom induced-subgraph formulation using `uncountably_chromatic` and `finite_independent_paths`; the generated target uses `chromaticCardinal = ℵ_ 1`, arbitrary subgraphs, and `InfinitelyConnected`. | Low-medium | Only continue if we want to write substantial bridge lemmas relating these graph/connectivity formulations. |

## Lean API / Proof Port

These likely have real proof content but need porting to the pinned Lean
4.27.0/mathlib environment. The repeated `plby/lean-proofs` source makes this a
possible batch theme, even if validation remains local and one task at a time.

| Task | Source | Current issue | Tractability | Next local step |
| --- | --- | --- | --- | --- |
| `erdosproblems-229-erdos-229` | `plby/lean-proofs`, Lean 4.24 | Large Lean 4.24 code still needs substantial porting. | Medium | Compile reduced source locally; fix first API break and assess error density. |
| `erdosproblems-303-erdos-303` | Erdős forum Lean 4.22 | Port failures spread through a homemade Ramsey development. | Medium-low | Decode/source the forum proof; identify whether Ramsey helpers are self-contained. |
| `erdosproblems-347-erdos-347` | External Lean project | Broad Lean 4.24 to 4.27 generated-proof failures. | Medium-low | Compile source in isolation and classify first failures as API drift vs incomplete generated proof. |
| `erdosproblems-541-erdos-541` | `plby/lean-proofs`, Lean 4.24 | Broad Lean 4.24 to 4.27 port failures. | Medium | Re-run local compile and compare with `229` for shared API drift. |
| `erdosproblems-56-erdos-56` | `plby/lean-proofs`, Lean 4.24 | Generated proof has many `exact?` gaps and recursion issues. | Low-medium | Determine whether gaps are actual missing proof obligations or failed generated suggestions. |
| `erdosproblems-845-erdos-845` | `plby/lean-proofs`, Lean 4.24 | Large Lean 4.24 proof does not compile on pinned environment. | Medium-low | Compile source locally and see whether failures are concentrated enough to repair. |
| `oeis-357513-a357513-supercongruence` | Formal Conjectures commit, Lean 4.22-era | Many Lean 4.27 port errors. | Medium-low | Port against pinned Formal Conjectures source; source is otherwise suitable if it becomes verifier-clean. |

## Large Proof Reduction / Import

These are promising if the relevant theorem can be isolated from irrelevant
large sections or if a small set of auxiliary files can be bundled cleanly.

| Task | Source | Current issue | Tractability | Next local step |
| --- | --- | --- | --- | --- |
| `arxiv-0911-2077-conjecture6-3-conjecture6-3` | Logical Intelligence proof | Existing oracle proves only the old truncated internal `letI` witness. | Medium | Import or port the real theorem around the cited source line; rebuild oracle for repaired target. |
| `arxiv-2602-05192-firstproof6-epsilon-light-subset-exists` | Archon FirstProof result | Proof depends on multiple upstream auxiliary files; bridge incomplete. | Medium | Identify minimal auxiliary file closure and see whether it can be bundled under oracle. |
| `erdosproblems-204-erdos-204` | Woett Lean file | Selected proof is not narrow enough and has broad port failures. | Medium-low | Try `erdos-355` style reduction to the target theorem dependencies. |
| `erdosproblems-457-erdos-457` | Woett Lean file | Proof crashes in an asymptotic block. | Medium-low | Isolate target dependency slice; determine whether crashing block is needed. |
| `erdosproblems-728-erdos-728` | `plby/lean-proofs`, Lean 4.24 auxiliary file | Selected file is a large auxiliary development, not a direct proof. | Low-medium | Locate actual target theorem in the auxiliary development or mark wrong-source. |
| `erdosproblems-848-asymptotic` | External large proof | Source proof is very large and timed out or became CPU-bound. | Low-medium | Try direct Lean compile with longer local timeout; if timeout persists, profile or reduce imports. |

## Verifier-Rule Conflict

| Task | Source | Current issue | Tractability | Next local step |
| --- | --- | --- | --- | --- |
| `erdosproblems-418-erdos-418` | `plby/lean-proofs`, Lean 4.24 | Proof uses banned/native computation patterns and has API drift. | Low-medium | Decide whether native computation can be replaced by explicit certificates acceptable to the verifier. |

## External Dependency Decision

These may have valid proofs but are not clean standalone oracle ports under the
current pinned environment.

| Task | Source | Current issue | Tractability | Next local step |
| --- | --- | --- | --- | --- |
| `arxiv-1308-0994-boxdotconjecture-boxdotconjecture` | FormalizedFormalLogic/Foundation | Proof exists only inside a large Lean 4.29 modal-logic development. | Low for v1 | Defer unless we decide to pin and vendor a second Lean project. |
| `erdosproblems-392-erdos-392` | PrimeNumberTheoremAnd project | Missing Lean 4.28 project dependencies. | Low for v1 | Defer or create an explicit dependency-import plan. |

## Axiom Or Unavailable Theorem

These should not be promoted as benchmark tasks unless the axiom is replaced by
a real proof or an alternate complete proof source is found.

| Task | Source | Current issue | Tractability | Next local step |
| --- | --- | --- | --- | --- |
| `erdosproblems-1141-erdos-1141` | External Lean file | Proof depends on extra unproved axioms. | Low | Search for an alternate complete proof; otherwise leave blocked. |
| `erdosproblems-1148-erdos-1148` | Lean-live source | Requires unavailable Duke theorem hypothesis. | Low | Treat as blocked until the missing theorem is formalized or replaced. |
| `erdosproblems-258-erdos-258` | Lean-live / gist | Depends on a `tao_teravainen` axiom. | Low | Do not promote without a proof of the axiom. |
| `erdosproblems-427-erdos-427` | External gist | Depends on an unproved Shiu theorem. | Low | Do not promote without a proof of Shiu theorem or a different proof. |
| `erdosproblems-434-ii` | Erdős forum source | Depends on an axiom for theorem 2. | Low | Search for a complete theorem 2 formalization; otherwise block. |
| `erdosproblems-659-erdos-659` | `plby/lean-proofs`, Lean 4.24 | Uses a custom `bernays` axiom. | Low | Do not promote unless the axiom is eliminated. |
| `erdosproblems-997-erdos-997` | Lean-live / gist | Depends on a `maynardTaoBFT` axiom. | Low | Do not promote without the underlying Maynard-Tao formalization. |

## Missing Or Placeholder Proof Source

These are unlikely to be repairable from the current manifest metadata.

| Task | Source | Current issue | Tractability | Next local step |
| --- | --- | --- | --- | --- |
| `util-attributes-basic-a-solved-problem-with-formal-proof` | Placeholder URL | Selected URL is `https://example.com/proof`. | Very low | Exclude or replace manifest entry with a real proof URL. |
| `util-attributes-basic-imo-2024-p6` | Placeholder string | Selected URL is the literal string `link`. | Very low | Exclude or replace manifest entry with a real proof URL. |
| `util-attributes-basic-imo-2024-p6-2` | Placeholder string | Selected URL is the literal string `link`. | Very low | Exclude or replace manifest entry with a real proof URL. |

## Wrong Answer Or Polarity Mismatch

These are not ordinary bridge candidates. The available proof source indicates
that the generated target has the wrong truth value or is stronger than the
proved theorem in a way that cannot be repaired by a small theorem bridge.

| Task | Source | Current issue | Tractability | Next local step |
| --- | --- | --- | --- | --- |
| `erdosproblems-678-erdos-678` | `plby/lean-proofs`, Lean 4.24 | Source contains `not_erdos_678_fc`, proving the negation of the generated eventual-infinitude proposition with only standard Lean axioms; the positive triple-infinitude variant depends on the `pi_alt` PNT axiom. | Very low | Exclude as generated unless Formal Conjectures corrects the target/answer or we generate a different theorem with a verifier-clean proof. |

## Wrong Proof Source Or Non-Implication

These selected sources prove a nearby but non-implying theorem. They should not
be promoted unless a different proof source is found or the missing mathematical
bridge is formalized.

| Task | Source | Current issue | Tractability | Next local step |
| --- | --- | --- | --- | --- |
| `erdosproblems-1071-i` | `plby/lean-proofs`, Lean 4.24 | Selected source proves a countably infinite set-based maximal collection of open unit segments; the generated target asks for a finite `Finset` maximal family in the unit square. | Very low | Search for a source proving the finite Danzer construction, or exclude this generated target for now. |
| `oeis-6697-conjecture` | AxiomMath external Lean | Selected proof proves the generating function for a formula-defined sequence `a`; the generated target's `a` is the actual subword-complexity cardinality. The source notes that formalizing the Allouche-Shallit formula is the missing bridge. | Very low | Exclude until the subword-complexity formula is formalized or a proof of the target definition is found. |

## Source Or Generator Issue

| Task | Source | Current issue | Tractability | Next local step |
| --- | --- | --- | --- | --- |
| `oeis-87719-a-formula` | Formal Conjectures PR commit | Frozen prefix contains `sorry`-based data used by the target definition. | Low | Decide whether to alter source extraction to avoid `sorry`-dependent data or exclude from v1. |
