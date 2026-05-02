# Remaining Failures Matrix

Date: 2026-05-02

This matrix tracks the 32 remaining candidates after 69 of the 101 generated
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
| Statement alignment / bridge | 5 | Medium-high | Inspect source theorem and target theorem side by side; attempt a bridge if implication is mathematically direct. |
| Lean API / proof port | 7 | Medium | Port locally one at a time; prefer shared compatibility fixes for repeated `plby/lean-proofs` patterns. |
| Large proof reduction / import | 6 | Medium | Trim irrelevant sections or import required auxiliary files; validate locally before promotion. |
| Verifier-rule conflict | 1 | Low-medium | Determine whether banned native/computation steps are essential or replaceable. |
| External dependency decision | 2 | Low for v1 | Defer unless we accept new pinned dependencies. |
| Axiom / unavailable theorem | 7 | Low | Do not promote without replacing axioms by proofs or finding alternate proof sources. |
| Missing or placeholder proof source | 3 | Very low | Exclude or mark blocked unless a real proof URL is found. |
| Source/generated target contains sorry dependency | 1 | Low | Requires source/generator redesign rather than oracle repair. |

Total: 32.

## Statement Alignment / Bridge

These are the first candidates to try. The likely repair is not a large proof
port but a bridge theorem from the available proof statement to the generated
benchmark statement.

| Task | Source | Current issue | Tractability | Next local step |
| --- | --- | --- | --- | --- |
| `erdosproblems-678-erdos-678` | `plby/lean-proofs`, Lean 4.24 | Oracle and benchmark statement have opposite or mismatched polarity. | Medium | Compare the source theorem with `Erdos678.erdos_678`; check whether polarity mismatch is a target/header issue or a true non-implication. |
| `erdosproblems-26-erdos-26` | `plby/lean-proofs`, Lean 4.24 | Selected proof targets the non-thick variant; target requires `IsThick`. | Medium | Compare with promoted `erdosproblems-26-tenenbaum`; see whether that proof can imply the base target or whether the base target is strictly stronger. |
| `erdosproblems-1067-erdos-1067` | `plby/lean-proofs`, Lean 4.24 | Selected proof is a materially different formulation. | Medium-low | Inspect source theorem and decide whether a bridge is plausible before porting. |
| `erdosproblems-1071-i` | `plby/lean-proofs`, Lean 4.24 | Selected proof targets a different finite/countable formulation. | Medium-low | Inspect statement relation; only port if the source theorem clearly implies the target. |
| `oeis-6697-conjecture` | AxiomMath external Lean | Selected proof is for the wrong theorem. | Low-medium | Recheck whether another theorem in the source file proves the generated target; otherwise mark as wrong-source. |

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

## Source Or Generator Issue

| Task | Source | Current issue | Tractability | Next local step |
| --- | --- | --- | --- | --- |
| `oeis-87719-a-formula` | Formal Conjectures PR commit | Frozen prefix contains `sorry`-based data used by the target definition. | Low | Decide whether to alter source extraction to avoid `sorry`-dependent data or exclude from v1. |
