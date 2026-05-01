# FormalConjectures-Bench: A Lean Theorem-Proving Benchmark from Formally-Resolved Conjectures

**Status:** Project brief / kickoff document
**Target output:** Research paper + open-source Harbor benchmark
**Owner:** Allen Graham Hart
**Date created:** May 2026

---

## TL;DR

Build a Harbor benchmark of approximately 100 instances drawn from Google DeepMind's [Formal Conjectures](https://github.com/google-deepmind/formal-conjectures) project, restricted to the subset of conjectures that have a formal proof attached (`@[formal_proof using lean4]` or `@[formal_proof using formal_conjectures]`). Each instance gives the agent a Lean 4 theorem statement and asks it to produce a complete, axiom-clean proof. Score with `#print axioms` plus a golden type-recheck against the canonical proof. Evaluate three frontier models, publish.

The pitch in one sentence: existing Lean benchmarks (miniF2F, PutnamBench, CombiBench) target competition mathematics; this one targets research-mathematics-adjacent results from named conjecture lists with provenance in real literature, and it has the property that every instance has a known proof so the harness itself can be canary-checked.

---

## Background

### Formal Conjectures

[Formal Conjectures](https://github.com/google-deepmind/formal-conjectures) is a Google DeepMind project collecting formalised statements of open and recently-resolved mathematical conjectures in Lean 4 with Mathlib. As of May 2026:

- 1,850 total problems (1,027 open, 823 solved)
- 104 with `formal_proof` attribute attached (a Lean 4 proof exists somewhere)
- Sources include Erdős Problems (1,311 entries), Wikipedia (476), Green's Open Problems (160), Hilbert/Millennium/Smale lists, MathOverflow, OEIS, and arXiv papers
- Tracks monthly tagged Mathlib releases; Apache 2.0 / CC-BY licensed
- Active project: 1,279 commits, 756 open issues, 113 open PRs as of this writing

The dashboard is at [google-deepmind.github.io/formal-conjectures](https://google-deepmind.github.io/formal-conjectures/) and the live problem browser is at [google-deepmind.github.io/formal-conjectures/browse/](https://google-deepmind.github.io/formal-conjectures/browse/).

### Why the formally-proved subset

The 104 instances with attached formal proofs have three properties that matter:

1. **Tractability is bounded** — a proof exists, so the task is known to be solvable.
2. **The harness is canary-checkable** — running the oracle through the verifier should always score 1.0; if it doesn't, the harness is broken, not the model.
3. **Strong reward-hack defences** — golden-file type-rechecking against the canonical proof catches any attempt to weaken the theorem statement.

We are explicitly *not* targeting the 719 informally-solved-only instances or the 1,027 open conjectures in v1. Those need different verification strategies and belong in a follow-up paper.

### Existing benchmarks for context

- [PutnamBench](https://github.com/trishullab/PutnamBench) — Putnam competition problems
- [miniF2F](https://github.com/openai/miniF2F) — high-school olympiad
- [CombiBench](https://arxiv.org/abs/2505.03171) — 100 combinatorial problems in Lean 4
- [LeanGeo-Bench](https://github.com/project-numina/LeanGeo) — Lean 4 geometry from IMO

The proposed benchmark is distinct in occupying the research-mathematics niche with explicit provenance to named conjecture collections.

---

## Existing prior art to coordinate with (do this before building)

Before writing any code, post on these channels and check for parallel efforts:

1. **[Formal Conjectures Zulip channel](https://leanprover.zulipchat.com/#narrow/channel/524981-Formal-conjectures)** — ask whether the DeepMind team or contributors are already building this.
2. **[Harbor / terminal-bench-3 discussions](https://github.com/harbor-framework/terminal-bench-3/discussions)** — confirm the framework fit and any conventions to follow.
3. **[teorth/erdosproblems wiki: AI contributions](https://github.com/teorth/erdosproblems/wiki/AI-contributions-to-Erd%C5%91s-problems)** — track who is doing what across the Erdős corpus specifically.
4. **GPT-Erdos by Neel Somani** — [github.com/neelsomani/gpt-erdos](https://github.com/neelsomani/gpt-erdos), already documenting LLM-driven proof search on Erdős problems.

If any of these turn up an in-progress benchmark with the same scope, coordinate rather than duplicate.

---

## Source repositories

The oracle proofs are scattered across several repos. Initial known sources:

- **Boris Alexeev's [plby/lean-proofs](https://github.com/plby/lean-proofs)** — many Erdős problem proofs by Aristotle (Harmonic). Files at `src/v4.24.0/ErdosProblems/Erdos<N>.lean`. All pinned to Lean 4.24.0 / Mathlib commit `f897ebcf72cd16f89ab4577d0c826cd14afaafc7`.
- **Mathlib itself** — some classical results referenced as `formal_proof using lean4 at "https://github.com/leanprover-community/mathlib4/..."`.
- **AlphaProof outputs** — Google DeepMind has published some AlphaProof-generated proofs with permissive licensing; check per-instance.
- **Other contributor repos** — pull from the `formal_proof` URL on each instance.

Per-instance licensing must be checked before redistribution. Apache 2.0 / MIT / CC-BY repos are fine; anything bespoke or proprietary needs separate handling (link-only, no oracle bundling).

---

## Reference implementation: Takens task

The starting point for the task structure is Allen's [`prove-takens-embedding-lean`](https://github.com/harbor-framework/terminal-bench-3/pull/166) PR. Key features to carry over:

- Public environment exposes only theorem stub + frozen API (`Core.lean` equivalent)
- Hidden golden environment with full oracle proof
- Verifier: `lake build` + `#print axioms` + golden type-recheck via `exact @canonical_proof`
- Banned tactics/options: `native_decide`, `@[implemented_by]`, `@[extern]`, `unsafe`, `run_cmd`, `#eval`, `initialize`
- Allowed axiom set: `propext`, `Classical.choice`, `Quot.sound` (and `Lean.ofReduceBool` / `Lean.ofReduceNat` / `Lean.trustCompiler` only if `native_decide` is permitted — recommend banning)
- Pinned Lean toolchain + Mathlib commit per-task

**Additional hardening for this benchmark:** Set `network = "off"` (or the equivalent network-disabled flag) in `task.toml`. The oracle proofs live in public GitHub repositories (plby/lean-proofs in particular), so an agent with internet access can simply fetch them. Disabling network egress closes this attack vector entirely. The Lean toolchain, Mathlib, and any other dependencies must be pre-baked into the environment Dockerfile rather than fetched at trial time.

The major architectural difference for FormalConjectures-Bench: instead of one bespoke task, build **one parameterised task type** that takes an instance ID and dynamically generates the environment from the manifest at task-load time.

---

## Sample oracle sizes

From inspection of three Aristotle-generated proofs in plby/lean-proofs:

| Problem | Difficulty | Lines | LOC | Size |
|---|---|---|---|---|
| Erdős 370 | Easy ("trivial proof" per Steinerberger) | 190 | 163 | 10.5 KB |
| Erdős 124b | Medium (the famous 6-hour autonomous solve) | 407 | 370 | 24.6 KB |
| Erdős 1026 | Hard (Erdős–Szekeres generalisation) | 3,658 | 3,462 | 269 KB |

Distribution across the full 104 is expected to be long-tailed: most in 150–500 LOC range, a few thousand-plus outliers. Total oracle codebase plausibly 30–60k LOC.

These proofs are AI-generated and **not idiomatic Lean** — heavy `aesop` / `nlinarith` / `grind` / `simp_all`, dense one-liner tactic blocks, pervasive `set_option linter.style.X false` overrides, and `set_option maxHeartbeats 0` for the larger ones. The harness must allow these.

---

## Architecture

```
formal-conjectures-bench/
├── manifest/
│   ├── build_manifest.py           # walks FormalConjectures, extracts instances
│   ├── manifest.json               # canonical instance list
│   └── pinned_versions.toml        # FC commit, Mathlib version, Lean toolchain
├── tasks/
│   └── prove-formal-conjecture/    # ONE parameterised Harbor task
│       ├── task.toml
│       ├── instruction.md.tmpl     # templated per instance
│       ├── environment/            # generated per-instance at load time
│       ├── solution/               # oracle, fetched from manifest
│       └── tests/                  # axiom audit + golden recheck
├── oracles/
│   └── <instance_id>/              # mirrored or symlinked oracle proofs
├── eval/
│   ├── run_baseline.py             # invokes Harbor across the manifest
│   └── analyse_results.py          # produces tables, contamination strata
└── paper/
    ├── main.tex
    └── tables/
```

The single Harbor task takes an `instance_id` parameter (or per-instance task subdirectories generated from the manifest, depending on Harbor's conventions — confirm with maintainers). Either way the manifest is the source of truth; everything downstream is generated.

---

## Implementation phases

### Phase 0: Coordination and manifest validation (1–2 days)

- Post on Formal Conjectures Zulip and Harbor discussions
- Pull FormalConjectures at a pinned commit
- Walk `FormalConjectures/**/*.lean`, extract every theorem with `formal_proof using lean4` or `formal_proof using formal_conjectures` attribute
- Output manifest JSON: `{instance_id, theorem_name, file_path, source_url, formal_proof_url, ams_tags, category, uses_answer_elaborator}`
- **Sanity-check the count.** Real number after filtering may be 70–90, not 104. Document the actual number.
- Per instance, classify: `oracle_kind` ∈ {`mathlib`, `lean_proofs_repo`, `formal_conjectures_inline`, `external`, `unavailable`}
- Drop instances where the oracle isn't fetchable or licence-compatible

### Phase 1: Single-instance proof of concept (3–5 days)

Pick three instances spanning the difficulty range — recommend Erdős 370 (easy), Erdős 124b (medium), Erdős 1026 (hard). For each, manually:

- Build the environment Dockerfile pinned to the right Lean/Mathlib (with `lake exe cache get` baked in so no network fetch is needed at trial time)
- Configure `task.toml` with network access disabled
- Extract the theorem statement and any frozen API definitions
- Place the oracle in the hidden golden directory
- Write the verifier: `lake build`, `#print axioms` parse, `exact @canonical_proof` golden recheck
- Run a manual oracle-pass test (oracle should always score 1.0)
- Run a manual agent-pass test (one model, one trial each) to confirm end-to-end works

This is the equivalent of the Takens task, but executed three times to surface generalisation issues before automating.

### Phase 2: Manifest-driven generalisation (1 week)

- Convert the three hand-built tasks into one parameterised task generated from the manifest
- Validate against all 104 instances by running each oracle through the verifier — 100% should pass. Anything that doesn't, fix or drop.
- This phase is where most "long-tail" issues surface: instances with multi-theorem files, instances with definitions that need additional API freezing, instances with build flags that conflict with the harness defaults.
- Produce a final canary report: "of 104 candidate instances, N passed oracle verification; the harness is calibrated against these N."

### Phase 3: Evaluation (3–7 days, mostly compute-bound)

- Three trials per (model, instance) pair
- Three frontier models: recommend Opus 4.7, GPT-5.x, Gemini 3 Pro
- Stratify reporting by:
  - AMS subject
  - Oracle line-count tier (small / medium / large)
  - Plausible contamination (oracle published before vs. after model cutoff)
  - With-citation vs. without-citation prompting (run both modes)
- Estimated total cost: $5–15k depending on size distribution

### Phase 4: Paper writing (2–4 weeks)

- Main table: pass@1 and pass@3 by model, with stratifications above
- Cheat-mode results as a separate table (analogue of the `/cheat` runs in the Takens PR)
- Failure mode analysis: what kinds of proofs do models reliably fail on?
- Comparison to existing Lean benchmarks in a related-work section
- Open release: manifest, task code, eval scripts, anonymised trajectories

---

## Verifier design

For each agent submission:

1. **File-level filter.** Only accept `.lean` files in the editable subtree. Reject everything else.
2. **Build.** `lake build` against pinned Lean toolchain + Mathlib commit, in a fresh container.
3. **Banned-feature scan.** Source grep for `native_decide`, `@[implemented_by]`, `@[extern]`, `unsafe`, `run_cmd`, `#eval`, `initialize`, `axiom` keyword, `sorry`. Reject if any present.
4. **Axiom audit.** `#print axioms <theorem_name>` must equal `[propext, Classical.choice, Quot.sound]` (no `sorryAx`, no user axioms, no `Lean.ofReduceBool` unless explicitly allowed).
5. **Golden type-recheck.** Hidden file with `theorem golden : <expected_type> := @<theorem_name>` must compile. This catches statement-weakening attacks.
6. **Sanity canary.** Compile a known-`sorry`'d theorem in the same environment and verify `sorryAx` IS detected. Confirms the verifier itself works.

Steps 3–6 are the ones from the Takens task; reuse that code.

### Verifier limitations to acknowledge in the paper

- Statement-misformalisation in FormalConjectures itself is not caught by any of these checks. If the formal statement is a weaker version of the informal Erdős problem, a clean proof is still useless mathematically. (See [Erdős 480 issue](https://github.com/google-deepmind/formal-conjectures/issues/1282) for a real example.)
- The `answer()` elaborator can be trivially "solved" by `answer({n | P n})` etc. Most formally-proved instances should have concrete answers filled in already, but check this during manifest building.
- Container-level isolation is imperfect; a determined attacker could in principle exploit Harbor framework state. Document this as a known limitation rather than pretending it's solved.

---

## Reward-hacking hardening

### Network isolation

`task.toml` must set the network flag to disabled for every trial. Since the oracle proofs are publicly hosted on GitHub (predominantly plby/lean-proofs, with some in Mathlib and elsewhere), an agent with web access can solve the task by fetching the oracle directly rather than producing its own proof. This is the single highest-yield reward-hacking vector for this benchmark and the cheapest to close.

Practical implications:

- All Lean toolchain components, Mathlib, and any other dependencies must be installed into the environment Dockerfile at build time (`lake exe cache get` baked into the image), not fetched at trial time.
- The `task.toml` should explicitly declare network off; verify the setting actually takes effect by attempting an outbound fetch from inside the container as part of the harness self-test.
- Document this as a benchmark-level constraint in the paper: results are conditional on the agent having no internet access. This is a different (and stronger) condition than most coding benchmarks but is necessary here.

This addresses *trial-time* oracle leakage. It does *not* address *training-time* contamination (the oracle being in the model's training corpus), which is a separate problem handled by the per-instance publication-date stratification in the evaluation phase.

### Other defences

From the Takens PR's three-month review process, expect adversarial trials to find:

- Type-signature weakening (caught by golden recheck)
- `sorry` smuggled through `partial def` or `unsafe` (caught by banned-feature scan)
- Custom axioms (caught by axiom audit)
- `native_decide` to close goals via compiler trust (banned outright)
- Manifest-level definition redefinition (caught by frozen-API freezing)

Things that are harder to defend against and need framework-level support, document as known limitations:

- Cross-task state leakage in the Harbor container
- Sandboxing of `IO` operations during elaboration

Run a `/cheat` evaluation explicitly as part of the methodology (reuse Harbor's existing cheating-prompt infrastructure from terminal-bench-3).

---

## Pinning and reproducibility

Everything must be version-pinned and the pin must be in the manifest:

- Lean toolchain: `leanprover/lean4:v4.X.Y` (whichever FC's current release tracks)
- Mathlib commit hash
- FormalConjectures commit hash
- Harbor framework version
- Per-oracle source repo + commit hash

Benchmark releases get versioned: `formal-conjectures-bench@2026-MM-leanX.Y.Z`. Six-month-stale results must remain reproducible; this is non-negotiable for a benchmark paper.

---

## Reporting structure (paper outline)

1. **Introduction** — research-math-adjacent benchmark gap, contribution
2. **Related work** — miniF2F, PutnamBench, CombiBench, FrontierMath, LeanGeo
3. **Dataset construction** — Formal Conjectures, the formally-proved subset, manifest pipeline, curation decisions, final N
4. **Verification methodology** — verifier design, reward-hacking defences, golden canary
5. **Evaluation** — models, settings, contamination handling
6. **Results** — main table + stratifications + cheat-mode + failure analysis
7. **Limitations** — misformalisation, container isolation, contamination upper bound
8. **Conclusion + open dataset** — release URLs, future work (719 informal-only instances)

Draft the abstract before writing code. Two paragraphs, no implementation details, just claim and contribution. If it doesn't read convincingly now, the project isn't scoped right.

---

## Risks and mitigations

| Risk | Likelihood | Mitigation |
|---|---|---|
| Parallel effort already in progress | Medium | Phase 0 coordination posts |
| 104 number drops below 70 after curation | Medium | Document honestly; 70 is still publishable |
| Contamination invalidates results for some models | High | Stratify by oracle publication date vs. model cutoff |
| Reward-hacking found post-publication | Medium-high | Run `/cheat` evaluation explicitly; document framework-level limitations |
| Agent fetches oracle from GitHub at trial time | High if not addressed | `network = off` in `task.toml`; pre-bake all dependencies in Dockerfile; verify via harness self-test |
| Mathlib version drift breaks oracle proofs | Low (we pin) | Pin everything; document recompilation procedure |
| Harbor framework changes mid-project | Low-medium | Pin Harbor version; coordinate with maintainers |
| Oracle proof licensing not redistributable | Medium | Per-instance licence audit during manifest build; link-only fallback |
| Compute budget exceeds $15k | Low-medium | Cost-cap per instance; drop largest oracles for v1 if needed |

---

## Open questions to resolve early

- Does the `formal_proof` attribute in FormalConjectures anchor to a specific theorem name in the linked file, or just to the file? (Affects disambiguation when files contain multiple theorems.)
- What's Harbor's convention for parameterised tasks — single task with instance ID, or generated subdirectory per instance? Confirm with maintainers.
- For instances using the `answer()` elaborator, is the canonical answer always already filled in (`answer(True)`, `answer(False)`, or a concrete term) for the formally-proved subset? If any are still `answer(sorry)`, drop them or handle separately.
- Citation-mode policy: default to with-citation (realistic workflow) or without (pure proof generation)? Recommendation: report both.

---

## Concrete first session prompt for the coding agent

> "Build the manifest. Clone https://github.com/google-deepmind/formal-conjectures at HEAD, pin to that commit. Walk every `.lean` file under `FormalConjectures/`. For each `theorem` declaration, extract: theorem name, file path, all `@[category ...]` tags, all `@[AMS ...]` tags, presence and value of `@[formal_proof ...]` attribute (with kind and URL), and whether the body uses the `answer()` elaborator. Filter to theorems where category includes `research solved` AND `formal_proof` is present with kind `lean4` or `formal_conjectures`. Output `manifest.json` as a list of instance records. Print summary statistics: total count, breakdown by AMS subject, breakdown by oracle source domain, count using `answer()`. Do not fetch oracle proofs yet — that's the next step."

After that runs and the count is established, the next session is: fetch oracle proofs, classify by line-count tier, identify the three exemplar instances for Phase 1.

---

## Useful links

**Source repositories:**
- [google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures) — primary dataset
- [plby/lean-proofs](https://github.com/plby/lean-proofs) — Aristotle/Harmonic Erdős proofs
- [teorth/erdosproblems](https://github.com/teorth/erdosproblems) — Erdős database
- [neelsomani/gpt-erdos](https://github.com/neelsomani/gpt-erdos) — related LLM-on-Erdős effort
- [harbor-framework/harbor](https://github.com/harbor-framework/harbor) — Harbor framework
- [harbor-framework/terminal-bench-3](https://github.com/harbor-framework/terminal-bench-3) — Terminal-Bench

**Documentation:**
- [Formal Conjectures dashboard](https://google-deepmind.github.io/formal-conjectures/)
- [Formal Conjectures docs](https://google-deepmind.github.io/formal-conjectures/doc/)
- [Mathlib4](https://github.com/leanprover-community/mathlib4)
- [Lean 4 documentation](https://leanprover.github.io/lean4/doc/)

**Community:**
- [Formal Conjectures Zulip channel](https://leanprover.zulipchat.com/#narrow/channel/524981-Formal-conjectures)
- [Lean Zulip](https://leanprover.zulipchat.com/)

**Reference task:**
- [prove-takens-embedding-lean PR #166](https://github.com/harbor-framework/terminal-bench-3/pull/166)

**Related benchmarks (for related-work section):**
- [PutnamBench](https://github.com/trishullab/PutnamBench)
- [miniF2F](https://github.com/openai/miniF2F)
- [CombiBench paper](https://arxiv.org/abs/2505.03171)
- [LeanGeo paper](https://arxiv.org/abs/2508.14644)

**Sample oracle proofs (referenced in this brief):**
- [Erdős 370 oracle](https://github.com/plby/lean-proofs/blob/main/src/v4.24.0/ErdosProblems/Erdos370.lean) — ~190 lines
- [Erdős 124b oracle](https://github.com/plby/lean-proofs/blob/main/src/v4.24.0/ErdosProblems/Erdos124b.lean) — ~407 lines
- [Erdős 1026 oracle](https://github.com/plby/lean-proofs/blob/main/src/v4.24.0/ErdosProblems/Erdos1026.lean) — ~3,658 lines

**Background reading:**
- ["Story of Erdős Problem 126" by Tao](https://terrytao.wordpress.com/2025/12/08/the-story-of-erdos-problem-126/)
- ["AI uncovers solutions to Erdős problems" — Scientific American](https://www.scientificamerican.com/article/ai-uncovers-solutions-to-erdos-problems-moving-closer-to-transforming-math/)
- ["Resolution of Erdős Problem #728"](https://arxiv.org/abs/2601.07421) — example writeup of an Aristotle proof

---

## Scope discipline (the things to NOT do in v1)

- Don't include the 719 informally-solved-only instances. Different paper.
- Don't include the 1,027 open conjectures. Different paper.
- Don't evaluate every model. Three frontier models is enough.
- Don't build novel framework infrastructure. Use Harbor as it is.
- Don't try to fix misformalisations in FormalConjectures upstream as part of this work — log them as issues, move on.
- Don't write the abstract last.

---

*This brief is intended as kickoff context for a coding agent. Treat sections as non-binding suggestions to revise as implementation surfaces real constraints. Update the manifest stats and oracle counts in this document as Phase 0 completes.*
