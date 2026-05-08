# FormalConjectures-Bench

FormalConjectures-Bench is a Harbor-native benchmark of Lean 4 theorem-proving
tasks derived from Google DeepMind's Formal Conjectures project.

The current `main` branch has two checked-in task roots:

- `tasks/`: 74 gold-solution tasks with bundled local Lean oracles. These run
  with internet access disabled. Their `Target.lean` files use a minimal
  exam-style surface: source-derived comments above the benchmark marker are
  stripped, except for the harbor canary.
- `tasks-v2/`: 2,558 non-gold tasks without bundled oracles. These run with
  internet access enabled so agents can use external literature while trying to
  produce new Lean proofs. These keep the richer source context generated from
  Formal Conjectures.

The checked-in task roots contain 2,632 task instances: 74 gold instances are
emitted under `tasks/`, and the remaining 2,558 non-gold instances are emitted
under `tasks-v2/`. The GDM-derived v2 candidate manifest records 2,630 task
instances; the additional Erdős 330 upper-density and Erdős 1151 non-empty
fixed-point gold tasks are benchmark-local.

## Benchmark Card

| Field | Value |
| --- | --- |
| Current task instances | 2,632 |
| Gold task root | `tasks/` |
| Gold tasks | 74 |
| Non-gold v2 task root | `tasks-v2/` |
| Non-gold v2 tasks | 2,558 |
| V2 batch manifests | `manifest/v2_batches/batch-001.json` through `batch-027.json` |
| Language | Lean 4 |
| Lean toolchain | `leanprover/lean4:v4.27.0` |
| Mathlib | `v4.27.0`, commit `a3a10db0e9d66acbebf76c5e6a135066525ac900` |
| Formal Conjectures commit | `233a10e857ef78e79fd9fe661d37db724089170a` |
| Verifier policy | Hidden golden project, theorem-header lock, banned escape hatches, axiom audit, and `sorry` canary |

## Task Buckets

| Bucket | Count | Task root | Internet | Oracle |
| --- | ---: | --- | --- | --- |
| `gold_solution` | 74 | `tasks/` | Off | Bundled local oracle |
| `informal_proof` | 722 | `tasks-v2/` | On | None |
| `deferred_formal_candidate` | 26 | `tasks-v2/` | On | None |
| `open_problem` | 1,810 | `tasks-v2/` | On | None |

The `open_problem` bucket consists of 905 prove/refute pairs. Of these, 348 are
ordinary theorem/negation pairs and 557 are simple yes/no `answer(sorry)` iff
pairs reformulated as theorem/negation pairs. Each pair has one task asking for
the proposition and one task asking for the formal negation of the frozen
proposition. Pair metadata lives in `manifest/v2_open_pairs.json`;
benchmark-level scoring should count a pair as passed if at least one side
passes and should flag any pair where both sides pass.

The `deferred_formal_candidate` bucket contains the old deferred candidates from
the gold-task repair pass. For v2 benchmark purposes they are treated as
non-gold, internet-enabled tasks with no bundled oracle.

Remaining `answer(sorry)` declarations are excluded when they require a
non-boolean value/classification answer, or when they are solved yes/no answer
forms that are not part of the open prove/refute scoring model.

## Repository Layout

- `manifest/manifest.json` is the source of truth for the 74 gold tasks emitted
  under `tasks/`.
- `manifest/v2_candidates.json` records the 2,630 GDM-derived v2 instances and
  their benchmark buckets.
- `manifest/v2_batches/` records deterministic batches used to generate
  `tasks-v2/`.
- `manifest/v2_open_pairs.json` records open-problem prove/refute pair
  metadata.
- `oracles/<instance_id>/` stores bundled canonical Lean oracle files for gold
  tasks.
- `generators/generate_tasks.py` renders Harbor task directories from the
  manifests, templates, and oracle files.
- `tasks/<instance_id>/` and `tasks-v2/<instance_id>/` contain generated Harbor
  tasks. Treat these as build artifacts and do not hand-edit them.
- `docs/benchmark-card.md` records the original v1.0.0 release card. This
  README describes the current `main` branch after the v2 expansion.
- `docs/remaining-failures-matrix.md` records the old deferred-candidate repair
  notes from the v1 gold-task pass.

## Checking

The gold-task checks are:

```bash
make check
```

This validates that:

- `manifest/manifest.json` is valid JSON;
- every included gold task has bundled local oracle files;
- bundled oracle metadata records redistribution as local/bundled;
- generated `solution/` files match `oracles/`;
- generated task metadata records the pinned Lean/FormalConjectures/Mathlib
  versions; and
- checked-in gold tasks match the generator output.

To check one v2 batch:

```bash
make check-v2-batch V2_BATCH=batch-027
```

To smoke-test a small Lean sample from one v2 batch:

```bash
make smoke-v2-batch V2_BATCH=batch-027 V2_LEAN_SMOKE=10
```

To Lean-smoke every generated v2 target with its placeholder `sorry`:

```bash
python3 scripts/smoke_v2_targets.py --batch manifest/v2_batches/batch-001.json --batch manifest/v2_batches/batch-002.json --batch manifest/v2_batches/batch-003.json --batch manifest/v2_batches/batch-004.json --batch manifest/v2_batches/batch-005.json --batch manifest/v2_batches/batch-006.json --batch manifest/v2_batches/batch-007.json --batch manifest/v2_batches/batch-008.json --batch manifest/v2_batches/batch-009.json --batch manifest/v2_batches/batch-010.json --batch manifest/v2_batches/batch-011.json --batch manifest/v2_batches/batch-012.json --batch manifest/v2_batches/batch-013.json --batch manifest/v2_batches/batch-014.json --batch manifest/v2_batches/batch-015.json --batch manifest/v2_batches/batch-016.json --batch manifest/v2_batches/batch-017.json --batch manifest/v2_batches/batch-018.json --batch manifest/v2_batches/batch-019.json --batch manifest/v2_batches/batch-020.json --batch manifest/v2_batches/batch-021.json --batch manifest/v2_batches/batch-022.json --batch manifest/v2_batches/batch-023.json --batch manifest/v2_batches/batch-024.json --batch manifest/v2_batches/batch-025.json --batch manifest/v2_batches/batch-026.json --batch manifest/v2_batches/batch-027.json --progress-every 10
```

To check every v2 batch:

```bash
for batch in manifest/v2_batches/batch-*.json; do
  make check-v2-batch V2_BATCH="$(basename "$batch" .json)"
done
```

## Regenerating Tasks

Clone the pinned Formal Conjectures dependency if it is not already present:

```bash
mkdir -p .cache
git clone https://github.com/google-deepmind/formal-conjectures.git .cache/formal-conjectures
git -C .cache/formal-conjectures checkout 233a10e857ef78e79fd9fe661d37db724089170a
```

Regenerate the gold task set:

```bash
make generate
```

Regenerate the v2 candidate manifest and batch manifests:

```bash
make v2-candidates V2_BATCH_SIZE=100
```

Regenerate a v2 batch:

```bash
make generate-v2-batch V2_BATCH=batch-027
```

For exploratory work on a gold candidate, pass `--include-candidates --only
<instance_id>` through the pilot Make targets:

```bash
make generate-pilot ONLY=<instance_id>
make check-pilot-generated ONLY=<instance_id>
```

Pilot-generated artifacts are not part of the tracked benchmark unless the
manifest entry is promoted and the generated task directory is committed.

## Running With Harbor

Run the public gold release through the Harbor registry:

```bash
uv tool install harbor

harbor run \
  --dataset formal-conjectures-gold@1.1.0 \
  --registry-url https://raw.githubusercontent.com/AllenGrahamHart/FormalConjectures-Bench/v1.1.0/registry.json
```

Run one task from the registry:

```bash
harbor run \
  --dataset formal-conjectures-gold@1.1.0 \
  --registry-url https://raw.githubusercontent.com/AllenGrahamHart/FormalConjectures-Bench/v1.1.0/registry.json \
  --task-name erdosproblems-399-erdos-399
```

The checked-in `registry.json` is a Harbor registry for
`formal-conjectures-gold@1.1.0`; its task entries pin the executable gold task
tree to commit `a3674901510f2f8d8a8c1de0c28c568fcd48828e`.

Run the offline gold bucket:

```bash
harbor run -p tasks
```

Run the internet-enabled non-gold v2 buckets:

```bash
harbor run -p tasks-v2
```

Use Harbor's usual agent/model flags to choose the solver. Bucket information is
recorded in each task's `task.toml` under `metadata.benchmark_bucket`.

Gold tasks use generous release timeouts by default: 24 hours for agent
execution, 2 hours for verification, and 4 hours for environment builds. Use
Harbor's timeout multiplier to scale these down or up for a local run:

```bash
harbor run -p tasks --timeout-multiplier 0.25
```

## Verification Model

Each generated task verifier checks that:

- the frozen prefix and theorem header are unchanged;
- the submitted proof is rebuilt in a fresh hidden golden project;
- the editable Lean subtree does not contain banned escape hatches;
- `lake build` succeeds in the pinned Lean environment;
- `#print axioms` for the target theorem contains only allowed axioms; and
- a local `sorry` canary is detected by the axiom-audit path.

Gold tasks set `environment.allow_internet = false`. Non-gold v2 tasks set
`environment.allow_internet = true`. Docker image builds may fetch pinned
dependencies in both cases.

## Release Notes

The original v1.0.0 line was a conservative gold-only release. The current
`main` branch keeps that gold bucket and adds the v2 non-gold benchmark task set
for internet-enabled formalization attempts.

See [docs/reproducibility.md](docs/reproducibility.md) for the archival
hardening plan that should be completed before a paper-grade immutable release.
