FORMAL_CONJECTURES_DIR ?= .cache/formal-conjectures
MANIFEST ?= manifest/manifest.json
TASKS_DIR ?= tasks
V2_MANIFEST ?= manifest/v2_candidates.json
V2_BATCHES_DIR ?= manifest/v2_batches
V2_EXCLUSIONS ?= manifest/v2_exclusions.csv
V2_OPEN_PAIRS ?= manifest/v2_open_pairs.json
V2_BATCH ?= batch-001
V2_TASKS_DIR ?= tasks-v2
V2_BATCH_SIZE ?= 100
V2_LEAN_SMOKE ?= 10
BASE_IMAGE_TAG ?= formal-conjectures-bench-base:v4.27.0-fc233a10e
RELEASE_VERSION ?= 1.4.0
RELEASE_TASK_COMMIT ?= 71449fdfa6f58f7f33887c33ec2c7202f46fb6df
RELEASE_GIT_URL ?= https://github.com/AllenGrahamHart/FormalConjectures-Bench

.PHONY: upstream manifest base-image generate-pilot generate check-generated check-pilot-generated check-manifest check-oracles check release-artifacts v2-candidates generate-v2-batch check-v2-batch smoke-v2-batch

upstream:
	mkdir -p .cache
	test -d "$(FORMAL_CONJECTURES_DIR)/.git" || git clone https://github.com/google-deepmind/formal-conjectures.git "$(FORMAL_CONJECTURES_DIR)"
	git -C "$(FORMAL_CONJECTURES_DIR)" fetch --tags --prune

manifest:
	python3 manifest/build_manifest.py --source "$(FORMAL_CONJECTURES_DIR)" --out "$(MANIFEST)" --pinned-out manifest/pinned_versions.toml

base-image:
	docker build --progress=plain -t "$(BASE_IMAGE_TAG)" docker/formal-conjectures-base

generate:
	python3 generators/generate_tasks.py --manifest "$(MANIFEST)" --formal-conjectures-source "$(FORMAL_CONJECTURES_DIR)" --tasks-dir "$(TASKS_DIR)"

check-generated:
	python3 generators/generate_tasks.py --manifest "$(MANIFEST)" --formal-conjectures-source "$(FORMAL_CONJECTURES_DIR)" --tasks-dir "$(TASKS_DIR)" --check

generate-pilot:
	python3 generators/generate_tasks.py --manifest "$(MANIFEST)" --formal-conjectures-source "$(FORMAL_CONJECTURES_DIR)" --tasks-dir "$(TASKS_DIR)" --include-candidates --only "$(ONLY)"

check-pilot-generated:
	python3 generators/generate_tasks.py --manifest "$(MANIFEST)" --formal-conjectures-source "$(FORMAL_CONJECTURES_DIR)" --tasks-dir "$(TASKS_DIR)" --include-candidates --only "$(ONLY)" --check

check-manifest:
	python3 -m json.tool "$(MANIFEST)" >/dev/null

check-oracles:
	python3 scripts/check_included_oracles.py --manifest "$(MANIFEST)" --oracles-dir oracles --tasks-dir "$(TASKS_DIR)"

check: check-manifest check-oracles check-generated

release-artifacts:
	python3 scripts/generate_release_artifacts.py \
		--version "$(RELEASE_VERSION)" \
		--git-url "$(RELEASE_GIT_URL)" \
		--git-commit-id "$(RELEASE_TASK_COMMIT)"

v2-candidates:
	python3 manifest/build_v2_candidates.py --source "$(FORMAL_CONJECTURES_DIR)" --current-manifest "$(MANIFEST)" --out "$(V2_MANIFEST)" --batches-dir "$(V2_BATCHES_DIR)" --exclusions "$(V2_EXCLUSIONS)" --open-pairs "$(V2_OPEN_PAIRS)" --batch-size "$(V2_BATCH_SIZE)"

generate-v2-batch:
	python3 generators/generate_tasks.py --manifest "$(V2_MANIFEST)" --formal-conjectures-source "$(FORMAL_CONJECTURES_DIR)" --tasks-dir "$(V2_TASKS_DIR)" --oracles-dir oracles --all --id-file "$(V2_BATCHES_DIR)/$(V2_BATCH).json"

check-v2-batch:
	python3 generators/generate_tasks.py --manifest "$(V2_MANIFEST)" --formal-conjectures-source "$(FORMAL_CONJECTURES_DIR)" --tasks-dir "$(V2_TASKS_DIR)" --oracles-dir oracles --all --id-file "$(V2_BATCHES_DIR)/$(V2_BATCH).json" --check
	python3 scripts/check_v2_batch.py --manifest "$(V2_MANIFEST)" --batch "$(V2_BATCHES_DIR)/$(V2_BATCH).json" --tasks-dir "$(V2_TASKS_DIR)"

smoke-v2-batch:
	python3 scripts/check_v2_batch.py --manifest "$(V2_MANIFEST)" --batch "$(V2_BATCHES_DIR)/$(V2_BATCH).json" --tasks-dir "$(V2_TASKS_DIR)" --formal-conjectures-source "$(FORMAL_CONJECTURES_DIR)" --lean-smoke "$(V2_LEAN_SMOKE)"
