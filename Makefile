FORMAL_CONJECTURES_DIR ?= .cache/formal-conjectures
MANIFEST ?= manifest/manifest.json
TASKS_DIR ?= tasks
BASE_IMAGE_TAG ?= formal-conjectures-bench-base:v4.27.0-fc233a10e

.PHONY: upstream manifest base-image generate-pilot generate check-manifest

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

generate-pilot:
	python3 generators/generate_tasks.py --manifest "$(MANIFEST)" --formal-conjectures-source "$(FORMAL_CONJECTURES_DIR)" --tasks-dir "$(TASKS_DIR)" --include-candidates --only "$(ONLY)"

check-manifest:
	python3 -m json.tool "$(MANIFEST)" >/dev/null
