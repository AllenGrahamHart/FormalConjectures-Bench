FORMAL_CONJECTURES_DIR ?= .cache/formal-conjectures
MANIFEST ?= manifest/manifest.json
TASKS_DIR ?= tasks

.PHONY: upstream manifest generate-pilot generate check-manifest

upstream:
	mkdir -p .cache
	test -d "$(FORMAL_CONJECTURES_DIR)/.git" || git clone https://github.com/google-deepmind/formal-conjectures.git "$(FORMAL_CONJECTURES_DIR)"
	git -C "$(FORMAL_CONJECTURES_DIR)" fetch --tags --prune

manifest:
	python3 manifest/build_manifest.py --source "$(FORMAL_CONJECTURES_DIR)" --out "$(MANIFEST)" --pinned-out manifest/pinned_versions.toml

generate:
	python3 generators/generate_tasks.py --manifest "$(MANIFEST)" --formal-conjectures-source "$(FORMAL_CONJECTURES_DIR)" --tasks-dir "$(TASKS_DIR)"

generate-pilot:
	python3 generators/generate_tasks.py --manifest "$(MANIFEST)" --formal-conjectures-source "$(FORMAL_CONJECTURES_DIR)" --tasks-dir "$(TASKS_DIR)" --include-candidates --only "$(ONLY)"

check-manifest:
	python3 -m json.tool "$(MANIFEST)" >/dev/null
