# Verifier Hardening

The verifier design follows the same pattern as the local Takens TB3 task:

- Treat the public task checkout as untrusted after the agent runs.
- Keep a hidden pristine Lean project under `tests/golden_env`.
- Copy only the editable Lean subtree into a fresh temporary hidden project.
- Ignore public `lakefile`, `lean-toolchain`, imports, and support files during
  the final build, except to assert they were not modified.
- Check the theorem header and all code above the target marker byte-for-byte.
- Build the hidden project, then audit `#print axioms`.
- Run a `sorry` canary to confirm the axiom-audit path detects `sorryAx`.
- Reject common escape hatches: `sorry`, `admit`, `axiom`, `unsafe`,
  `native_decide`, `@[implemented_by]`, `@[extern]`, `run_cmd`, `#eval`,
  `initialize`, `builtin_initialize`, and `load_dynlib`.

Generated tasks set `allow_internet = false`; the Docker image build may fetch
pinned dependencies, but the agent and verifier run offline.
