# Verifier Hardening

The verifier design follows the same pattern as the local Takens TB3 task:

- Treat the public task checkout as untrusted after the agent runs.
- Keep a hidden pristine Lean project under `tests/golden_env`.
- Copy only the editable Lean subtree into a fresh temporary hidden project.
- Ignore public `lakefile`, `lean-toolchain`, imports, and support files during
  the final build, except to assert they were not modified.
- Check the theorem header and all code above the target marker byte-for-byte.
- Build the hidden project, then audit `#print axioms`; malformed axiom-audit
  output is treated as a verifier failure.
- Run a `sorry` canary to confirm the axiom-audit path detects `sorryAx`.
- Run a hidden golden wrapper theorem with the original expected signature,
  proved by applying the submitted theorem.
- Provide the agent a read-only verifier-equivalent checker at
  `/app/check.sh`, backed by `/opt/formal-conjectures-bench-checker`, so it can
  iterate before final grading.
- Reject common escape hatches: `sorry`, `admit`, `axiom`, `unsafe`,
  `native_decide`, `@[implemented_by]`, `@[extern]`, `run_cmd`, `#eval`,
  `initialize`, `builtin_initialize`, and `load_dynlib`.
- Reject parser and metaprogramming extensions in editable sources, including
  `macro`, `macro_rules`, `syntax`, `elab`, custom notation declarations, and
  related infix/prefix/postfix/mixfix commands. These are not needed for normal
  Lean proofs and can interfere with verifier audit commands or theorem
  statement elaboration.
- Reject symlinks and non-Lean files in the editable source tree.
- Link verifier dependency packages directly from
  `/opt/formal-conjectures/.lake/packages`, not through mutable `/app` state.
- Treat Lake dependency config files as scratch: the image keeps a root-owned
  backup and the verifier restores it before building, while package source and
  compiled theorem artifacts stay non-writable to the runtime user.

Generated tasks set `allow_internet = false`; the Docker image build may fetch
pinned dependencies, but the agent and verifier run offline.
The runtime user is non-root, `/opt/formal-conjectures` is read-only, and only
`/app/FormalConjecturesBench` plus Lake build cache state are writable.
