# Task Generation

`generate_tasks.py` renders Harbor task directories from reviewed manifest
entries. Generated tasks should not be hand-edited; change the manifest,
templates, or oracle inputs and regenerate instead.

By default the generator only emits entries with
`"inclusion_status": "included"`. Use `--include-candidates` for local pilot
work before licence/oracle review. For v1.0.0, remaining candidate entries are
marked as deferred and are outside the release unless explicitly generated for
repair work.

Use `--check` to render the selected task set into a temporary directory and
compare it with the checked-in `tasks/` tree. This is intended for CI and local
stale-output checks:

```bash
make check-generated
make check-pilot-generated ONLY=<instance_id>
```
