# Task Generation

`generate_tasks.py` renders Harbor task directories from reviewed manifest
entries. Generated tasks should not be hand-edited; change the manifest,
templates, or oracle inputs and regenerate instead.

By default the generator only emits entries with
`"inclusion_status": "included"`. Use `--include-candidates` for local pilot
work before licence/oracle review.
