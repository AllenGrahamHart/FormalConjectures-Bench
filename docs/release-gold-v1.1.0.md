# Gold Release v1.1.0

FormalConjectures-Bench Gold v1.1.0 packages the 74 offline gold-solution tasks
as a Harbor registry dataset.

## Artifacts

- `registry.json`: Harbor registry entry for `formal-conjectures-gold@1.1.0`.
- `huggingface/formal-conjectures-gold/README.md`: Hugging Face dataset card.
- `huggingface/formal-conjectures-gold/tasks.jsonl`: one metadata row per gold
  task.
- `dataset.toml`: small release metadata mirror.

The registry task entries pin the executable task tree to commit
`a3674901510f2f8d8a8c1de0c28c568fcd48828e`.

## Regenerating

```bash
make release-artifacts
```

This regenerates `registry.json` and
`huggingface/formal-conjectures-gold/tasks.jsonl`.

## Validation

```bash
make check
harbor datasets list --registry-path registry.json
```

Optionally smoke-test one task through the registry:

```bash
harbor run \
  --dataset formal-conjectures-gold@1.1.0 \
  --registry-path registry.json \
  --task-name erdosproblems-399-erdos-399 \
  --agent oracle
```

## Publishing

1. Commit and push release artifacts.
2. Tag the release commit as `v1.1.0`.
3. Confirm the raw registry URL works:

   ```bash
   harbor datasets list \
     --registry-url https://raw.githubusercontent.com/AllenGrahamHart/FormalConjectures-Bench/v1.1.0/registry.json
   ```

4. Upload `huggingface/formal-conjectures-gold/` to the Hugging Face dataset
   repository.
