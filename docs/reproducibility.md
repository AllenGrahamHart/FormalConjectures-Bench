# Reproducibility Plan

This benchmark should be reproducible from local, pinned artifacts. The Lean
statements and oracle proofs for included tasks are committed to this repo; the
remaining risk is the dependency/image layer used to run them.

## Current Invariants

- Included task statements are generated into `tasks/<instance_id>/`.
- Included oracle proofs are committed under `oracles/<instance_id>/`.
- Generated `solution/` files are copies of the matching `oracles/` files.
- The FormalConjectures commit, Lean toolchain, and Mathlib commit are recorded
  in `manifest/pinned_versions.toml` and each generated `task.toml`.
- Generated task metadata sets `allow_internet = false`.
- The verifier uses local files and the baked `/opt/formal-conjectures`
  dependency checkout; it does not fetch external proof URLs.

Run the lightweight guardrail checks with:

```bash
make check-oracles
make check-generated
```

`make check` runs both checks plus JSON manifest validation.

## Current Non-Archival Dependencies

The repository is not yet fully archival from a fresh clone because image builds
still depend on live infrastructure:

- `docker/formal-conjectures-base/Dockerfile` starts from `ubuntu:24.04` by tag,
  not OCI digest.
- The base image installs packages via `apt-get`.
- The base image downloads the elan installer from GitHub.
- The base image clones FormalConjectures from GitHub, then checks out a pinned
  commit.
- `lake exe cache get` depends on remote cache availability.
- Generated task images install small runtime tools via `apt-get`.

These are build-time dependencies, not verifier-time dependencies, but they
should be removed or pinned before a paper-grade release.

## Future Archival Hardening

Before freezing a paper-grade archival release:

1. Publish the base image to an immutable registry location, preferably GHCR.
2. Reference the base image by OCI digest in generated task Dockerfiles.
3. Pin the Ubuntu base image by digest if rebuilding the base image remains part
   of the release process.
4. Move all runtime tools needed by generated tasks into the base image so task
   images can build without `apt-get`.
5. Replace the live elan installer path with a pinned release or a checked
   checksum.
6. Record SHA256 checksums for oracle files, generated task files, and verifier
   templates in a lockfile.
7. Add CI that runs `make check`, validates each included oracle, and confirms
   task validation runs with Docker networking disabled after images are built.
8. Attach a source tarball plus base-image digest, and optionally an OCI image
   archive, to the release.

Do this after the v1.1.0 gold task list and verifier template have had more
external exercise. Until then, keep the lightweight checks strict enough that
included tasks cannot depend on live proof URLs or unbundled oracle files.
