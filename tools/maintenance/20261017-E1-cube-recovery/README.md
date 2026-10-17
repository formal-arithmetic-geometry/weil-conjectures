# E1 cube provider recovery verification

The active launcher lives outside this repository. These files archive the
2026-10-17 maintenance of `Sheaf.Paper.CondensedQbarPullbackCube`:

- `resume-selector.patch`: the one-line deployed repair. An explicit UUID and
  stdin prompt marker are required; `--last` is excluded even beside a UUID.
- `test_resume_selector.py`: extracts the actual selector functions with `ast`;
  it never imports the dispatcher, runs a model, or touches runtime admission state.
- `codex_retry.py`, `codex_admission.py`: snapshots of the concurrently maintained
  launcher supervisor and its import dependency. This maintenance changed only
  the selector guard in the supervisor. Other recovery/admission changes belong
  to the parallel infrastructure repairs, including NK, Q65, Q126 and Q55.
- `test_codex_retry.py`: the existing fake-CLI recovery suite retained for
  reproducible verification; it launches only test children.
- `attempts.json`: paths, hashes and final diagnostics of the E1 runs. The final
  run was still active when captured, so its hash describes that instant only.

From this directory run:

```
python3 -m unittest -v test_resume_selector test_codex_retry
```

To check a later installed supervisor without loading its admission module:

```
CODEX_RETRY_SOURCE=/home/ubuntu/weil-launcher-all/codex_retry.py python3 test_resume_selector.py -v
```

The local evidence directory also retains five tests of the shared provider
admission and actual maintenance-launch path. All 23 checks passed locally.
The two original selector failures and final passing output are retained in the
maintenance workspace. The item handoff is in
`tools/launcher/route-notes/Sheaf.Paper.CondensedQbarPullbackCube.md` and
`coord/maintenance/E1-condensed-qbar-pullback-cube-20261017.md`.

The existing dispatcher need not be killed: its future process executions read
the deployed CLI wrapper and route note. Source-only dispatcher changes from
other maintenance sessions become active on its next ordinary start. Preserve
later fixes if redeploying; these are audit snapshots, not a blanket rollback.
