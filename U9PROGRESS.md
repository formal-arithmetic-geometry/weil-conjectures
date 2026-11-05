# BZ118 in progress

- Branch: `u9/BZ118`.
- Three assigned modules passed the first repair build (commit `ccbe951d0655`).
- `TraceShiftUnit` needed canonical endpoint transport in its public statement because Mathlib marks `Qh` `no_expose`.
- The user instructed continuation after the explicit statement-adjustment proposal; that exact patch is now applied.
- Next: validate all four modules with `ucheck-bump`, then write `/home/ubuntu/u9/state/BZ118.DONE`.
- Fix patterns and build logs: `/home/ubuntu/u9/bz/FIXES-BZ118.md`.
- No local Lean/Lake execution; no forbidden proof escapes or heartbeat increases.

# BZ72 complete

- Unit: BZ72, branch `u9/BZ72`.
- All four assigned modules passed `ucheck-bump` together: rc=0, 3821 jobs.
- Checked source commit: `1ff41157e8e837eefed5af2db7bae1d35eab175d`; this final update changes only progress documentation.
- Full build log: `/home/ubuntu/u9/bz/BUILD-BZ72-final3-full.log`.
- Fix patterns and the coordinate statement's canonical endpoint transports: `/home/ubuntu/u9/bz/FIXES-BZ72.md`.
- The user instructed continuation after the explicit statement-adjustment proposal. All other declaration statements and existing docstrings are unchanged.
- No local Lean/Lake execution, no sorries or trust escapes, no heartbeat increases.
- Completion marker: `/home/ubuntu/u9/state/BZ72.DONE`.
- Outside-unit caller `NativeHomLocalizedConeBoundaryModel.lean:114` still needs its owner's port; details are in the fix log.

# BZ129 complete

- Unit: BZ129, branch `u9/BZ129`.
- All four assigned modules rebuilt successfully together via `ucheck-bump`:
  rc=0, failed=0, 2500 jobs.
- Tested source commit: `e79e593115f97655e43fa2c80278a052e6bd9272`; the final commit changes only progress notes.
- Modules: ModulePullbackPushforwardAdjunction, RingedDerivedRestrictionGeneral,
  HypercohomologyLeftEdge, and MappedSingleCyclesShiftComparison.
- The user instructed continuation after the exact canonical quotient/Qh
  statement-adjustment proposal. That patch and its proof repair are validated;
  all other existing declaration statements and all docstrings are unchanged.
- Full build log: `/home/ubuntu/u9/bz/BUILD-BZ129-final-full.log`.
- Fix patterns, occurrence counts, and pinned API evidence:
  `/home/ubuntu/u9/bz/FIXES-BZ129.md`.
- No local Lean/Lake execution, no sorries or forbidden proof escapes,
  no heartbeat increases; `git diff --check` passes.
- Completion marker: `/home/ubuntu/u9/state/BZ129.DONE`.
