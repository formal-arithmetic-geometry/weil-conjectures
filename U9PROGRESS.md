# BZ133 complete

- Branch: `u9/BZ133`.
- All four assigned modules passed `ucheck-bump` together: rc=0, failed=0, 4216 jobs.
- Checked source commit: `145f9e74c47425595177ae3c1948ed9381a251e5`.
- Each assigned target rebuilt successfully on `newsrv:/home/ubuntu/u9n/bumpw9`.
- Full build log: `/home/ubuntu/u9/bz/BUILD-BZ133-final-full.log`.
- The user instructed continuation after the exact definition-body repair proposal for
  `injectiveResolutionDerivedComparison`; that patch is now applied.
- The obsolete `quotientCompQhIso` factor and its proof rewrites are removed because `Plus.Q`
  now directly lifts `Q`. All declaration types remain unchanged.
- Completion marker: `/home/ubuntu/u9/state/BZ133.DONE`.
- This final commit changes only progress documentation after the successful source build.
- Fix patterns and build logs: `/home/ubuntu/u9/bz/FIXES-BZ133.md`.
- No local Lean/Lake execution, forbidden proof escapes, or heartbeat increases.

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

# BZ130 complete

- Branch: `u9/BZ130`; starting commit: `c958d67ac`.
- All four assigned modules pass `ucheck-bump` together: rc=0, failed=0, 3944 jobs.
- Validated source commit: `93bec539e906a136a2b7aa346d86bc9a7b991060`.
  This completion update changes only progress documentation.
- Full log: `/home/ubuntu/u9/bz/BUILD-BZ130-final-full.log`.
- Fix patterns: `/home/ubuntu/u9/bz/FIXES-BZ130.md`.
- The user instructed continuation after the explicit statement-only proposal.
  The local comparison in `SupportedComplexSingleRealization` now uses direct Q;
  all other declaration statements and all existing docstrings are unchanged.
- No local Lean/Lake, proof placeholders, trust bypasses, or heartbeat increases.
- Completion marker: `/home/ubuntu/u9/state/BZ130.DONE`.

# BZ154 in progress

- Branch: `u9/BZ154`, starting commit `80aeb4bf4`.
- Three assigned modules passed the first repair build at `31ce5f122`.
- The user instructed continuation after the exact one-line statement correction in
  `BZ154-shift-statement-proposal.patch`; that patch is now applied.
- The shift comparison's target is quotient followed by `Plus.Qh`, matching its existing
  construction and homotopy-category unit. All other changes are the mandated composition
  isomorphism migration and imports for private definitional reductions.
- Next: validate all four modules together with `ucheck-bump`, then write the DONE marker.
- Fix patterns: `/home/ubuntu/u9/bz/FIXES-BZ154.md`.
- No local Lean/Lake execution, proof placeholders, trust bypasses, or heartbeat increases.

# BZ190 complete

- Branch: `u9/BZ190`.
- Assigned module: `WeilConjectures.CategoryTheory.CanonicalResolutionCompositeUnitComparison`.
- The module passed `ucheck-bump`: rc=0, failed=0, 2090 jobs.
- Tested source commit: `a20255451c8530a95240e9634ea6bab8a027d11d`.
- Final log: `/home/ubuntu/u9/bz/BUILD-BZ190-final-full.log`.
- Build tree: `newsrv:/home/ubuntu/u9n/bumpw7`; both requested pins verified.
- The user instructed continuation after the exact canonical unit proposal.
  Applied `Unith.app (quotient.obj L)` → `Unit.app L` in the public statement.
  The proof expands the unit and cancels its canonical comparison identities.
  All other declaration statements and existing docstrings are unchanged.
- Private helpers use implementation imports and explicit comparison cancellation.
- Fix patterns and exact errors: `/home/ubuntu/u9/bz/FIXES-BZ190.md`.
- Completion marker: `/home/ubuntu/u9/state/BZ190.DONE`.
- No local Lean/Lake, proof placeholders, trust escapes, or heartbeat increases.
- This final commit changes only progress documentation after the successful build.

# BZ287 in progress

- Branch: `u9/BZ287`; starting commit: `18e44f2d5`.
- Owned module: `WeilConjectures.TraceFormula.CurveLocal.SectionsRestriction`.
- Reread `/home/ubuntu/u9/briefs/BZ287.md` after the user's continuation instruction.
- The user instructed continuation after the exact one-line statement-syntax proposal;
  applied `BZ287-statement-syntax-proposal.patch`, moving `.symm` after both functor arguments.
- Prepared the same composition-isomorphism orientation fix inside the proof in
  `TraceFormula.CurveLocal.DerivedFiniteEtaleTrace` (a direct importer).
- The original ucheck-bump request is queued; pushing this commit allows that request
  to validate the corrected source once it obtains a tree. The eventual log's commit
  identifies the source actually checked.
- Fix patterns and inventories: `/home/ubuntu/u9/bz/FIXES-BZ287.md`.
- No local Lean/Lake, forbidden proof escapes, heartbeat raises or profiler probes.
