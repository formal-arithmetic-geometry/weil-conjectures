# BZ150 complete

- Branch: `u9/BZ150`; starting commit: `80aeb4bf4`.
- All four assigned modules passed together with `ucheck-bump`: rc=0, failed=0, 3644 jobs.
- Validated source commit: `fb9bd7b27d169a5e395ed809947ee52e6fd0b46e`.
- Build tree: `newsrv:/home/ubuntu/u9n/bumpw5`.
- Full log: `/home/ubuntu/u9/bz/BUILD-BZ150-final-full.log`.
- The user instructed continuation after the exact one-line statement migration proposal.
  `rightDerivedPullback_comp` now uses `(mapDerivedCategoryCompIso P P').symm` because
  Mathlib owns the old name with the opposite orientation; the intended map is preserved.
- All remaining declaration statements and existing docstrings are unchanged.
- Completion marker: `/home/ubuntu/u9/state/BZ150.DONE`.
- This completion update changes only progress documentation after the successful source build.
- Fix patterns and logs: `/home/ubuntu/u9/bz/FIXES-BZ150.md`.
- No local Lean/Lake execution, proof placeholders, trust bypasses, or heartbeat increases.

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

# BZ159 complete

- Unit: BZ159; branch: `u9/BZ159`.
- All four assigned modules passed `ucheck-bump` together: rc=0, failed=0, 4255 jobs.
- Validated source commit: `f69c33ffa45cfbe76eeabefd69b81cd9b1b10343`.
  This completion update changes only progress documentation.
- Build host: `newsrv:/home/ubuntu/u9n/bumpw6`.
- Full log: `/home/ubuntu/u9/bz/BUILD-BZ159-final-full.log`.
- Modules: DerivedSingleShiftNormalization, NativeDerivedBaseChange, Inertia,
  CyclicDerivedActionRealization.
- The user instructed continuation after the explicit equivalent statement API proposal;
  the two cyclic-action statement references now use the forward composition isomorphism.
  All other existing statement text and docstrings remain unchanged.
- Fix patterns and whole-tree baseline occurrence counts:
  `/home/ubuntu/u9/bz/FIXES-BZ159.md`.
- No proof placeholders, trust bypasses, local Lean/Lake execution, or heartbeat increases.
- Completion marker: `/home/ubuntu/u9/state/BZ159.DONE`.

# BZ266 in progress

- Branch: `u9/BZ266`; starting commit: `c781553bf`.
- Re-read the brief and progress notes on continuation.
- The user instructed continuation after the explicit compositor compatibility proposal.
  Applied `.inv` → `.hom` in `comparison_comp`, removed `.symm` in `unit_comp`'s `heD`,
  and adjusted the proof cancellation; the original mathematical maps are preserved.
- Replaced the obsolete identity computation with Mathlib's exact single-object lemma.
- Proof-only remote build checked the identity repair; next build checks the compositor patch.
- Patterns and logs: `/home/ubuntu/u9/bz/FIXES-BZ266.md`.
- Only remote `ucheck-bump` builds; no proof placeholders, trust bypasses, or limit raises.
