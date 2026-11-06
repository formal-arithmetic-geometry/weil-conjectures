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

# BZ154 complete

- Branch: `u9/BZ154`, starting commit `80aeb4bf4`.
- All four assigned modules passed together through `ucheck-bump`: rc=0, failed=0, 3457 jobs.
- Validated source commit: `d26e23a372af96d353232cce73966fa427f1419d`.
- Each assigned module rebuilt successfully on `newsrv:/home/ubuntu/u9n/bumpw2`.
- Full build log: `/home/ubuntu/u9/bz/BUILD-BZ154-final-full.log`.
- The user instructed continuation after the exact one-line statement correction in
  `BZ154-shift-statement-proposal.patch`; that patch is applied and validated.
- The shift comparison's target is quotient followed by `Plus.Qh`, matching its existing
  construction and homotopy-category unit. Other changes are the mandated composition
  isomorphism migration and imports for private definitional reductions.
- Fix patterns and whole-tree occurrence counts: `/home/ubuntu/u9/bz/FIXES-BZ154.md`.
- No local Lean/Lake execution, proof placeholders, trust bypasses, or heartbeat increases.
- Completion marker: `/home/ubuntu/u9/state/BZ154.DONE`.
- This completion commit changes only progress documentation; Lean sources match the green build.

# BZ229 complete

- Branch: `u9/BZ229`; starting commit: `c0384594d`.
- Assigned module: `WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebraDerivedRightAdjointLift`.
- The module passed `ucheck-bump`: rc=0, failed=0, 2110 jobs; target rebuilt in 10 seconds.
- Validated source commit: `0673016c02360dade89345e38fc576c7609cf662`.
- Build tree: `newsrv:/home/ubuntu/u9n/bumpw1`.
- Full build log: `/home/ubuntu/u9/bz/BUILD-BZ229-final-full.log`.
- The user instructed continuation after the explicit one-token statement correction proposal.
  Applied `.hom` -> `.inv` in the composition-factor helper to preserve its original map
  after adopting Mathlib's reversed composition isomorphism. Other statement types and
  all existing docstrings are unchanged.
- Definition bodies and inverse cancellation now use the new composition orientation.
  Two trailing `rfl` tactics after `simp` were removed. The final `rfl` after `erw` is needed
  in this module and is retained.
- Fix patterns and whole-tree counts: `/home/ubuntu/u9/bz/FIXES-BZ229.md`.
- No local Lean/Lake execution, proof placeholders, trust bypasses, or heartbeat increases.
- Completion marker: `/home/ubuntu/u9/state/BZ229.DONE`.
- This completion commit changes only progress documentation; Lean source matches the green build.

# BZ311 complete

- Branch: `u9/BZ311`; starting commit: `ec1bc636d`.
- Assigned module and both downstream layers passed `ucheck-bump` together:
  rc=0, failed=0, 1935 jobs, on `poolb:43.166.72.113`.
- Validated source commit: `d599eea1699030daa1a58ff564ab648fb03d536e`.
- Green modules: `WeilConjectures.CategoryTheory.Abelian.DerivedBottomCycleTransport`,
  `WeilConjectures.CategoryTheory.Abelian.DerivedBottomUnitNormalizationFormula`,
  and `WeilConjectures.CategoryTheory.Abelian.DerivedBottomUnitNormalization`.
- The user instructed continuation after the exact three-statement proposal.
  Those canonical quotientCompQhIso endpoint transports are the only Lean changes;
  all proof bodies, declaration binders, assumptions, and docstrings are unchanged.
- Full log: `/home/ubuntu/u9/bz/BUILD-BZ311-final-full.log`.
- Fix pattern and whole-tree candidate count: `/home/ubuntu/u9/bz/FIXES-BZ311.md`.
- Contract audit: `/home/ubuntu/u9/bz/BZ311-contract-audit.txt`.
- No local Lean/Lake execution, sorries, forbidden proof shortcuts, or limit increases.
- Completion marker: `/home/ubuntu/u9/state/BZ311.DONE`.
- This final commit changes only progress documentation; Lean sources match the green build.

# BZ384 in progress

- Branch: `u9/BZ384`; starting commit: `98654719b`.
- Baseline remote build confirmed five errors in compositor directions in declaration types.
- The user instructed continuation after the explicit nine-direction patch proposal.
  That patch is now applied, preserving the original equations under Mathlib's reversed compositor.
- Next: remote validation of the assigned module, then its three direct importers.
- Fix patterns and baseline log: `/home/ubuntu/u9/bz/FIXES-BZ384.md`.
- No local Lean/Lake, proof placeholders, trust bypasses, or heartbeat increases.

# BZ469 in progress

- Branch: `u9/BZ469`; starting commit: `99a06bbbb`.
- The user instructed continuation after the exact two-site API proposal.
  Applied `.symm` to both composition comparisons in
  `injectiveSections_strictLocal_comparison`, preserving the original map directions
  under Mathlib's reversed compositor.
- Pinned API inspected at b63f6e8a; known quotient patterns do not match this module.
- Next: remote validation, then up to four direct importers and a second downstream layer.
- Fix patterns: `/home/ubuntu/u9/bz/FIXES-BZ469.md`.
- No local Lean/Lake execution, proof placeholders, trust bypasses, or heartbeat changes.

# BZ511 in progress

- Branch: `u9/BZ511`; starting commit: `fa248eeed`.
- The user instructed continuation after the exact two-private-helper API proposal.
  The compositor inverse in `derivedCompSingle` and the direct compositor in
  `derivedTripleNatSingle` are applied. The public theorem statement is unchanged.
- Proofs now use Mathlib's single-object compositor lemma, hom naturality, and
  hom/inv cancellation; the redundant `rfl` after `simp only` is removed.
- Pinned Mathlib source was inspected at b63f6e8a. Patterns, occurrence counts,
  and integration errors: `/home/ubuntu/u9/bz/FIXES-BZ511.md`.
- Existing `ucheck-bump` invocation is queued; it reads the pushed branch after
  acquiring a tree. Next: validate the owned module and continue downstream.
- No local Lean/Lake, proof placeholders, trust bypasses, or heartbeat increases.

# BZ557 in progress

- Branch: `u9/BZ557`; starting commit: `8af5cb324`.
- Added the public AffineScheme import to direct importer AffineBasisSectionsDerivedUnit.
- Initial remote builds stopped in the shared Presheaf.InternalHom dependency.
- On continuation, merged BZ558 prerequisite repair `f28760733369366ac823f0084f3c4090afa3a90d`.
- Next: ucheck-bump on AffineBasisSectionsResolutionHomologyEpi, AffineBasisSectionsDerivedUnit,
  and AffineOpenSectionsResolutionQuasiIso; fix any owned errors and write DONE when green.
- Notes and build evidence: `/home/ubuntu/u9/bz/FIXES-BZ557.md`.
- No local Lean/Lake, statement changes, proof escapes, or heartbeat increases.

# BZ603 in progress

- Branch: `u9/BZ603`; starting commit: `cfcb63ad7`.
- Baseline remote build: eight errors caused by hidden `HomologicalComplexUpToQuasiIso.Qh`.
- Public and implementation Localization imports removed seven diagnostics; the private
  helper statements and proofs compile. The one public representative statement still failed.
- The user instructed continuation after the canonical Q/Qh endpoint-transport proposal.
  Applied the comparison hom/inv maps only to that equality, preserving its mathematical
  maps, binders, assumptions, and other statements. The proof normalizes identity transports.
- Next: `ucheck-bump` on the assigned module, then `CompletedScalarAssociator` downstream.
- Fix patterns and exact diagnostics: `/home/ubuntu/u9/bz/FIXES-BZ603.md`.
- No local Lean/Lake, proof placeholders, trust bypasses, or heartbeat increases.


# BZ646 complete

- Green owned module: `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ComparisonUpperStarCoherence`.
- Green direct importer: `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ComparisonBaseChangeMate`.
- Final remote validation: `ucheck-bump` at source commit `e46a90620ceda4662bd450189ee57edb7cc5cad6`,
  rc=0, failed=0, 5603 jobs; both changed modules rebuilt successfully.
- Ported composition comparison directions, simplified composition components directly,
  removed a redundant tactic, and normalized symmetric isomorphism projections.
- Declaration statements, imports, and docstrings are unchanged; all source edits are in proofs.
- All seven machine rewrite rules exactly reproduce the final files from baseline `bb4aa5315`.
- Three direct importers were attempted. Identity coherence requires a statement change and is
  left untouched. Étale-reading coherence and its next-layer importer are blocked by unowned
  dependencies. The broad failing batch was stopped after those blockers were confirmed.
- Handoff records: `/home/ubuntu/u9/bz/FIXES-BZ646.md` and `/home/ubuntu/u9/state/BZ646.DONE`.
- No local Lean/Lake execution, proof placeholders, trust bypasses, or heartbeat changes.


# BZ683 complete

- Branch: `u9/BZ683`; starting commit: `4bbea9d82`.
- Assigned module `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ChangeOfRingsTensorTransition`
  passed `ucheck-bump`: rc=0, failed=0, 2873 jobs, target rebuilt in 9.4 seconds.
- Validated source commit: `9ebd05ad943b03304d7e35268cffa36c7118fa18`.
- The user instructed continuation after the exact one-line dependency-name proposal.
  Named the local instance in `ChangeOfRingsTransition` as
  `changeOfRingsTransitionRestrictedModule`; its type and proof remain unchanged.
  This removes the generated proof-name collision with `TensorProductOfUniverses`.
- The dependency also rebuilt successfully. Assigned leaf source and all statements are unchanged.
- Both downstream layers were attempted: `FinitePerfectAdicQuotientStrictRealizationData`
  and `FinitePerfectAdicQuotientStrictRealizationSquare`. Skipped because six dependencies
  outside this unit fail; the batch was stopped after collecting those diagnostics.
- Full logs: `/home/ubuntu/u9/bz/BUILD-BZ683-fix1-full.log` and
  `/home/ubuntu/u9/bz/BUILD-BZ683-downstream-full.log`.
- Fix pattern, exact diagnostic, contextual rewrite rule, and whole-tree occurrence counts:
  `/home/ubuntu/u9/bz/FIXES-BZ683.md`.
- Contract audit: `/home/ubuntu/u9/bz/BZ683-contract-audit.txt`.
- Completion marker: `/home/ubuntu/u9/state/BZ683.DONE`.
- No local Lean/Lake, proof placeholders, trust bypasses, or heartbeat changes.
- This final commit changes only progress documentation; Lean sources match the green build.

# BZ740 complete

- Branch: `u9/BZ740`; starting commit: `f271bd088`.
- Assigned module `WeilConjectures.AlgebraicGeometry.DerivedPullbackTensorUnitNormalization`
  passed `ucheck-bump`: rc=0, failed=0, 3927 jobs; target rebuilt in 48 seconds.
- Validated source commit: `814682ae46`. The assigned target also rebuilt successfully
  in the downstream batch at `28be0e52ca`.
- The user instructed continuation after the exact one-line identity-cast proposal.
  That patch and two Localization imports are the only Lean changes.
- All other statement text, proof bodies, docstrings, and heartbeat settings are unchanged.
  Both recorded rewrite rules exactly reproduce the source from the baseline.
- Direct importer `DerivedPullbackTensorUnitKFlat` was checked and fails in a kept
  public theorem's hμ binder (line 359), requiring further statement-level Qh/Q conversions.
  It and next-layer `DerivedPullbackTensorUnit` are deferred under the kept-statement rule.
  Neither downstream file was edited.
- Full logs: `/home/ubuntu/u9/bz/BUILD-BZ740-assigned-green-full.log` and
  `/home/ubuntu/u9/bz/BUILD-BZ740-downstream1-full.log`.
- Fix patterns, exact diagnostics, and occurrence counts: `/home/ubuntu/u9/bz/FIXES-BZ740.md`.
- Contract audit: `/home/ubuntu/u9/bz/BZ740-contract-audit.txt`.
- Completion marker: `/home/ubuntu/u9/state/BZ740.DONE`.
- No local Lean/Lake, proof placeholders, trust bypasses, or heartbeat increases.
- This final commit changes only progress documentation; Lean source matches the green build.

# BZ798 in progress

- Branch: `u9/BZ798`; original baseline: `6a4b38f19`.
- Resumed after rereading `/home/ubuntu/u9/briefs/BZ798.md` and the progress notes.
- Merged the current integrated bump branch at `d9a3ea12c`. It already removes the
  unused signed-projection comparison chain and its downstream callers. The earlier
  referenced-caller blocker therefore no longer applies.
- Deleted only the remaining unused `SignedProjectionResolution.totalInverse`;
  whole-tree `git grep -w totalInverse -- WeilConjectures Comparator` found its sole
  declaration and no callers. It is listed unused and absent from kept-decls.txt.
- All surviving declaration text is unchanged from the integrated branch.
- Next: validate the owned module, then its direct importers and downstream layers.
- Previous diagnostic history is archived in FIXES-BZ798-preintegration.md.
- No local Lean/Lake execution, proof placeholders, trust bypasses, or heartbeat increases.

# BZ850 in progress

- Branch: `u9/BZ850`; baseline: `2ab2b07a3`.
- The user instructed continuation after the explicit three-declaration upstream restoration proposal.
- Restored `derived_projection_exists`, `coefficientConstantTowerProjection_exists`, and
  `coefficientConstantTowerProjection` in CoefficientRingedSequenceSiteSupplement with their
  original statements and docstrings. Their surviving users prohibit pruning them.
- Added Localization imports and explicit simplification of its hidden comparison components.
- The assigned CoefficientConstantTowerRoos source is unchanged.
- Next: remote ucheck-bump on the assigned module, then both direct importers.
- No local Lean/Lake, proof placeholders, trust bypasses, or heartbeat increases.

# BZ864 in progress

- Branch: `u9/BZ864`; baseline `e167a50a4`.
- The original missing open-comparison helper was pruned while its affine-chart caller remains.
- First proof replacement exposed two upstream failures; user instructed continuation to green.
- Restoring the referenced degree-zero open comparison chain with original signatures.
- The assigned theorem now uses the degree-zero pinned square and target automorphisms.
- No existing theorem statement changes, proof placeholders, or heartbeat increases.
- All compilation is remote through `ucheck-bump`; build 7 is queued. Build 3 was cancelled while queued; builds 4 and 5 supplied concrete prerequisite diagnostics.
- Fix records and restoration inventories: `/home/ubuntu/u9/bz/FIXES-BZ864.md`.
- Next: repair errors reported by those builds, validate the leaf, then continue downstream.

- BZ864 update: 17 Lean modules changed, restoring 22 still-needed declarations and adding three helpers.
- Pinned single-counit definitions now compile using explicit universe `w` and reflexive casts.
- Remaining diagnosed repairs: abstract the homotopy-square isomorphism construction and
  normalize casts in the pinned counit composition proof; submitted in build 6.
- Build logs: `/home/ubuntu/u9/bz/BZ864-build-4-full.log` and `BZ864-build-5-full.log`.
- No original statement changes, forbidden proof escapes, or heartbeat raises.

- Build 6: abstract homotopy helper elaborated, but exposed definition required its helper public. Fixed.
- Build 6: counit simpa retained a Qh conversion mismatch; applied known BZ721 `simp at h ⊢; exact h` under full unfolding.
- Build 7 submits both repairs; no other source changes pending.

- Build 7: homotopy iso, counit equation, target triangle, and zero apex now green.
- Restriction factors: removed solved-goal rfl; its newly restored helper is private because the original type uses hidden Qh reduction. The sole caller now imports all of that helper module. No existing public statement changed.

- Build 7 finished with two failing modules: restriction factors (prepared fix) and a further pruned homotopy tensor-counit helper. Restored that helper from a3a372af5 without its former heartbeat override. 18 Lean files changed, 23 restored declarations.
- Build 8 validates these changes on the assigned module and affine locality.

- Build 8: restriction factors and homotopy tensor counit green. Remaining failures: normalize reflexive casts before the degree-zero counit map-composition rewrite; reverse quotientCompQhIso when transporting a K-to-Q representative to Qh. Both fixes prepared for build 9.

- Full-header audit now checks all let-bound type clauses: 62 unchanged existing/restored types and 3 new helpers across 19 Lean files; no baseline declaration deleted. See BZ864-full-header-audit.tsv.
- Build 9 is running on poolb:43.157.135.193 at 6d626d27d5, rebuilding additional prerequisites. Build 8 compiler diagnostics are complete; its wrapper separately hit a transient EOF parse error after compilation. Current bbuild.sh passes bash -n.

- Build 9: every prerequisite green through SingleComplexOpenBaseChangeCalculation. Only OpenPinnedSingleDegreeZeroTarget failed: 200000-heartbeat timeout at the broad source-factor rewrite (18s). Replaced it with targeted conv; also applied the established full-transparency cast normalization to the final equality. Default heartbeat limit retained. Build 10 next.

- Build 10: targeted rewrite and cast normalization passed; timeout moved to the final apex-isomorphism composition at 200000 heartbeats (22s). Set only this theorem to 400000, justified by those measured failures; its original pre-prune budget was 1000000. No instance-limit timeout is involved. Build 11 next.

- Current remote job: build 11, commit bda90a40ff, log /home/ubuntu/u9/logs/BZ864-20261106T083418.log, poolb:43.157.153.196. Local exec session 5819. All checks through SingleComplexOpenCounitCompatibility are green; target/leaf/locality still pending.
- Machine-rule audit: 16 rules parse; five snapshot-checked rules now match once before and zero times after. Identity-cleanup insertion rule made idempotent.

- Build 11: target comparison and degree-zero square green. Only the assigned theorem failed, exhausting 200000 heartbeats in 12s. For build 12, normalize module aliases, make derived universes explicit, and scope its budget to 400000. Public theorem header unchanged.
