# Scheduled upstream sync 8bd69aede -> 34248f3e4 (2026-10-24T05:09:43Z)

## Reason

Routine sync with slopmaster2 (844 commits; ~/cc1/upsync-quick.py). A three-way merge (the owner, 2026-10-23): our changes of upstream files stay, upstream's changes come in; what still differs from upstream is sent upstream by the PR agent.

## Old

upstream base 8bd69aede181d65fe0934e5c23e246bd06b68b42

## New

upstream base 34248f3e401c51555e3b709c59e69bd6aa88b6fc; merge conflict 1, deleted-here 4, merged 4, resolved 3, same 1, source-proof 3, take 523

Conflicts resolved by merge agents (tools/upstream_merge_agent.py; full records in /home/ubuntu/upstream-sync/quick/20261024T130121/merge-agents/tasks/):

### `WeilConjectures/AlgebraicGeometry/ClosedPointResidueField.lean`

# ClosedPointResidueField merge record
- Conflict (added-by-both, whole file; base empty): ours had one lemma `Scheme.isAlgClosed_residueField_of_isClosed`; upstream (34248f3e4) added the full file (header, docstring, extra import `WeilConjectures.FieldTheory.SepClosedFiniteExtension`, and lemmas `Hom.isClosed_singleton_iff_finite_residueField`, `Hom.essFiniteType_residueFieldAlgebraMap`, `Module.Finite.of_essFiniteType_of_isAlgebraic`, `Hom.isClosed_singleton_iff_isAlgebraic_residueField`, `Hom.residueField_of_isClosed_of_isSepClosed`).
- Resolution: upstream's text taken verbatim; our lemma (not present upstream under any name) appended unchanged in its own `namespace AlgebraicGeometry` block after `end AlgebraicGeometry.Scheme`, so it keeps its full name and its own `k`/`X` binders.
- Imports: upstream's (superset of ours). No statement changed, nothing dropped. Compiles (exit 0), no sorry.

### `WeilConjectures/CategoryTheory/ModuleObjects/GrothendieckAbelian.lean`

- One conflict (kind "other"): both sides added the same `open MonObj in section` block (relativeTensorπ, relativeTensorCofork, isColimitRelativeTensorCofork, freeTensorSplit, freeTensorCoforkIsColimit, freeTensorUnderlyingIso, tensorπ_freeTensorUnderlyingIso_hom, freeTensorForgetIso, flat_free) where base had nothing.
- The two hunks are identical except for blank lines: upstream commit 9f4b6c4c87 is our proof that was sent upstream.
- Resolved with upstream's text (source). The whole file now equals upstream's tip 34248f3e4, including the module docstring ("## Proofs" section, which replaces our stale "## Sorried input" text).
- Nothing adapted, nothing dropped. Compiles (exit 0).

### `WeilConjectures/SixFunctors/ProEtale/ModuleObject/BaseChangeTheorems/LowerShriek/CompactificationIndependence.lean`

# Merge record: LowerShriek/CompactificationIndependence
- Both sides independently proved the three former `sorry`s (restriction comparison, E- and Q̄_ℓ-pushforward comparisons) with essentially identical proofs; upstream's versions are taken.
- Conflict 1 (helper lemmas): ours `openUnitIsIso`, `linearCounitOfAbelian`, `moduleCounitOfLinear`, `cartesianModuleCounit`, `cartesianDerivedCounit`, `boundedCartesianCounit` are the same lemmas as upstream's documented `isIso_*` helpers (upstream uses `inferInstance` instead of `openUnitIsIso`); took upstream's, dropped ours as duplicates.
- Conflict 2 (`isIso_boundedConstructibleOpenImmersionLowerShriekRefinement`): both proved; took upstream's proof.
- Conflict 3 (`refinementPushforwardIsIsoOfExchange` vs upstream's `isIso_refinementPushforward_of_isIso_lowerStarOpenImmersionLowerShriekExchange`): same proof, took upstream's name/text.
- Conflicts 4-5 (the two pushforward isIso theorems): both proved; took upstream's (calls upstream's helper).
- Non-conflict hunk: removed our section variable `[IsFinitenessCoefficient ℓ Λ]` in `section Refinement`, matching upstream commit d36322652 (it would have added a hypothesis to upstream statements).
- Kept our two `set_option linter.*` lines (harmless). Result equals upstream's tip plus those two lines; compiles (exit 0).

Dropped of ours: `openUnitIsIso`: private helper made redundant: upstream's proof uses inferInstance; `linearCounitOfAbelian`: duplicate of upstream's isIso_linearOpenImmersionLowerShriekAdjunction_counit_app_of_isIso; `moduleCounitOfLinear`: duplicate of upstream's isIso_openImmersionLowerShriekUpperStarAdjunction_counit_app_of_isIso; `cartesianModuleCounit`: duplicate of upstream's isIso_counit_app_upperStar_obj_openImmersionLowerShriek; `cartesianDerivedCounit`: duplicate of upstream's isIso_derivedCounit_app_upperStar_obj_openImmersionLowerShriek; `boundedCartesianCounit`: duplicate of upstream's isIso_boundedConstructibleCounit_app_upperStar_obj_openImmersionLowerShriek; `refinementPushforwardIsIsoOfExchange`: duplicate of upstream's isIso_refinementPushforward_of_isIso_lowerStarOpenImmersionLowerShri

Conflicts not resolved by an agent:

- `WeilConjectures/SixFunctors/Etale/Derived/ProjectionFormula/Integral.lean`: the tip's file, ours to coord/preferred-upstream (does not compile (exit 1): t 1 (17.9 s)
/home/ubuntu/cc1/rset-tmp/c-vbx9xhw5/lean/WeilConjectures/SixFunctors/Etale/Derived/ProjectionFormula/Integral.lean:6:0: error: object file '/home/ubuntu/weil-c)

Still quarantined, upstream's change merged into the quarantined copy:

- `WeilConjectures.TraceFormula.Correspondence`: merged
- `WeilConjectures.TraceFormula.Main`: merged
- `WeilConjectures.TraceFormula.Statement`: merged
- `WeilConjectures.TraceFormula.WeilTrace`: merged

## Users

538 Lean file(s) changed by the merge and the canonical migration; 1085 node record(s) re-pointed by the migration.

## Status

landed
