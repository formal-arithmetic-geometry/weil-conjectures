# Derived/Monoidal: upstream's proof brought into live ahead of the 2026-10-26 sync (upstream file)

Module `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal` (upstream).
Maintainer landing 2026-10-27, on the owner's order: bring upstream's proved version into live now
instead of waiting for the full upstream sync.

## Source

Upstream `slopmaster2` at 94795abff8 (PR #1694) proves every property that live left `sorry`
(`upperStarTensorComplexHom_comm`, the naturality fields of `upperStarTensorCounit` and
`leftDerivedUpperStarTensorLeftCounit`, `isLeftDerivedFunctor₂_upperStarTensor`,
`isIso_leftDerivedUpperStarTensor`, the coherences of `monoidal_leftDerivedUpperStar`).
The files are taken byte for byte from the sync work tree
(`~/upstream-sync/sync-20261026/r2/work`, the 2026-10-26 sync re-applied on live), where the
upstream file is split so that each part compiles alone within 60 s:

| module | holds |
|---|---|
| `Derived.MonoidalComplex` | tensor of complexes, K-flat pullback, `upperStarTensorComplexHomX`, `upperStarTensorComplexHom_comm` |
| `Derived.MonoidalComplexHom` | `upperStarTensorComplexHom` (= inverse of the comonoidal comparison), `upperStarTensorTarget` |
| `Derived.MonoidalCounit` | `upperStarTensorCounit` |
| `Derived.MonoidalRightCounit` | `leftDerivedUpperStarTensorRight/Left/RightCounit`, `isLeftDerivedFunctor₂_upperStarTensor` |
| `Derived.MonoidalTensor` | `leftDerivedUpperStarTensorLeftCounit`, `leftDerivedUpperStarTensor`, `_fac` |
| `Derived.MonoidalIso` | `isIso_leftDerivedUpperStarTensor`, `leftDerivedUpperStarTensorIso`, `leftDerivedUpperStarUnitIso` |
| `Derived.MonoidalOplax` | `leftDerivedUpperStarOplaxMonoidal` |
| `Derived.Monoidal` | `monoidal_leftDerivedUpperStar` (imports all of the above) |

All public names and statements live's importers use are kept. The private helpers of live's
version (`p5*`, the private shortcut instances, `upperStarPreservesFlat`, ...) are gone; no other
module used them. Live's private imports of `Sheaf.Paper.IntegralResidueDerivedMonoidal`,
`Sheaf.Paper.InverseImageModuleFlat` and `MapHomologicalComplex` are dropped (private, so no
importer saw them).

`Derived.ProjectionMapShiftFac` and `Derived.ProjectionMapShift` (our 2026-10-27 split, see
maint-projectionmapshift-split.md) declared six lemmas that upstream's Monoidal now provides with
the same statements (`isEquivalence_extendScalars_condensedPullbackHom`,
`kFlat_upperStar_mapHomologicalComplex_obj`, `kFlat_upperStar_mapHomotopyCategory_obj`,
`upperStarTensorComplexHom_δ`, `leftDerivedUpperStarTensorRightCounit_app_app`,
`leftDerivedUpperStarTensor_app_app_fac`); they now import them (text of the sync work tree).

## Checks

Single-file compiles (-j1, one thread) at load ~40: MonoidalComplex 22.6 s, ComplexHom 18.7 s,
Counit 33.9 s, RightCounit 23.7 s, Tensor 33.4 s, Iso 33.3 s, Oplax 17.7 s, Monoidal 16.7 s,
ProjectionMapShiftFac 3.4 s, ProjectionMapShift 38.9 s; no `sorry`. All 49 direct importers of
Monoidal / ProjectionMapShift / ProjectionMapShiftFac compile against the change (the two kernel
errors seen first came from stale intermediate .oleans and vanish once the intermediate module is
rebuilt). `Sheaf.Paper.CompletionTriangleComparison` takes 72 s, 77 s before the change too.

## Record

DAG nodes of the moved declarations repointed (module, file, statement): def-sfb-derived-pullback-
tensor-left-counit, def-sfb-upper-star-tensor-counit, lem-sfb-upper-star-tensor-complex-
comparison-chain-map, lem-sfb-derived-pullback-tensor-left-derived, lem-sfb-derived-pullback-
tensor-comparison-iso, lem-sfb-derived-pullback-strong-monoidal. The preferred-upstream note for
this module (proofs to re-apply) is obsolete and removed. The pending upstream sync meets
identical text here, so its catch-up has nothing to merge in these files.

## Follow-up (same day): cached instances scoped; IntegralProperReductionBound restored

Upstream's Monoidal publicly imports `Sheaf.SixFunctors.ModCondensedCachedInstances` (in the split,
via MonoidalComplex), so its 14 cached instances for `Mod (Sheaf (ProEt.topology Z) Ab)
(condensedRingObj Λ Z)` became visible to everything downstream of Monoidal. In
`Sheaf.Paper.IntegralProperReductionBound`, whose ring `AdicCompletion.ring l E X` is an abbreviation
of `condensedRingObj (DerivedNakayama.integerRing l E) X`, unifying them made the search for
`Mod.derivedExtendMapDerivedCategoryAdjunction` time out (a `Sheaf.monoidalCategory` defeq of 13 s);
the build of 2026-10-27T14:11Z went red and the module and its 3821 importers were quarantined.

Fix: the instances are now `scoped` in the namespace
`AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances`; the modules that import the file
open that scope (the 8 Monoidal modules, ProjectionMapShift, ContinuousIntegralExchangeTargetAdjunct).
Downstream modules see none of them, as before this port. Making the import private instead was
tried and rejected: inside the `public section` the private instances do not serve the public
declarations, and MonoidalIso took 65-88 s.

Measured alone (-j1, load ~50): ModCondensedCachedInstances 8.6 s, MonoidalComplex 27.1 s,
ComplexHom 23.7 s, Counit 37.8 s, RightCounit 23.8 s, Tensor 27.1 s, Iso 31.4 s, Oplax 17.5 s,
Monoidal 17.0 s, ProjectionMapShiftFac 4.7 s, ProjectionMapShift 39.8 s,
ContinuousIntegralExchangeTargetAdjunct 40.4 s, IntegralProperReductionBound 18.2 s (unchanged
text, restored from quarantine/ in this landing; its importers come back by the rework cluster
restore).
