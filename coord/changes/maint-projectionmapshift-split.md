# Derived/ProjectionMapShift: split and cached instances (upstream file)

Module `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProjectionMapShift` (upstream).
For the PR agent to send upstream. No statement or name changes.

## Reason

The file compiled alone in 84 s even with the faster Localizing (191 s with the old one), and
in 94-129 s under build load. Most of the time was the instance search for
`Mod (Sheaf (ProEt.topology Z) Ab) (condensedRingObj Λ Z)`: `∀ X₁ X₂ : GradedObject ℤ _, HasTensor`
took 23 s over 18 uses, plus `PreservesColimit (Functor.empty _)` of the tensor functors. See
coord/changes/maint-localizing-cached-modcondensed-instances.md.

## Change

* The file imports `Sheaf.SixFunctors.ModCondensedCachedInstances`, which holds the cached
  instances (all `inferInstance`, priority 2000).
* Everything before `kFlat_upperStar_mapHomotopyCategory_obj` moves unchanged, with the same
  preamble, to a new module `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProjectionMapShiftFac`.
  That part is `isEquivalence_extendScalars_condensedPullbackHom`,
  `kFlat_upperStar_mapHomologicalComplex_obj`, `upperStarTensorComplexHom_δ`,
  `leftDerivedUpperStarTensorRightCounit_app_app` and `leftDerivedUpperStarTensor_app_app_fac`.
  ProjectionMapShift publicly imports the new module.

Result, measured together at load ~100: ProjectionMapShiftFac 54 s and ProjectionMapShift 52 s,
against 94-129 s for the single file at the same load. Importers IntegralTensorPullback 8 s and
LocalizingProjection 9 s. No DAG node records these declarations.
