# Derived/Localizing: cached instances for module objects over Λ_Z (upstream file)

Module `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Localizing` (upstream).
For the PR agent to send upstream. No statement changes.

## Reason

The file compiled alone in 98-110 s, 84 s of it typeclass inference. Each mention of
`L((f)^*⟦Λ⟧)` (`Functor.leftDerivedFunctor`, see
`CategoryTheory/DerivedCategory/LeftDerivedFunctor/Defs.lean`) carries the instance arguments
`∀ X₁ X₂ X₃ X₄ : GradedObject ℤ C, HasTensor₄ObjExt …`, `HasGoodTensor₁₂Tensor`,
`HasGoodTensorTensor₂₃`, `HasColimitsOfShape ℤ C`, `PreservesColimitsOfShape ℤ (tensor)`, and
so on, for `C = Mod (Sheaf (ProEt.topology Z) Ab) (condensedRingObj Λ Z)`. Each ∀ instance is
re-searched from the generic GradedObject/colimit instances, at 2-4 s per use, and that search
is not cached across declarations. The private shortcuts that
`ModuleObject/Derived/Monoidal.lean` declares for the same goals are not visible to importers.

## Change

* Nine instances (priority 2000), stated for `Mod (Sheaf (ProEt.topology Z) Ab) (condensedRingObj Λ Z)`
  and proved by `inferInstance`, added before the first section:
  `hasTensorFour_modCondensed`, `hasGoodTensor₁₂Tensor_modCondensed`,
  `hasGoodTensorTensor₂₃_modCondensed`, `hasColimitsOfShapeInt_modCondensed`,
  `hasExactColimitsOfShapeInt_modCondensed`, `hasCountableCoproducts_modCondensed`,
  `preservesColimitsOfShapeInt_tensorLeft_modCondensed`,
  `preservesColimitsOfShapeInt_tensorRight_modCondensed`, `hasFunctorialFlatResolution_modCondensed`.
* The instance `((R((p)_*⟦Λ⟧) ⋙ curriedTensor 𝔻(Y)).obj M).CommShift ℤ` now uses
  `(inferInstance : Functor.CommShift …)` in place of `inferInstanceAs (…)`. It took 8.2 s
  before and 0.6 s after.

Result: 32 s alone (162 s against 50 s when both ran under the same machine load).
Importers: LocalizingInputs 8 s and TransportSources 10 s. ProjectionMapShift takes 84 s, and
191 s with the old Localizing.

A better upstream location for these instances is the file that first derives `(f)^*⟦Λ⟧`
(`ModuleObject/Derived/UpperLowerStar.lean`). There every importer would get them.
