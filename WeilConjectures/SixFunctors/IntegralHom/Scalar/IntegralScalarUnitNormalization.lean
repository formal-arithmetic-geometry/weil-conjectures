/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.DeligneLaumon.PrincipalKoszulStrictReplacement.PrincipalKoszulStrictReplacement
public import WeilConjectures.SixFunctors.Integral.IntegralReductionTowerWellDefinedUnrestricted
public import WeilConjectures.SmoothPurity.IntegralOnSlice.IntegralDerivedOperationsOnSlices
import WeilConjectures.SixFunctors.IntegralHom.Reduction.IntegralHomReductionModels

/-! # Identifying the two canonical scalar-extension augmentation maps

## References

* Stacks Project, Tag 03EK.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits Opposite
namespace WeilConjectures.IntegralHom
attribute [local instance 20000] abSheafify abLocallyBijective
attribute [local irreducible] completedIntegralCoefficientSheafUnrestricted
  HasDerivedCategory.standard scalarReductionExistence scalarReductionDerivedExistence
  unrestrictedIntegralReductionExistence
attribute [local implicit_reducible] completedIntegralCommRingSheafUnrestricted
  CategoryTheory.sheafCompose IntegralOnSlice.Site IntegralOnSlice.siteCategory
  IntegralOnSlice.topology IntegralOnSlice.restrict IntegralOnSlice.ring IntegralOnSlice.finite
  IntegralOnSlice.projection SheafOfModules.restrictScalars
  completedIntegralCommRingProjectionUnrestricted integralCoefficientSheaf
  integralCoefficientCommRingSheaf

/-- The slice augmentation at the empty slice datum is the recorded scalar unit. -/
theorem integralScalarAugmentation_eq_unrestrictedUnit
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (Y : AlgebraicGeometry.Scheme.{t})
    (P : CochainComplex (PrincipalKoszulStrictReplacement.Modules l E Y) ℤ) (n : ℕ) :
    ((IntegralOnSlice.augmentation l E Y none).app P).app (op n) =
      unrestrictedTowerUnit l E Y P n := by
  ext i U x
  exact (IntegralOnSlice.augmentation_existsUnique l E Y none).exists.choose_spec P n i U x
    |>.trans ((unrestrictedTowerUnit_condition l E Y P n i U x).symm)

end WeilConjectures.IntegralHom
