/- Copyright (c) 2026 The SHEAF contributors. -/
module
public import Sheaf.Paper.RationalTatePullback
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
import all Sheaf.Paper.DerivedExchangeExactNormalization
@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.RationalP1
open DiagonalCoefficients CondensedRing
section DerivedCalculations

attribute [local instance 20000] AlgebraicGeometry.ProEtale.sheafBraidedCategory

attribute [local instance] CondensedRing.cachedFour CondensedRing.cachedGood12
  CondensedRing.cachedGood23 CondensedRing.cachedTensorLeft CondensedRing.cachedTensorRight
  CondensedRing.cachedSheafColimits CondensedRing.cachedSheafBigColimits
  CondensedRing.cachedCoequalizers CondensedRing.cachedModulePreadditive
  CondensedRing.cachedModuleFlatResolution CondensedRing.cachedExactSequential
  CondensedRing.cachedTensorLeftSequential CondensedRing.cachedTensorRightSequential
  CondensedRing.pullback_commShift

@[instance_reducible] noncomputable def cachedModuleClosed (T : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) [MonObj R] [IsCommMonObj R] :
    MonoidalClosed (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) R) := by
  let : SymmetricCategory (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) :=
    { toBraidedCategory := sheafBraidedCategory Ab.{u + 1} T
      symmetry := fun M N ↦ @SymmetricCategory.symmetry _ _ _
        (sheafSymmetricCategory T) M N }
  exact Mod.monoidalClosed

attribute [local instance 30000] cachedModuleClosed

end DerivedCalculations
end AlgebraicGeometry.ProEtale.RationalP1
