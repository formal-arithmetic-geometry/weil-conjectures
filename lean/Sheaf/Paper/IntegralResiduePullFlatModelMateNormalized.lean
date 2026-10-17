/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE
Authors: SHEAF group A2
-/
module

public import Sheaf.Paper.IntegralResiduePullSquareData
import Sheaf.Paper.IntegralResiduePullOrdinaryUnit

/-! The counit-normalized mate calculation for the integral residue pull square.

Source: Bhatt--Scholze, Remark 6.8.15.
(blueprint: new-integral-residue-pull-flat-model-comparison-mate-normalized)
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Limits MonoidalCategory
open CategoryTheory.Functor
open scoped CategoryTheory.Obj CategoryTheory.Functor
local instance : EssentiallySmall.{u + 1} Profinite.{u} := essentiallySmallSelf.{0} _
namespace AlgebraicGeometry.ProEtale.CondensedRing
attribute [local irreducible] Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  Functor.mapDerivedCategory
variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]

/-- After cancellation of the exact residue pullback counit, the derived mate
calculation is the scalar-adjunction square. The proof expands the two derived
counits, transposes along `residueExchangeReductionAdjunction`, and applies
`residueExchangePull_ordinary_unit`; naturality of the localization counits
then gives the displayed normalized equation.
(blueprint: new-integral-residue-pull-flat-model-comparison-mate-normalized)
-/
theorem residueExchangePull_flatModel_mate_normalized
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (H : HomotopyCategory
      (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
        (condensedRingObj (integralCoeff ℓ E) Y)) (.up ℤ))
    (hC : IsIso ((residueExchangeUpperStarCounit
      (Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)) f).app
      (((Mod.extendScalars
        (coefficientMap (integralReductionMap ℓ E) Y)).mapHomotopyCategory
          (.up ℤ)).obj H))) :
    ((residueExchangeReduction ℓ E X).map
        ((residueExchangeUpperStarCounit (integralCoeff ℓ E) f).app H) ≫
      (residueExchangeReductionCounit ℓ E X).app
        ((((f)^*⟦integralCoeff ℓ E⟧).mapHomotopyCategory (.up ℤ)).obj H) ≫
      DerivedCategory.Qh.map
        ((NatTrans.mapHomotopyCategory
          (pullIso (integralReductionMap ℓ E) f).hom (.up ℤ)).app H)) ≫
      inv ((residueExchangeUpperStarCounit
        (Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)) f).app
        (((Mod.extendScalars
          (coefficientMap (integralReductionMap ℓ E) Y)).mapHomotopyCategory
            (.up ℤ)).obj H)) =
    (residueExchangePullHom ℓ E f).app (DerivedCategory.Qh.obj H) ≫
      (residueExchangeUpperStar
        (Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)) f).map
        ((residueExchangeReductionCounit ℓ E Y).app H) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing

