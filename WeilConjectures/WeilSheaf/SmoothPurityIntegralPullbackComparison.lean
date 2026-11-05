/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityScalarPullback
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.WeaklyEtaleBaseChange

/-! # The underlying integral coefficient pullback -/

@[expose] public section

universe u
open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Obj AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale

variable {X U : Scheme.{u}} (g : U ⟶ X) [WeaklyEtale g] (l : ℕ) [Fact l.Prime]

/-- The integral pullback commutes with forgetting the coefficient action. -/
noncomputable def purityIntegralPullbackForgetIso :
    Mod.forget (condensedRingObj (Profinite.continuousMapRingObj ℤ_[l]) X) ⋙
        (g)^*[Ab.{u + 1}] ≅
      (g)^*⟦Profinite.continuousMapRingObj ℤ_[l]⟧ ⋙
        Mod.forget (condensedRingObj (Profinite.continuousMapRingObj ℤ_[l]) U) :=
  CondensedRing.upperStarForgetIso (Profinite.continuousMapRingObj ℤ_[l]) g

/-- Commutativity of the integral coefficient ring, in the native ring-sheaf coordinates. -/
instance (priority := 20000) purityIntegralCommMonObj :
    IsCommMonObj (Profinite.continuousMapRingObj.{u} ℤ_[l]) :=
  Sheaf.isCommMonObj_sheafCompose_obj (coherentTopology Profinite.{u})
    (Profinite.continuousMapRingSheaf ℤ_[l])
    fun S (a b : ULift.{u + 1} C(S.unop, ℤ_[l])) ↦ mul_comm a b

/-- The coefficient extension unit in the integral ring-sheaf coordinates. -/
noncomputable def purityIntegralPullbackUnit
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj ℤ_[l]) X)) :
    (g)^*[Ab.{u + 1}].obj M.X ⟶
      ((g)^*⟦Profinite.continuousMapRingObj ℤ_[l]⟧.obj M).X :=
  CondensedRing.upperStarUnitHom (Profinite.continuousMapRingObj ℤ_[l]) g M

end AlgebraicGeometry.ProEtale
