/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartStratificationDefs
import WeilConjectures.CategoryTheory.ModuleObjects.FreeMap
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FinitelyPresentedStalk
import WeilConjectures.AlgebraicGeometry.ProEtale.SepClosedPointLift

/-! # Finite freeness at the chosen geometric point
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CoefficientHeartTower

/-- A lisse native coefficient module becomes finite free at a geometric point.
Source: Bhatt--Scholze, Example 4.1.10. -/
theorem point_freeness
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X : Scheme.{u}}
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hM : IsLisseCoefficientModule Λ M)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (v : Spec (.of Ω) ⟶ X) :
    Mod.IsFree (condensedRingObj Λ (Spec (.of Ω)))
      ((CondensedRing.upperStar Λ v).obj M) := by
  obtain ⟨U, hU⟩ := hM
  obtain ⟨i, g, hg⟩ := U.exists_comp_eq_of_isSepClosed_of_proetale v
  subst v
  have hfree := (hU i).map (CondensedRing.upperStar Λ g)
    (CondensedRing.upperStarObjRegularIso Λ g)
  exact hfree.of_iso ((CondensedRing.upperStarComp Λ g (U.f i)).app M).symm

end AlgebraicGeometry.ProEtale.CoefficientHeartTower
