/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.ForgetCoherence
public import WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.Coherence

/-!
# The exchange isomorphisms of pullbacks and pushforwards with automorphisms are mates
-/

@[expose] public section

universe u' u

open CategoryTheory Category Limits Opposite

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
lemma lowerStar_map_counitIso_inv_app_comp_lowerStarComp {X Y : Scheme.{u}} (φ : X ⟶ Y)
    (a : X ≅ X) (b : Y ≅ Y) (c : a.hom ≫ φ = φ ≫ b.hom) (c' : φ ≫ b.inv = a.inv ≫ φ)
    (M : Sheaf (ProEt.topology X) A) :
    (φ)_*[A].map ((lowerStarEquivalence A a).counitIso.inv.app M) ≫
      (lowerStarComp A a.hom φ).hom.app ((a.inv)_*[A].obj M) ≫
      (lowerStarCongr A c).hom.app _ ≫ (lowerStarComp A φ b.hom).inv.app ((a.inv)_*[A].obj M) =
    (lowerStarEquivalence A b).counitIso.inv.app ((φ)_*[A].obj M) ≫
      (b.hom)_*[A].map ((lowerStarComp A φ b.inv).hom.app M ≫ (lowerStarCongr A c').hom.app M ≫
        (lowerStarComp A a.inv φ).inv.app M) := by
  have ea : (lowerStarEquivalence A a).counitIso =
      lowerStarComp A a.inv a.hom ≪≫ lowerStarCongr A a.inv_hom_id ≪≫ lowerStarId A X := rfl
  have eb : (lowerStarEquivalence A b).counitIso =
      lowerStarComp A b.inv b.hom ≪≫ lowerStarCongr A b.inv_hom_id ≪≫ lowerStarId A Y := rfl
  rw [ea, eb]
  ext V
  simp only [Iso.trans_inv, NatTrans.comp_app, ObjectProperty.FullSubcategory.comp_hom,
    lowerStarComp_hom_app_hom_app, lowerStarComp_inv_app_hom_app, lowerStarCongr_hom_app_hom_app,
    lowerStarCongr_inv_app_hom_app, lowerStarId_inv_app_hom_app, lowerStar_map_hom_app',
    lowerStar_obj_obj_map', ← Functor.map_comp, ← op_comp, assoc, Functor.map_comp]
  trace_state
  sorry

end AlgebraicGeometry.ProEtale
