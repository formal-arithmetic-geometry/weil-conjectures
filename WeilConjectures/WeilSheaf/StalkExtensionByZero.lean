/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.Coherence
public import WeilConjectures.WeilSheaf.OpenImmersion
public import WeilConjectures.WeilSheaf.StalkIso
public import WeilConjectures.WeilSheaf.StalkUpperStar

/-!
# Stalks of the extension by zero along an open immersion
-/

@[expose] public section

universe u' u

open CategoryTheory Limits

namespace AlgebraicGeometry.ProEtale

section General

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
variable {Y X : Scheme.{u}} (J : Y ⟶ X) (a : Y ≅ Y) (b : X ≅ X)

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
/-- The inverse of a congruence isomorphism of pushforwards is the reverse congruence. -/
lemma lowerStarCongr_inv {Z W : Scheme.{u}} {g g' : Z ⟶ W} (h : g = g') :
    (lowerStarCongr A h).inv = (lowerStarCongr A h.symm).hom := by
  subst h
  rfl

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
/-- The inverse counit of the pushforward equivalence along an isomorphism, unfolded. -/
lemma lowerStarEquivalence_counitIso_inv_app {Z : Scheme.{u}} (e : Z ≅ Z)
    (M : Sheaf (Scheme.ProEt.topology Z) A) :
    (lowerStarEquivalence A e).counitIso.inv.app M =
      (lowerStarId A Z).inv.app M ≫ (lowerStarCongr A e.inv_hom_id.symm).hom.app M ≫
        (lowerStarComp A e.inv e.hom).inv.app M := by
  change (lowerStarId A Z).inv.app M ≫ (lowerStarCongr A e.inv_hom_id).inv.app M ≫
    (lowerStarComp A e.inv e.hom).inv.app M = _
  rw [lowerStarCongr_inv]

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
lemma lowerStar_map_counitIso_inv_app_comp (hc : a.hom ≫ J = J ≫ b.hom)
    (hci : J ≫ b.inv = a.inv ≫ J) (M : Sheaf (Scheme.ProEt.topology Y) A) :
    (J)_*[A].map ((lowerStarEquivalence A a).counitIso.inv.app M) ≫
        (lowerStarComp A a.hom J).hom.app ((a.inv)_*[A].obj M) ≫
        (lowerStarCongr A hc).hom.app ((a.inv)_*[A].obj M) ≫
        (lowerStarComp A J b.hom).inv.app ((a.inv)_*[A].obj M) =
      (lowerStarEquivalence A b).counitIso.inv.app ((J)_*[A].obj M) ≫
        (b.hom)_*[A].map ((lowerStarComp A J b.inv).hom.app M ≫
          (lowerStarCongr A hci).hom.app M ≫ (lowerStarComp A a.inv J).inv.app M) := by
  rw [lowerStarEquivalence_counitIso_inv_app, lowerStarEquivalence_counitIso_inv_app]
  ext V
  simp only [NatTrans.comp_app, ObjectProperty.FullSubcategory.comp_hom,
    lowerStarComp_hom_app_hom_app, lowerStarComp_inv_app_hom_app, lowerStarCongr_hom_app_hom_app,
    lowerStarId_inv_app_hom_app, lowerStar_map_hom_app', lowerStar_obj_obj_map',
    Functor.map_comp, ← Functor.map_comp, ← op_comp, Category.assoc]
  trace_state
  sorry

end General

end AlgebraicGeometry.ProEtale
