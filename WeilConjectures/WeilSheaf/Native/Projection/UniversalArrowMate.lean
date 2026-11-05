/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.MateTransposeIsIso
public import Mathlib.CategoryTheory.Yoneda

/-! # Invertibility of a mate from a compatible universal arrow -/

@[expose] public section

namespace CategoryTheory.Adjunction

variable {C D E F : Type*} [Category* C] [Category* D] [Category* E] [Category* F]
  {L : C ⥤ D} {R : D ⥤ C} {L' : E ⥤ F} {R' : F ⥤ E}
  (adj : L ⊣ R) (adj' : L' ⊣ R') {U : C ⥤ E} {V : D ⥤ F}

/-- A universal arrow transposes to an isomorphism under any right adjunction. -/
lemma isIso_homEquiv_of_bijective {A : C} {B : D} (d : L.obj A ⟶ B)
    (hd : ∀ M, Function.Bijective (fun u : M ⟶ A ↦ L.map u ≫ d)) :
    IsIso (adj.homEquiv A B d) := by
  apply isIso_of_yoneda_map_bijective
  intro M
  convert (adj.homEquiv M B).bijective.comp (hd M) using 1
  ext u
  exact (adj.homEquiv_naturality_left u d).symm

/-- If a universal arrow lies over the geometric counit through an isomorphism, the mate of
its forget comparison is invertible at the target. -/
lemma isIso_mateEquiv_app_of_universalArrow (α : TwoSquare U L L' V)
    {A : C} {B : D} (d : L.obj A ⟶ B)
    (hd : ∀ M, Function.Bijective (fun u : M ⟶ A ↦ L.map u ≫ d))
    (e : U.obj A ≅ R'.obj (V.obj B))
    (he : α.app A ≫ V.map d = L'.map e.hom ≫ adj'.counit.app (V.obj B)) :
    IsIso ((mateEquiv adj adj' α).app B) := by
  have : IsIso (adj.homEquiv A B d) := adj.isIso_homEquiv_of_bijective d hd
  have h : U.map (adj.homEquiv A B d) ≫ (mateEquiv adj adj' α).app B = e.hom := by
    apply (adj'.homEquiv _ _).symm.injective
    rw [Adjunction.homEquiv_symm_map_comp_app adj adj' (mateEquiv adj adj' α),
      Equiv.symm_apply_apply, Equiv.symm_apply_apply, Adjunction.homEquiv_counit]
    exact he
  have : IsIso (U.map (adj.homEquiv A B d) ≫ (mateEquiv adj adj' α).app B) := by
    rw [h]
    infer_instance
  exact IsIso.of_isIso_comp_left (U.map (adj.homEquiv A B d)) _

end CategoryTheory.Adjunction
