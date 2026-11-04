/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityFreeResolution

/-!
# Testing a trace on free objects

An invertible comparison with the free functor transfers the universal property of
an underlying trace to free Weil objects. The free resolution criterion then extends
that universal property to bounded Weil objects. This avoids choosing a geometric
comparison for a native right adjoint.
-/

@[expose] public section

open CategoryTheory

namespace CategoryTheory.Adjunction

/-- A universal arrow has an invertible adjoint transpose. -/
theorem isIso_homEquiv_of_bijective
    {C D : Type*} [Category C] [Category D] {T : C ⥤ D} {R : D ⥤ C}
    (adj : T ⊣ R) {H : C} {Y : D} (d : T.obj H ⟶ Y)
    (hd : ∀ M, Function.Bijective (fun u : M ⟶ H ↦ T.map u ≫ d)) :
    IsIso (adj.homEquiv H Y d) := by
  apply isIso_of_yoneda_map_bijective
  intro M
  change Function.Bijective (fun u : M ⟶ H ↦ u ≫ adj.homEquiv H Y d)
  have h : (fun u : M ⟶ H ↦ u ≫ adj.homEquiv H Y d) =
      (adj.homEquiv M Y) ∘ (fun u : M ⟶ H ↦ T.map u ≫ d) := by
    funext u
    exact (adj.homEquiv_naturality_left u d).symm
  rw [h]
  exact (adj.homEquiv M Y).bijective.comp (hd M)

/-- A trace which is universal after forgetting is universal on free objects, provided
the comparison of the free functors is invertible and respects the free units. -/
theorem bijective_map_comp_on_free_of_forget
    {C C' D D' : Type*} [Category C] [Category C'] [Category D] [Category D']
    {I : C ⥤ C'} {U : C' ⥤ C} (adj₁ : I ⊣ U)
    {J : D ⥤ D'} {V : D' ⥤ D} (adj₂ : J ⊣ V)
    (R : C' ⥤ D') (r : C ⥤ D) (e : R ⋙ V ≅ U ⋙ r)
    {A : C'} {B : D'} (d : R.obj A ⟶ B) (X : C)
    (β : J.obj (r.obj X) ≅ R.obj (I.obj X))
    (hβ : adj₂.unit.app (r.obj X) ≫ V.map β.hom =
      r.map (adj₁.unit.app X) ≫ e.inv.app (I.obj X))
    (h : Function.Bijective (fun u : X ⟶ U.obj A ↦
      r.map u ≫ e.inv.app A ≫ V.map d)) :
    Function.Bijective (fun u : I.obj X ⟶ A ↦ R.map u ≫ d) := by
  have he (u : I.obj X ⟶ A) :
      adj₂.homEquiv (r.obj X) B (β.hom ≫ R.map u ≫ d) =
        r.map (adj₁.homEquiv X A u) ≫ e.inv.app A ≫ V.map d := by
    simp only [Adjunction.homEquiv_unit, Functor.map_comp, Category.assoc]
    rw [reassoc_of% hβ, ← e.inv.naturality_assoc u]
    rfl
  constructor
  · intro u u' huu
    apply (adj₁.homEquiv X A).injective
    apply h.1
    rw [← he u, ← he u', huu]
  · intro y
    obtain ⟨u, hu⟩ := h.2 (adj₂.homEquiv (r.obj X) B (β.hom ≫ y))
    refine ⟨(adj₁.homEquiv X A).symm u, ?_⟩
    apply (cancel_epi β.hom).1
    apply (adj₂.homEquiv (r.obj X) B).injective
    rw [he, Equiv.apply_symm_apply]
    exact hu

end CategoryTheory.Adjunction
