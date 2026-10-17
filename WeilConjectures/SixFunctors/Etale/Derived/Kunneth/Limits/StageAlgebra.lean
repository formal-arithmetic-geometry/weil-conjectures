/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Limits.DimensionShift

/-!
# Calculus of transition maps on stalks

Elementwise consequences of the composition law of the transition maps of stages
(`AlgebraicGeometry.Etale.LimitStage.transition_apply_comp`), transport of elementwise colimits
along isomorphisms (`ModuleCat.IsElementwiseColimit.of_iso`), and change of the scheme of
coefficients along a morphism `v : W' ⟶ W` (`AlgebraicGeometry.Etale.LimitStage.mapW`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace ModuleCat.IsElementwiseColimit

variable {R : Type*} [Ring R] {I : Type*} [Category I]

/-- Elementwise colimits are transported along compatible isomorphisms. -/
lemma of_iso {A A' : I → ModuleCat R} {B B' : ModuleCat R} {σ : ∀ i, A i ⟶ B}
    {σ' : ∀ i, A' i ⟶ B'} {τ : ∀ {i j : I}, (i ⟶ j) → (A j ⟶ A i)}
    {τ' : ∀ {i j : I}, (i ⟶ j) → (A' j ⟶ A' i)} (e : ∀ i, A i ≅ A' i) (eB : B ≅ B')
    (hσ : ∀ i, (e i).hom ≫ σ' i = σ i ≫ eB.hom)
    (hτ : ∀ {i j : I} (f : i ⟶ j), (e j).hom ≫ τ' f = τ f ≫ (e i).hom)
    (h' : IsElementwiseColimit A' B' σ' τ') : IsElementwiseColimit A B σ τ := by
  refine ⟨fun b ↦ ?_, fun i a ha ↦ ?_⟩
  · obtain ⟨i, a', ha'⟩ := h'.1 (eB.hom.hom b)
    refine ⟨i, (e i).inv.hom a', ?_⟩
    apply (ConcreteCategory.injective_of_mono_of_preservesPullback eB.hom)
    rw [← ModuleCat.comp_apply, ← hσ, ModuleCat.comp_apply, ← ModuleCat.comp_apply (e i).inv,
      Iso.inv_hom_id, ModuleCat.id_apply, ha']
  · have h0 : (σ' i).hom ((e i).hom.hom a) = 0 := by
      rw [← ModuleCat.comp_apply, hσ, ModuleCat.comp_apply, ha, map_zero]
    obtain ⟨j, f, hf⟩ := h'.2 i _ h0
    refine ⟨j, f, ?_⟩
    apply (ConcreteCategory.injective_of_mono_of_preservesPullback (e j).hom)
    rw [← ModuleCat.comp_apply, ← hτ, ModuleCat.comp_apply, hf, map_zero, map_zero]

end ModuleCat.IsElementwiseColimit

namespace AlgebraicGeometry.Etale

variable (Λ : Type (u + 1)) [CommRing Λ]

namespace LimitStage

variable {B W : Scheme.{u}}

/-- The composition law of the transition maps, applied to elements of stalks. -/
lemma transition_apply_comp (q : ℤ) (x : B)
    (K : DerivedCategory.Plus (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    {α β γ : LimitStage B W} (φ : Hom α β) (ψ : Hom β γ) (χ : Hom α γ) (h : φ.comp ψ = χ)
    (y : (stalkHomology Λ q x).obj ((functor Λ γ).obj K)) :
    ((stalkHomology Λ q x).map ((transition Λ φ).app K)).hom
        (((stalkHomology Λ q x).map ((transition Λ ψ).app K)).hom y) =
      ((stalkHomology Λ q x).map ((transition Λ χ).app K)).hom y := by
  subst h
  rw [← ModuleCat.comp_apply, ← Functor.map_comp, ← NatTrans.comp_app, transition_comp]

/-- The transition maps of a pair of mutually inverse morphisms of stages are inverse. -/
lemma transition_apply_inv (q : ℤ) (x : B)
    (K : DerivedCategory.Plus (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    {α β : LimitStage B W} (φ : Hom α β) (ψ : Hom β α) (h : φ.comp ψ = Hom.id α)
    (y : (stalkHomology Λ q x).obj ((functor Λ α).obj K)) :
    ((stalkHomology Λ q x).map ((transition Λ φ).app K)).hom
        (((stalkHomology Λ q x).map ((transition Λ ψ).app K)).hom y) = y := by
  rw [transition_apply_comp Λ q x K φ ψ _ h, transition_id]
  rfl

end LimitStage

end AlgebraicGeometry.Etale
