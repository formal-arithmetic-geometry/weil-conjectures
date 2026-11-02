/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Sites.Categorical.CategoricalFiniteCechCriterion
public import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteAffineCechRefinement

/-! # A Čech criterion separating affine and terminal calculations

Source: the affine-cover and proper Čech steps of the closed-injective calculation.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.ProEt

attribute [local instance] Over.ConstructProducts.over_finiteProducts_of_finiteWidePullbacks

private theorem affine_of_terminal_map {S : Scheme.{u}} (T : S.ProEt) [IsIso T.hom]
    {V : S.ProEt} [IsAffine V.left] {N : Over V} (e : N.left ≅ T) :
    IsAffine N.left.left := by
  have : IsIso e.inv.left :=
    inferInstanceAs (IsIso ((ProEt.forget S ⋙ Over.forget S).map e.inv))
  have : IsIso e.hom.left :=
    inferInstanceAs (IsIso ((ProEt.forget S ⋙ Over.forget S).map e.hom))
  let s : T.left ⟶ V.left := e.inv.left ≫ N.hom.left
  have hs : s ≫ V.hom = T.hom := by
    dsimp only [s]
    rw [Category.assoc, MorphismProperty.Over.w N.hom, MorphismProperty.Over.w e.inv]
  have : IsClosedImmersion (s ≫ V.hom) := by rw [hs]; infer_instance
  have : IsClosedImmersion s := IsClosedImmersion.of_comp s V.hom
  have : IsAffine T.left := isAffine_of_isAffineHom s
  exact IsAffine.of_isIso e.hom.left

/-- To prove positive derived-section vanishing, it suffices to prove finite Čech
exactness separately over affine objects and over the terminal object.
Source: Stacks, Tag 03F9, and finite affine pro-étale refinements.
(blueprint: lem-sp-proetale-affine-and-terminal-cech-criterion).

Proof: use the class of affine objects together with the
terminal object itself. Every covering sieve of one of these objects has a finite affine
refinement whose Čech intersections are affine, by quasi-compactness and separatedness.
For an affine base, an intersection equal to the terminal object is affine too:
its map to the affine base is a section of a separated morphism, hence a closed
immersion. Thus the affine and terminal hypotheses give Čech exactness on the whole
class. Apply the categorical finite Čech criterion to this class and the terminal
object. All arguments include empty covers and the empty scheme. -/
theorem isZero_sections_of_affine_and_terminal_cech
    (Λ : Type (u + 1)) [CommRing Λ] {S : Scheme.{u}}
    (T : S.ProEt) [IsIso T.hom] [CompactSpace T.left] [T.left.IsSeparated]
    (F : Sheaf (topology S) (ModuleCat.{u + 1} Λ))
    (haffine : ∀ (V : S.ProEt), IsAffine V.left →
      ∀ {n : ℕ} (U : Fin n → Over V),
        (∀ (k : ℕ) (y : Fin (k + 1) → Fin n),
          IsAffine (Presheaf.cechNerveObj U y).left.left) →
        Sieve.ofArrows (fun a ↦ (U a).left) (fun a ↦ (U a).hom) ∈ topology S V →
        ∀ q : ℕ, ((cechComplexFunctor U).obj ((Over.forget V).op ⋙ F.obj)).ExactAt (q + 1))
    (hterminal : ∀ {n : ℕ} (U : Fin n → Over T),
      (∀ (k : ℕ) (y : Fin (k + 1) → Fin n),
        IsAffine (Presheaf.cechNerveObj U y).left.left ∨
          (Presheaf.cechNerveObj U y).left = T) →
      Sieve.ofArrows (fun a ↦ (U a).left) (fun a ↦ (U a).hom) ∈ topology S T →
      ∀ q : ℕ, ((cechComplexFunctor U).obj ((Over.forget T).op ⋙ F.obj)).ExactAt (q + 1))
    (q : ℕ) : IsZero (((ProEtale.sectionsFunctor (ModuleCat.{u + 1} Λ) T).rightDerived
      (q + 1)).obj F) := by
  let B : S.ProEt → Prop := fun V ↦ IsAffine V.left ∨ V = T
  have hcov : ∀ V, B V → ∀ R ∈ topology S V,
      ∃ (n : ℕ) (U : Fin n → Over V),
        (∀ (k : ℕ) (y : Fin (k + 1) → Fin n), B (Presheaf.cechNerveObj U y).left) ∧
        (∀ a, R (U a).hom) ∧
        Sieve.ofArrows (fun a ↦ (U a).left) (fun a ↦ (U a).hom) ∈ topology S V := by
    intro V hV R hR
    have hcompact : CompactSpace V.left := by
      rcases hV with hV | rfl
      · have := hV
        infer_instance
      · infer_instance
    have hsep : V.left.IsSeparated := by
      rcases hV with hV | rfl
      · have := hV
        infer_instance
      · infer_instance
    obtain ⟨n, U, hU, hUR, hcover⟩ := exists_finite_affine_cech_of_mem_topology hR
    exact ⟨n, U, fun k y ↦ Or.inl (hU k y), hUR, hcover⟩
  have hF : Sheaf.finiteCechAcyclicOn B F := by
    intro V hV n U hUB hcover q
    rcases hV with hV | rfl
    · have := hV
      exact haffine V hV U (fun k y ↦ by
        rcases hUB k y with h | e
        · exact h
        · exact affine_of_terminal_map T (eqToIso e)) hcover q
    · exact hterminal U hUB hcover q
  exact Sheaf.isZero_rightDerived_eval_of_finiteCech B hcov F hF T
    (Or.inr rfl) q

end AlgebraicGeometry.Scheme.ProEt
