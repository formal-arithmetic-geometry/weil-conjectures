/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.CategoryTheory.Triangulated.Triangulated
import WeilConjectures.CategoryTheory.Triangulated.HomotopyLimit.Tower

/-!
# Finite tails of Roos homotopy-limit cones

Source: Stacks Project, derived.tex, Tag 08TC (Roos triangle), with finite translation
proved in `IsHomotopyLimit.whiskerAdd` (blueprint: lem-sp-roos-finite-tail-cone).
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace CategoryTheory

/--
Finite tails of a Roos homotopy-limit cone retain the same vertex and prescribed
projection legs: if `M → ∏ X → ∏ X → M[1]` (first arrow `p`, middle arrow `1 - s_X`)
is distinguished, then for every `k` the tail `X^{≥k}_n = X (k + n)` with its original
transitions `t (k + n)` has a distinguished Roos triangle with the same vertex `M`,
first arrow the product of the legs `p_{k+n}`, and some boundary `δ'`.
No exactness of products is assumed.
Source: Stacks Project, derived.tex, Tag 08TC; finite translation by
`IsHomotopyLimit.whiskerAdd` (blueprint: lem-sp-roos-finite-tail-cone).

Proof (node lem-sp-roos-finite-tail-cone).
1. The first two arrows compose to zero. After the nth product projection this says
   `p_n = p_{n+1} ≫ t_n`, so these legs define a cone over `Functor.ofOpSequence t`.
   The product universal property identifies its Milnor triangle with the given one.
2. Apply the existing proved `IsHomotopyLimit.whiskerAdd` theorem. It retains the cone
   vertex and legs after finite translation. The equality `n + k = k + n` identifies
   the indexing functor with `n ↦ k + n`, preserving the original transitions.
3. Use `IsHomotopyLimit.exists_distTriang` with the chosen product of the tail. Product
   extensionality identifies its first arrow with the prescribed product of legs and
   its middle arrow with `towerTransitionEndomorphism (fun n ↦ t (k + n))`.
   The resulting boundary supplies `δ'`. No direct-sum cancellation is needed.
-/
theorem roos_finite_tail_cone
    {D : Type u} [Category.{v} D] [HasZeroObject D] [HasShift D ℤ]
    [Preadditive D] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    [IsTriangulated D] [HasCountableProducts D]
    (X : ℕ → D) (t : ∀ n : ℕ, X (n + 1) ⟶ X n) (M : D)
    (p : M ⟶ ∏ᶜ X) (δ : (∏ᶜ X) ⟶ M⟦(1 : ℤ)⟧)
    (h : IsDerivedLimitTriangle t M p δ) (k : ℕ) :
    ∃ δ' : (∏ᶜ (fun n : ℕ ↦ X (k + n))) ⟶ M⟦(1 : ℤ)⟧,
      IsDerivedLimitTriangle (K := fun n : ℕ ↦ X (k + n)) (fun n : ℕ ↦ t (k + n)) M
        (Pi.lift (fun n : ℕ ↦ p ≫ Pi.π X (k + n))) δ' := by
  let F : ℕᵒᵖ ⥤ D := Functor.ofOpSequence t
  have hp (n : ℕ) : p ≫ Pi.π X n = p ≫ Pi.π X (n + 1) ≫ t n := by
    have hz : p ≫ towerTransitionEndomorphism t = 0 :=
      comp_distTriang_mor_zero₁₂ _ h
    rw [towerTransitionEndomorphism, Preadditive.comp_sub, Category.comp_id,
      sub_eq_zero] at hz
    have hn := congrArg (fun f ↦ f ≫ Pi.π X n) hz
    simpa only [Category.assoc, towerProductShift, Pi.lift_π] using hn
  let c : Cone F :=
    { pt := M
      π := NatTrans.ofOpSequence (fun n ↦ p ≫ Pi.π X n) (by
        intro n
        change (𝟙 M) ≫ (p ≫ Pi.π X n) =
          (p ≫ Pi.π X (n + 1)) ≫ F.map (homOfLE (Nat.le_succ n)).op
        rw [Category.id_comp]
        simpa only [F, Functor.ofOpSequence_map_homOfLE_succ, Category.assoc] using hp n) }
  have hc : IsHomotopyLimit c := by
    refine ⟨Fan.mk _ (Pi.π X), productIsProduct X, δ, ?_⟩
    have he : Fan.IsLimit.lift (productIsProduct X) (fun n ↦ c.π.app ⟨n⟩) = p := by
      apply Pi.hom_ext
      intro n
      exact Fan.IsLimit.fac (productIsProduct X) _ n
    have hs : towerShift (F := F) (productIsProduct X) = towerProductShift t := by
      apply Pi.hom_ext
      intro n
      rw [show towerProductShift t ≫ Pi.π X n = Pi.π X (n + 1) ≫ t n from
        Pi.lift_π _ _]
      simpa only [fan_mk_proj, F, Functor.ofOpSequence_map_homOfLE_succ] using
        towerShift_proj (F := F) (productIsProduct X) n
    rw [he, hs]
    exact h
  let S : ℕᵒᵖ ⥤ ℕᵒᵖ :=
    (Monotone.functor (f := fun n : ℕ ↦ k + n) (fun _ _ h ↦ Nat.add_le_add_left h k)).op
  have hS : addOpFunctor k = S := by
    dsimp [addOpFunctor, S]
    congr 2
    funext n
    exact Nat.add_comm n k
  have hc' := hc.whiskerAdd k
  rw [hS] at hc'
  obtain ⟨δ', hδ'⟩ := hc'.exists_distTriang (productIsProduct (fun n : ℕ ↦ X (k + n)))
  refine ⟨δ', ?_⟩
  have hs : towerShift (F := S ⋙ F) (productIsProduct (fun n : ℕ ↦ X (k + n))) =
      towerProductShift (fun n : ℕ ↦ t (k + n)) := by
    apply Pi.hom_ext
    intro n
    rw [show towerProductShift (fun n : ℕ ↦ t (k + n)) ≫
        Pi.π (fun n : ℕ ↦ X (k + n)) n =
        Pi.π (fun n : ℕ ↦ X (k + n)) (n + 1) ≫ t (k + n) from Pi.lift_π _ _]
    have ht := towerShift_proj (F := S ⋙ F)
      (productIsProduct (fun n : ℕ ↦ X (k + n))) n
    simp only [fan_mk_proj] at ht
    rw [ht]
    change Pi.π (fun n : ℕ ↦ X (k + n)) (n + 1) ≫
      F.map (S.map (homOfLE (Nat.le_succ n)).op) = _
    rw [show S.map (homOfLE (Nat.le_succ n)).op =
      (homOfLE (Nat.le_succ (k + n))).op from Subsingleton.elim _ _]
    simp [F]
  change Triangle.mk _ (𝟙 _ - _) δ' ∈ distTriang D at hδ'
  rw [hs] at hδ'
  have he : Fan.IsLimit.lift (productIsProduct (fun n : ℕ ↦ X (k + n)))
      (fun n ↦ (c.whisker S).π.app ⟨n⟩) =
      Pi.lift (fun n : ℕ ↦ p ≫ Pi.π X (k + n)) := by
    apply Pi.hom_ext
    intro n
    rw [Pi.lift_π]
    exact Fan.IsLimit.fac (productIsProduct (fun n : ℕ ↦ X (k + n))) _ n
  rw [he] at hδ'
  exact hδ'

end CategoryTheory
