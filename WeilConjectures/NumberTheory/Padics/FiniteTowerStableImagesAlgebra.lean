/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import Mathlib.Algebra.Category.ModuleCat.Limits
public import WeilConjectures.Algebra.Category.ModuleCat.StableImageTower
import Mathlib.CategoryTheory.CofilteredSystem
import WeilConjectures.Algebra.Category.ModuleCat.TowerLimitInducedMaps

/-!
# Stable images of finite coefficient-module towers

The algebraic half of `lem-zl-finite-tower-stable-images`: in a tower of finite modules
over the coefficient integers, the images stabilise, the limit projections have the stable
images as ranges, the stable-image transitions are surjective, and each projection induces
`lim F / ker p_n ≃ B_n`. No surjectivity of the original transitions is assumed.
(blueprint: lem-zl-finite-tower-stable-images-algebra).
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits Opposite

namespace Padic

/-- The algebraic stable-image assertions for a finite coefficient-module tower.

Source: latest blueprint, `prop-zl-smooth-proper-relative-purity`, proof, Step 1,
Passage to the limit; Stacks Project Tags 0596 and 0597
(blueprint: lem-zl-finite-tower-stable-images-algebra).

Proof (the node's steps; `t_{m,n}` the transition, `B_n` the stable image, `p_n` the
projection):
1. Finite modules are Artinian, so the decreasing images `im t_{m,n}` stabilise and equal
   `B_n` for large `m` (`ModuleCat.exists_stableImage_eq_towerRange`).
2. For `b ∈ B_n`, take `k` beyond the stabilisation indices of `n` and `n + 1` and
   `b = t_{k,n}(z)`; then `t_{k,n+1}(z) ∈ B_{n+1}` maps to `b`. By induction every composite
   restricted transition `B_m → B_n` is surjective.
3. `p_n(x) = t_{m,n}(p_m(x))` gives `im p_n ≤ B_n`. Conversely the `B_m` form a system of
   nonempty finite sets with surjective transitions, so its sections surject onto `B_n`
   (König; Stacks 0597; `Functor.eval_section_surjective_of_surjective`); a section is a
   compatible family, i.e. an element of the limit (`towerLimitMk`) lying over `b`.
4. The first isomorphism theorem `lim F / ker p_n ≃ im p_n = B_n`. -/
theorem finiteTower_stable_images_algebra
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E]
    (F : ℕᵒᵖ ⥤ ModuleCat.{v} (coefficientExtensionIntegers l E))
    [∀ n : ℕ, Finite (F.obj (op n))] :
    (∀ n : ℕ, ∃ (m₀ : ℕ) (hn : n ≤ m₀), ∀ (m : ℕ) (hm : m₀ ≤ m),
      ModuleCat.towerRange F (hn.trans hm) = ModuleCat.stableImage F n) ∧
    (∀ n : ℕ, LinearMap.range (limit.π F (op n)).hom = ModuleCat.stableImage F n) ∧
    (∀ n : ℕ, Function.Surjective
      ((ModuleCat.stableImageTower F).map (homOfLE (Nat.le_succ n)).op)) ∧
    (∀ n : ℕ, ∃ e : ((ModuleCat.carrier (limit F)) ⧸
      LinearMap.ker (limit.π F (op n)).hom) ≃ₗ[
        coefficientExtensionIntegers l E] ModuleCat.stableImage F n,
      ∀ x : (ModuleCat.carrier (limit F)),
        (e (Submodule.Quotient.mk x) : F.obj (op n)) = (limit.π F (op n)) x) := by
  have hart := fun n : ℕ ↦ isArtinian_of_finite (R := coefficientExtensionIntegers l E)
    (M := F.obj (op n))
  -- Step 1: stabilization.
  have h1 : ∀ n : ℕ, ∃ (m₀ : ℕ) (hn : n ≤ m₀), ∀ (m : ℕ) (hm : m₀ ≤ m),
      ModuleCat.towerRange F (hn.trans hm) = ModuleCat.stableImage F n := fun n ↦ by
    obtain ⟨N, hN, h⟩ := ModuleCat.exists_stableImage_eq_towerRange F n
    exact ⟨N, hN, fun m hm ↦ (h m hm).symm⟩
  -- Step 2: adjacent stable-image transitions are surjective.
  have h3 : ∀ n : ℕ, Function.Surjective
      ((ModuleCat.stableImageTower F).map (homOfLE (Nat.le_succ n)).op) := by
    rintro n ⟨y, hy⟩
    obtain ⟨N₁, hN₁, h₁⟩ := h1 n
    obtain ⟨N₂, hN₂, h₂⟩ := h1 (n + 1)
    have hM₂ : N₂ ≤ max N₁ N₂ := le_max_right _ _
    rw [← h₁ (max N₁ N₂) (le_max_left _ _)] at hy
    obtain ⟨z, rfl⟩ := hy
    have hz : (F.map (homOfLE (hN₂.trans hM₂)).op).hom z ∈ ModuleCat.stableImage F (n + 1) := by
      rw [← h₂ _ hM₂]
      exact ⟨z, rfl⟩
    exact ⟨⟨_, hz⟩, Subtype.ext (ModuleCat.tower_map_hom_map_hom F n.le_succ _ z)⟩
  -- All stable-image transitions are surjective.
  have hall : ∀ {n m : ℕ} (h : n ≤ m), Function.Surjective
      ((ModuleCat.stableImageTower F).map (homOfLE h).op) := by
    intro n m h
    induction m, h using Nat.le_induction with
    | base =>
      rw [show (homOfLE (le_refl n)).op = 𝟙 (op n) from
        Quiver.Hom.unop_inj (Subsingleton.elim _ _), CategoryTheory.Functor.map_id]
      exact fun x ↦ ⟨x, rfl⟩
    | succ m hnm ih =>
      rw [← homOfLE_comp hnm (Nat.le_add_right m 1), op_comp, Functor.map_comp]
      intro y
      obtain ⟨z, rfl⟩ := ih y
      obtain ⟨w, rfl⟩ := h3 m z
      exact ⟨w, rfl⟩
  -- Step 3: projection ranges.
  have h2 : ∀ n : ℕ, LinearMap.range (limit.π F (op n)).hom = ModuleCat.stableImage F n := by
    intro n
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      refine Submodule.mem_iInf _ |>.2 fun m ↦ Submodule.mem_iInf _ |>.2 fun hm ↦ ?_
      exact ⟨limit.π F (op m) x, limit.w_apply F (homOfLE hm).op x⟩
    · intro b hb
      let G := ModuleCat.stableImageTower F ⋙ forget _
      have : ∀ j, Finite (G.obj j) := fun j ↦
        inferInstanceAs (Finite (ModuleCat.stableImage F j.unop))
      have : ∀ j, Nonempty (G.obj j) := fun j ↦ ⟨(0 : ModuleCat.stableImage F j.unop)⟩
      have Gsur : ∀ ⦃i j : ℕᵒᵖ⦄ (f : i ⟶ j), Function.Surjective (G.map f) := by
        intro i j f
        rw [nat_op_hom_eq_homOfLE f]
        exact hall _
      obtain ⟨s, hs⟩ := G.eval_section_surjective_of_surjective Gsur (op n)
        (⟨b, hb⟩ : ModuleCat.stableImage F n)
      refine ⟨towerLimitMk (fun k ↦ ((show ModuleCat.stableImage F k from s.val (op k)) :
        F.obj (op k))) fun k ↦ ?_, ?_⟩
      · exact congrArg Subtype.val (s.prop (homOfLE (Nat.le_add_right k 1)).op)
      · rw [limit_π_towerLimitMk]
        exact congrArg Subtype.val hs
  refine ⟨h1, h2, h3, fun n ↦ ?_⟩
  -- Step 4: first isomorphism theorem.
  refine ⟨(LinearMap.quotKerEquivRange (limit.π F (op n)).hom).trans
    (LinearEquiv.ofEq _ _ (h2 n)), fun x ↦ rfl⟩

end Padic
