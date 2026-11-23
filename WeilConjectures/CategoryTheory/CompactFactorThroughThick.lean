/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.CompactObject
public import Mathlib.CategoryTheory.Triangulated.Generators
import WeilConjectures.CategoryTheory.CompactCoproductFiniteThickSupport
import WeilConjectures.CategoryTheory.CompactTriangleConnectingApproximation

/-!
# Compact maps into generator stages factor through finite thick closure

Source: Stacks Project, Derived Categories, Tag 09SP, with the stage notation of
Tag 09SN.
-/

@[expose] public section

universe w v u

open CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace CategoryTheory

/-- A map from a compact object into any finite generator stage factors through the
thick closure of a finite direct sum of the compact objects. No generation assumption
is imposed. Source: Stacks Project, Tag 09SP.
-/
theorem compact_factorThrough_thickClosure
    {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
    [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive]
    [Pretriangulated C] [IsTriangulated C] [HasCoproducts.{w} C]
    {I : Type w} (E : I → C) (hcompact : ∀ i : I, IsCompactObject (E i))
    (X : ℕ → C) (t : ∀ n : ℕ, X n ⟶ X (n + 1))
    (hinitial : ∃ (J : Type w) (i : J → I) (m : J → ℤ),
      Nonempty (X 0 ≅ ∐ fun j : J ↦ (E (i j))⟦m j⟧))
    (hstages : ∃ (Z : ℕ → C) (a : ∀ n : ℕ, Z n ⟶ X n)
        (b : ∀ n : ℕ, X (n + 1) ⟶ (Z n)⟦(1 : ℤ)⟧),
      (∀ n : ℕ, ∃ (J : Type w) (i : J → I) (m : J → ℤ),
        Nonempty (Z n ≅ ∐ fun j : J ↦ (E (i j))⟦m j⟧)) ∧
      ∀ n : ℕ, Triangle.mk (a n) (t n) (b n) ∈ distTriang C)
    (C₀ : C) (hC₀ : IsCompactObject C₀) (n : ℕ) (f : C₀ ⟶ X n) :
    ∃ (S : Finset I) (Q : C) (a : C₀ ⟶ Q) (b : Q ⟶ X n),
      (ObjectProperty.singleton (∐ fun i : {i : I // i ∈ S} ↦ E i.val)).triangEnvelope Q ∧
        a ≫ b = f := by
  classical
  obtain ⟨Z, z, δ, hZ, hdist⟩ := hstages
  induction n generalizing C₀ with
  | zero =>
      obtain ⟨J, i, m, ⟨e⟩⟩ := hinitial
      obtain ⟨S, Q, a, b, hQ, hab⟩ :=
        compact_coproduct_finite_thick_support E i m C₀ hC₀ (f ≫ e.hom)
      refine ⟨S, Q, a, b ≫ e.inv, hQ, ?_⟩
      rw [← Category.assoc, hab, Category.assoc, e.hom_inv_id, Category.comp_id]
  | succ n ih =>
      let T := Triangle.mk (z n) (t n) (δ n)
      obtain ⟨S, Q, a, b, hQ, hab⟩ :=
        compact_triangle_connecting_approximation E hcompact T (hdist n) (hZ n)
          (fun K hK g ↦ ih K hK g) C₀ hC₀ f
      change Q ⟶ X (n + 1) at b
      have hdiff : (f - a ≫ b) ≫ T.mor₃ = 0 := by
        rw [Preadditive.sub_comp, hab, sub_self]
      obtain ⟨g, hg⟩ := T.coyoneda_exact₃ (hdist n) (f - a ≫ b) hdiff
      obtain ⟨S', Q', a', b', hQ', ha'b'⟩ := ih C₀ hC₀ g
      let U := S ∪ S'
      let P := (ObjectProperty.singleton
        (∐ fun i : {i : I // i ∈ U} ↦ E i.val)).triangEnvelope
      have hQU : P Q := finite_thick_mono E Finset.subset_union_left Q hQ
      have hQ'U : P Q' := finite_thick_mono E Finset.subset_union_right Q' hQ'
      have hsum : P (Q ⊞ Q') := by
        exact P.prop_of_iso (biprod.isoProd Q Q').symm (P.prop_prod Q Q' hQU hQ'U)
      refine ⟨U, Q ⊞ Q', biprod.lift a a', biprod.desc b (b' ≫ t n), hsum, ?_⟩
      rw [biprod.lift_desc, ← Category.assoc a' b', ha'b']
      change f - a ≫ b = g ≫ t n at hg
      change a ≫ b + g ≫ t n = f
      rw [← hg]
      exact add_sub_cancel _ _

end CategoryTheory
