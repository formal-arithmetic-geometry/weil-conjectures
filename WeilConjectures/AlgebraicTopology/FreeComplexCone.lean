/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex

/-!
# Cones in free complexes of simplicial sets

Let `Free : Type u ⥤ A` be any functor to a preadditive category, `r : S ⟶ S'` a morphism of
simplicial sets, and suppose that on a set `F` of `(n + 1)`-simplices of `S` we are given a
"cone" `h₁ : S _⦋n + 1⦌ → S' _⦋n + 2⦌` such that `d₀ (h₁ τ) = r τ` and
`d_{i + 1} (h₁ τ) = h₀ (d_i τ)` for `τ ∈ F`. Then the alternating face map complexes satisfy the
cone identity `d ∘ h₁ = r - h₀ ∘ d` on the free object on `F`. Consequently, the image under `r`
of every cycle supported in `F` is a boundary. We also treat degree `0`, where the cone is taken
relative to an augmentation.

## Main results

- `AlgebraicTopology.FreeComplexCone.map_comp_d_succ`, `map_comp_d_zero`: cone identities.
- `AlgebraicTopology.FreeComplexCone.d_map_succ`, `d_map_zero`: elementwise consequences.
-/

@[expose] public section

universe w' v' u' u

open CategoryTheory Opposite Simplicial

namespace AlgebraicTopology.FreeComplexCone

variable {A : Type u'} [Category.{v'} A] [Preadditive A] (Free : Type u ⥤ A)
  {S S' : SimplicialObject (Type u)} (r : S ⟶ S')

omit [Preadditive A] in
lemma δ_comp_eq {X : SimplicialObject (Type u)} {m : ℕ} (i : Fin (m + 2)) :
    SimplicialObject.δ (C := A) (X ⋙ Free) i = Free.map (X.δ i) := rfl

/-- The cone identity in positive degrees. -/
lemma map_comp_d_succ {n : ℕ} (F : Set (S _⦋n + 1⦌)) (h₁ : S _⦋n + 1⦌ → S' _⦋n + 2⦌)
    (h₀ : S _⦋n⦌ → S' _⦋n + 1⦌)
    (hc₀ : ∀ τ ∈ F, S'.δ 0 (h₁ τ) = r.app _ τ)
    (hc : ∀ τ ∈ F, ∀ i : Fin (n + 2), S'.δ i.succ (h₁ τ) = h₀ (S.δ i τ)) :
    Free.map (↾(Subtype.val : F → _)) ≫ Free.map (↾h₁) ≫
        ((alternatingFaceMapComplex A).obj (S' ⋙ Free)).d (n + 2) (n + 1) =
      Free.map (↾(Subtype.val : F → _)) ≫ Free.map (r.app _) -
        Free.map (↾(Subtype.val : F → _)) ≫
          ((alternatingFaceMapComplex A).obj (S ⋙ Free)).d (n + 1) n ≫ Free.map (↾h₀) := by
  have h0' : ↾(Subtype.val : F → _) ≫ ↾h₁ ≫ S'.δ 0 = ↾(Subtype.val : F → _) ≫ r.app _ := by
    ext ⟨τ, hτ⟩
    exact hc₀ τ hτ
  have hs' : ∀ i : Fin (n + 2), ↾(Subtype.val : F → _) ≫ ↾h₁ ≫ S'.δ i.succ =
      ↾(Subtype.val : F → _) ≫ S.δ i ≫ ↾h₀ := by
    intro i
    ext ⟨τ, hτ⟩
    exact hc τ hτ i
  rw [alternatingFaceMapComplex_obj_d, alternatingFaceMapComplex_obj_d,
    AlternatingFaceMapComplex.objD, AlternatingFaceMapComplex.objD, Fin.sum_univ_succ]
  simp only [Preadditive.comp_add, Preadditive.comp_sum, Preadditive.sum_comp,
    Preadditive.comp_zsmul, Preadditive.zsmul_comp, δ_comp_eq, ← Functor.map_comp, h0', hs',
    Fin.val_zero, pow_zero, one_smul, Fin.val_succ, pow_succ, mul_neg, mul_one, neg_smul,
    Finset.sum_neg_distrib, sub_eq_add_neg]

/-- The cone identity in degree `0`, relative to an augmentation `e` and a vertex map `c`. -/
lemma map_comp_d_zero (F : Set (S _⦋0⦌)) (h₀ : S _⦋0⦌ → S' _⦋1⦌) {P : Type u}
    (e : S _⦋0⦌ → P) (c : P → S' _⦋0⦌)
    (hc₀ : ∀ τ ∈ F, S'.δ 0 (h₀ τ) = r.app _ τ)
    (hc₁ : ∀ τ ∈ F, S'.δ 1 (h₀ τ) = c (e τ)) :
    Free.map (↾(Subtype.val : F → _)) ≫ Free.map (↾h₀) ≫
        ((alternatingFaceMapComplex A).obj (S' ⋙ Free)).d 1 0 =
      Free.map (↾(Subtype.val : F → _)) ≫ Free.map (r.app _) -
        Free.map (↾(Subtype.val : F → _)) ≫ Free.map (↾e) ≫ Free.map (↾c) := by
  have h0' : ↾(Subtype.val : F → _) ≫ ↾h₀ ≫ S'.δ 0 = ↾(Subtype.val : F → _) ≫ r.app _ := by
    ext ⟨τ, hτ⟩
    exact hc₀ τ hτ
  have h1' : ↾(Subtype.val : F → _) ≫ ↾h₀ ≫ S'.δ 1 =
      ↾(Subtype.val : F → _) ≫ ↾e ≫ ↾c := by
    ext ⟨τ, hτ⟩
    exact hc₁ τ hτ
  rw [show ((alternatingFaceMapComplex A).obj (S' ⋙ Free)).d 1 0 =
      AlternatingFaceMapComplex.objD (S' ⋙ Free) 0 from alternatingFaceMapComplex_obj_d _ 0,
    AlternatingFaceMapComplex.objD, Fin.sum_univ_two]
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul, neg_smul,
    Preadditive.comp_add, Preadditive.comp_neg, δ_comp_eq, ← Functor.map_comp, h0', h1',
    sub_eq_add_neg]
variable {FA : A → A → Type*} {CA : A → Type w'} [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)]
  [ConcreteCategory.{w'} A FA] [∀ X, AddCommGroup (CA X)]
  [∀ X Y, AddMonoidHomClass (FA X Y) (CA X) (CA Y)]

/-- If `z` is a cycle supported on `F` and `h₁` is a cone on `F`, then `r z` is the boundary
of `h₁ z`. -/
lemma d_map_succ
    (hsub : ∀ {X Y : A} (f g : X ⟶ Y) (x : ToType X), (f - g) x = f x - g x)
    {n : ℕ} (F : Set (S _⦋n + 1⦌)) (h₁ : S _⦋n + 1⦌ → S' _⦋n + 2⦌)
    (h₀ : S _⦋n⦌ → S' _⦋n + 1⦌)
    (hc₀ : ∀ τ ∈ F, S'.δ 0 (h₁ τ) = r.app _ τ)
    (hc : ∀ τ ∈ F, ∀ i : Fin (n + 2), S'.δ i.succ (h₁ τ) = h₀ (S.δ i τ))
    (z : ToType (Free.obj (S _⦋n + 1⦌)))
    (hz : z ∈ Set.range (Free.map (↾(Subtype.val : F → _))))
    (hd : ((alternatingFaceMapComplex A).obj (S ⋙ Free)).d (n + 1) n z = 0) :
    ((alternatingFaceMapComplex A).obj (S' ⋙ Free)).d (n + 2) (n + 1) (Free.map (↾h₁) z) =
      Free.map (r.app _) z := by
  obtain ⟨z, rfl⟩ := hz
  have := congrArg (fun f ↦ f z) (map_comp_d_succ Free r F h₁ h₀ hc₀ hc)
  simp only [hsub, ConcreteCategory.comp_apply] at this
  rw [hd, map_zero, sub_zero] at this
  exact this

/-- If `z` is a degree `0` chain with vanishing augmentation, supported on `F`, and `h₀` is
a cone on `F` with vertex given by `c`, then `r z` is the boundary of `h₀ z`. -/
lemma d_map_zero
    (hsub : ∀ {X Y : A} (f g : X ⟶ Y) (x : ToType X), (f - g) x = f x - g x)
    (F : Set (S _⦋0⦌)) (h₀ : S _⦋0⦌ → S' _⦋1⦌) {P : Type u}
    (e : S _⦋0⦌ → P) (c : P → S' _⦋0⦌)
    (hc₀ : ∀ τ ∈ F, S'.δ 0 (h₀ τ) = r.app _ τ)
    (hc₁ : ∀ τ ∈ F, S'.δ 1 (h₀ τ) = c (e τ))
    (z : ToType (Free.obj (S _⦋0⦌)))
    (hz : z ∈ Set.range (Free.map (↾(Subtype.val : F → _))))
    (hd : Free.map (↾e) z = 0) :
    ((alternatingFaceMapComplex A).obj (S' ⋙ Free)).d 1 0 (Free.map (↾h₀) z) =
      Free.map (r.app _) z := by
  obtain ⟨z, rfl⟩ := hz
  have := congrArg (fun f ↦ f z) (map_comp_d_zero Free r F h₀ e c hc₀ hc₁)
  simp only [hsub, ConcreteCategory.comp_apply] at this
  rw [hd, map_zero, sub_zero] at this
  exact this

end AlgebraicTopology.FreeComplexCone
