/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.CompactOfBoundedExt

/-!
# Morphisms out of a bounded above object only see a window of degrees

Let `C` be an abelian category with exact countable products, `P` a class of objects of `C` and
`s` an object of `D(C)` concentrated in degrees `≤ 0` such that `Hom(s, B[q]) = 0` for `B` in
`P` and `q > d`. For `K` with cohomology in `P` and `m : ℤ`, the truncation maps
`K ⟵ τ_{≤ m} K ⟶ τ_{≥ m - d} τ_{≤ m} K` induce bijections

`Hom(s, K[m]) ⟵ Hom(s, (τ_{≤ m} K)[m]) ⟶ Hom(s, (τ_{≥ m - d} τ_{≤ m} K)[m])`

(`DerivedCategory.bijective_comp_truncLEι_shift_and_truncGEπ_shift`).

## Implementation details

The first bijection holds for degree reasons. For the second, `Hom(s, L) = 0` for every `L`
with cohomology in `P` concentrated in degrees `< -d`
(`DerivedCategory.eq_zero_of_isLE_self`): this sharpens
`DerivedCategory.eq_zero_of_isLE` by one degree, using the truncation triangle
`τ_{< -d - 1} L ⟶ L ⟶ τ_{≥ -d - 1} L ⟶`.
-/

@[expose] public section

open CategoryTheory Category Limits Pretriangulated Preadditive

namespace CategoryTheory.Pretriangulated

variable {C : Type*} [Category* C] [Preadditive C]

private lemma bijective_comp_of_bijective_comp_units_smul {s A B : C} (g : A ⟶ B) (ε : ℤˣ)
    (h : Function.Bijective fun f : s ⟶ A ↦ f ≫ (ε • g)) :
    Function.Bijective fun f : s ⟶ A ↦ f ≫ g := by
  have hε : Function.Bijective fun y : s ⟶ B ↦ ε • y :=
    Function.Involutive.bijective fun y ↦ by rw [smul_smul, Int.units_mul_self, one_smul]
  convert hε.comp h using 1
  ext f
  simp [Units.smul_def, smul_smul]

variable [HasZeroObject C] [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C]

/-- For a distinguished triangle `T` and `n : ℤ`, if `s` admits no nonzero morphisms to
`T.obj₃⟦n⟧` and `T.obj₃⟦n⟧⟦-1⟧`, then composition with `T.mor₁⟦n⟧'` is a bijection
`Hom(s, T.obj₁⟦n⟧) ≃ Hom(s, T.obj₂⟦n⟧)`. -/
lemma bijective_comp_shift_map_mor₁ (T : Triangle C) (hT : T ∈ distTriang C) (n : ℤ) (s : C)
    (h₃ : ∀ f : s ⟶ T.obj₃⟦n⟧, f = 0) (h₃' : ∀ f : s ⟶ T.obj₃⟦n⟧⟦(-1 : ℤ)⟧, f = 0) :
    Function.Bijective fun f : s ⟶ T.obj₁⟦n⟧ ↦ f ≫ T.mor₁⟦n⟧' :=
  bijective_comp_of_bijective_comp_units_smul _ n.negOnePow
    (bijective_comp_mor₁ _ (Triangle.shift_distinguished T hT n) s h₃ h₃')

/-- For a distinguished triangle `T` and `n : ℤ`, if `s` admits no nonzero morphisms to
`T.obj₁⟦n⟧` and `T.obj₁⟦n⟧⟦1⟧`, then composition with `T.mor₂⟦n⟧'` is a bijection
`Hom(s, T.obj₂⟦n⟧) ≃ Hom(s, T.obj₃⟦n⟧)`. -/
lemma bijective_comp_shift_map_mor₂ (T : Triangle C) (hT : T ∈ distTriang C) (n : ℤ) (s : C)
    (h₁ : ∀ f : s ⟶ T.obj₁⟦n⟧, f = 0) (h₁' : ∀ f : s ⟶ T.obj₁⟦n⟧⟦(1 : ℤ)⟧, f = 0) :
    Function.Bijective fun f : s ⟶ T.obj₂⟦n⟧ ↦ f ≫ T.mor₂⟦n⟧' :=
  bijective_comp_of_bijective_comp_units_smul _ n.negOnePow
    (bijective_comp_mor₂ _ (Triangle.shift_distinguished T hT n) s h₁ h₁')

end CategoryTheory.Pretriangulated

namespace DerivedCategory

open TStructure (t)

variable {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]
  [Abelian.HasKInjectiveResolutions C] [HasLimitsOfShape (Discrete ℕ) C]
  [HasExactLimitsOfShape (Discrete ℕ) C] {P : ObjectProperty C} [P.ContainsZero]
  [P.IsClosedUnderIsomorphisms]

/-- If `Hom(s, B[-n]) = 0` for `B` in `P` and `n ≤ N`, then `Hom(s, L) = 0` for every `L` with
cohomology in `P` in degrees `≤ N`. -/
lemma eq_zero_of_isLE_self {s : DerivedCategory C} (N : ℤ)
    (hvan : ∀ B, P B → ∀ n ≤ N, ∀ f : s ⟶ (singleFunctor C n).obj B, f = 0)
    (L : DerivedCategory C) (hL : homologyProperty P L) [L.IsLE N] (f : s ⟶ L) : f = 0 := by
  let T := (t.triangleLTGE N).obj L
  have hT : T ∈ distTriang _ := t.triangleLTGE_distinguished N L
  have : T.obj₁.IsLE (N - 1) := inferInstanceAs (t.IsLE T.obj₁ (N - 1))
  have : T.obj₃.IsGE N := inferInstanceAs (t.IsGE ((t.truncGE N).obj L) N)
  have : t.IsLE L N := ‹L.IsLE N›
  have : T.obj₃.IsLE N := inferInstanceAs (t.IsLE ((t.truncGE N).obj L) N)
  obtain ⟨g, hg⟩ := Triangle.coyoneda_exact₂ _ hT f
    (eq_zero_of_isGE_of_isLE_self N hvan N T.obj₃ (homologyProperty_truncGE hL N) le_rfl _)
  rw [hg, eq_zero_of_isLE N hvan T.obj₁ ((homologyProperty P).prop_of_iso
    ((t.truncLEIsoTruncLT (N - 1) N (by lia)).app L) (homologyProperty_truncLE hL (N - 1))) g,
    zero_comp]

/-- Let `s` be concentrated in degrees `≤ 0` with `Hom(s, B[q]) = 0` for `B` in `P` and `q > d`.
For `K` with cohomology in `P` and `m : ℤ`, the truncation maps
`K ⟵ τ_{≤ m} K ⟶ τ_{≥ m - d} τ_{≤ m} K` induce bijections
`Hom(s, K[m]) ⟵ Hom(s, (τ_{≤ m} K)[m]) ⟶ Hom(s, (τ_{≥ m - d} τ_{≤ m} K)[m])`. -/
theorem bijective_comp_truncLEι_shift_and_truncGEπ_shift {s : DerivedCategory C} [s.IsLE 0]
    (d : ℤ) (hvan : ∀ B, P B → ∀ n < -d, ∀ f : s ⟶ (singleFunctor C n).obj B, f = 0)
    (K : DerivedCategory C) (hK : homologyProperty P K) (m : ℤ) :
    Function.Bijective (fun f : s ⟶ ((t.truncLE m).obj K)⟦m⟧ ↦
        f ≫ ((t.truncLEι m).app K)⟦m⟧') ∧
      Function.Bijective (fun f : s ⟶ ((t.truncLE m).obj K)⟦m⟧ ↦
        f ≫ ((t.truncGEπ (m - d)).app ((t.truncLE m).obj K))⟦m⟧') := by
  have hvan' : ∀ B, P B → ∀ n ≤ -d - 1, ∀ f : s ⟶ (singleFunctor C n).obj B, f = 0 :=
    fun B hB n hn ↦ hvan B hB n (by lia)
  constructor
  · let T := (t.triangleLEGT m).obj K
    have : T.obj₃.IsGE (m + 1) := inferInstanceAs (t.IsGE ((t.truncGT m).obj K) (m + 1))
    have h₃ : (T.obj₃⟦m⟧).IsGE 1 := t.isGE_shift _ (m + 1) m 1 (by lia)
    have h₃' : (T.obj₃⟦m⟧⟦(-1 : ℤ)⟧).IsGE 2 := t.isGE_shift _ 1 (-1) 2 (by lia)
    exact bijective_comp_shift_map_mor₁ T (t.triangleLEGT_distinguished m K) m s
      (fun f ↦ t.zero_of_isLE_of_isGE f 0 1 (by lia) inferInstance h₃)
      (fun f ↦ t.zero_of_isLE_of_isGE f 0 2 (by lia) inferInstance h₃')
  · let K' := (t.truncLE m).obj K
    let T := (t.triangleLTGE (m - d)).obj K'
    have hT₁ : homologyProperty P T.obj₁ := (homologyProperty P).prop_of_iso
      ((t.truncLEIsoTruncLT (m - d - 1) (m - d) (by lia)).app K')
      (homologyProperty_truncLE (homologyProperty_truncLE hK m) (m - d - 1))
    have : T.obj₁.IsLE (m - d - 1) := inferInstanceAs (t.IsLE T.obj₁ (m - d - 1))
    have : (T.obj₁⟦m⟧).IsLE (-d - 1) := t.isLE_shift _ (m - d - 1) m (-d - 1) (by lia)
    have : (T.obj₁⟦m⟧⟦(1 : ℤ)⟧).IsLE (-d - 1) :=
      have := t.isLE_shift (T.obj₁⟦m⟧) (-d - 1) 1 (-d - 2) (by lia)
      t.isLE_of_le _ (-d - 2) (-d - 1) (by lia)
    have hP₁ := (homologyProperty P).le_shift m _ hT₁
    exact bijective_comp_shift_map_mor₂ T (t.triangleLTGE_distinguished (m - d) K') m s
      (eq_zero_of_isLE_self (-d - 1) hvan' _ hP₁)
      (eq_zero_of_isLE_self (-d - 1) hvan' _
        ((homologyProperty P).le_shift 1 _ hP₁))

end DerivedCategory
