/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.VerdierDualFinite

/-!
# The Verdier dual on a finite reduced scheme in every degree

On a finite reduced `k₀`-scheme `Z` the Verdier dual `𝔻_Z` is t-exact
(`AlgebraicGeometry.WeilComplex.isGE_isLE_verdierDual_of_isFinite`), so it exchanges the
cohomology sheaves of degrees `n` and `-n`: `𝓗⁻ⁿ(𝔻_Z A) ≅ 𝓗⁰(𝔻_Z (𝓗ⁿ(A)[0]))` for every Weil
complex `A` on `Z`. For `n = 1` this is
`AlgebraicGeometry.WeilComplex.nonempty_homologySheaf_neg_one_verdierDual_iso`.

## Main statements

- `AlgebraicGeometry.WeilComplex.nonempty_homologySheaf_neg_verdierDual_iso`:
  `𝓗⁻ⁿ(𝔻_Z A) ≅ 𝓗⁰(𝔻_Z (𝓗ⁿ(A)[0]))`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite Pretriangulated Triangulated

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

namespace WeilComplex

variable {Z : Scheme.{u}} [Z.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (Z ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Z ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Z ↘ Spec (CommRingCat.of k₀))]
  [IsFinite (Z ↘ Spec (CommRingCat.of k₀))] [IsReduced Z]
  [HasUpperShriek k₀ l (Z ↘ Spec (CommRingCat.of k₀))]

open Pretriangulated.Opposite

/-- **`𝔻_Z` in degree `-n`**: on a finite reduced `k₀`-scheme `Z`,
`𝓗⁻ⁿ(𝔻_Z A) ≅ 𝓗⁰(𝔻_Z (𝓗ⁿ(A)[0]))` for every Weil complex `A`. The truncation triangles
`τ_{≤ n-1} A ⟶ A ⟶ τ_{≥ n} A ⟶` and `τ_{≤ n} τ_{≥ n} A ⟶ τ_{≥ n} A ⟶ τ_{≥ n+1} τ_{≥ n} A ⟶`,
dualized, identify `𝓗⁻ⁿ(𝔻_Z A)` with `𝓗⁻ⁿ(𝔻_Z(𝓗ⁿ(A)[-n])) = 𝓗⁰(𝔻_Z(𝓗ⁿ(A)[0]))`, `𝔻_Z` being
t-exact. -/
theorem nonempty_homologySheaf_neg_verdierDual_iso (A : WeilComplex k₀ l Z) (n : ℤ) :
    Nonempty ((homologySheaf (-n)).obj ((verdierDual k₀ l Z).obj (op A)) ≅
      (homologySheaf 0).obj ((verdierDual k₀ l Z).obj
        (op (WeilSheaf.toComplex.obj ((homologySheaf n).obj A))))) := by
  obtain ⟨_, _⟩ := exists_commShift_isTriangulated_verdierDual k₀ l Z
  set t := tStructure k₀ l Z
  -- the truncation `τ_{≤ n-1} A ⟶ A ⟶ B = τ_{≥ n} A ⟶`
  set T₁ := (t.triangleLEGE (n - 1) n (by lia)).obj A
  have hT₁ : T₁ ∈ distTriang _ := t.triangleLEGE_distinguished _ _ _ A
  have h₁ : t.IsLE T₁.obj₁ (n - 1) := inferInstanceAs (t.IsLE ((t.truncLE (n - 1)).obj A) (n - 1))
  have : t.IsGE T₁.obj₃ n := inferInstanceAs (t.IsGE ((t.truncGE n).obj A) n)
  have hD₁ : t.IsGE ((verdierDual k₀ l Z).obj (op T₁.obj₁)) (-(n - 1)) :=
    isGE_verdierDual_of_isLE T₁.obj₁ (n - 1)
  have i₁ := _root_.DerivedCategory.isIso_homologyMap_mor₁ _
    ((objectProperty k₀ l Z).ι.map_distinguished _
      (verdierDual_mapTriangle_distinguished T₁ hT₁)) (-n - 1) (-n) (by lia)
    (isZero_homologyFunctor_of_isGE ((verdierDual k₀ l Z).obj (op T₁.obj₁)) (-(n - 1)) (-n - 1)
      (by lia) hD₁)
    (isZero_homologyFunctor_of_isGE ((verdierDual k₀ l Z).obj (op T₁.obj₁)) (-(n - 1)) (-n)
      (by lia) hD₁)
  let E₁ : (homologySheaf (-n)).obj ((verdierDual k₀ l Z).obj (op T₁.obj₃)) ≅
      (homologySheaf (-n)).obj ((verdierDual k₀ l Z).obj (op A)) :=
    ObjectProperty.isoMk _ (@asIso _ _ _ _ _ i₁)
  -- the truncation `C = τ_{≤ n} B ⟶ B ⟶ τ_{≥ n+1} B ⟶`
  set T₂ := (t.triangleLEGE n (n + 1) (by lia)).obj T₁.obj₃
  have hT₂ : T₂ ∈ distTriang _ := t.triangleLEGE_distinguished _ _ _ _
  have : t.IsLE T₂.obj₁ n := inferInstanceAs (t.IsLE ((t.truncLE n).obj T₁.obj₃) n)
  have : t.IsGE T₂.obj₁ n := inferInstanceAs (t.IsGE ((t.truncLE n).obj T₁.obj₃) n)
  have h₃ : t.IsGE T₂.obj₃ (n + 1) :=
    inferInstanceAs (t.IsGE ((t.truncGE (n + 1)).obj T₁.obj₃) (n + 1))
  have hD₃ : t.IsLE ((verdierDual k₀ l Z).obj (op T₂.obj₃)) (-(n + 1)) :=
    isLE_verdierDual_of_isGE T₂.obj₃ (n + 1)
  have i₂ := _root_.DerivedCategory.isIso_homologyMap_mor₂ _
    ((objectProperty k₀ l Z).ι.map_distinguished _
      (verdierDual_mapTriangle_distinguished T₂ hT₂)) (-n) (-n + 1) (by lia)
    (isZero_homologyFunctor_of_isLE ((verdierDual k₀ l Z).obj (op T₂.obj₃)) (-(n + 1)) (-n)
      (by lia) hD₃)
    (isZero_homologyFunctor_of_isLE ((verdierDual k₀ l Z).obj (op T₂.obj₃)) (-(n + 1)) (-n + 1)
      (by lia) hD₃)
  let E₂ : (homologySheaf (-n)).obj ((verdierDual k₀ l Z).obj (op T₁.obj₃)) ≅
      (homologySheaf (-n)).obj ((verdierDual k₀ l Z).obj (op T₂.obj₁)) :=
    ObjectProperty.isoMk _ (@asIso _ _ _ _ _ i₂)
  -- `C ≅ 𝓗ⁿ(C)[-n]`
  obtain ⟨e⟩ := nonempty_iso_shift_toComplex_homologySheaf T₂.obj₁ n
  let E₃ : (homologySheaf (-n)).obj ((verdierDual k₀ l Z).obj (op T₂.obj₁)) ≅
      (homologySheaf 0).obj ((verdierDual k₀ l Z).obj (op (WeilSheaf.toComplex.obj
        ((homologySheaf n).obj T₂.obj₁)))) :=
    (homologySheaf (-n)).mapIso
        ((verdierDual k₀ l Z).mapIso e.symm.op ≪≫ verdierDualShiftIso _ n) ≪≫
      homologySheafShiftIso _ n (-n) 0 (by lia)
  -- `𝓗ⁿ(C) ≅ 𝓗ⁿ(B) ≅ 𝓗ⁿ(A)`
  have i₃ := _root_.DerivedCategory.isIso_homologyMap_mor₁ _
    ((objectProperty k₀ l Z).ι.map_distinguished _ hT₂) (n - 1) n
    (by lia) (isZero_homologyFunctor_of_isGE T₂.obj₃ (n + 1) (n - 1) (by lia) h₃)
    (isZero_homologyFunctor_of_isGE T₂.obj₃ (n + 1) n (by lia) h₃)
  have i₄ := _root_.DerivedCategory.isIso_homologyMap_mor₂ _
    ((objectProperty k₀ l Z).ι.map_distinguished _ hT₁) n (n + 1)
    (by lia) (isZero_homologyFunctor_of_isLE T₁.obj₁ (n - 1) n (by lia) h₁)
    (isZero_homologyFunctor_of_isLE T₁.obj₁ (n - 1) (n + 1) (by lia) h₁)
  let e₃ : (homologySheaf n).obj T₂.obj₁ ≅ (homologySheaf n).obj T₁.obj₃ :=
    ObjectProperty.isoMk _ (@asIso _ _ _ _ _ i₃)
  let e₄ : (homologySheaf n).obj A ≅ (homologySheaf n).obj T₁.obj₃ :=
    ObjectProperty.isoMk _ (@asIso _ _ _ _ _ i₄)
  let eH : (homologySheaf n).obj T₂.obj₁ ≅ (homologySheaf n).obj A := e₃ ≪≫ e₄.symm
  exact ⟨E₁.symm ≪≫ E₂ ≪≫ E₃ ≪≫
    (homologySheaf 0).mapIso ((verdierDual k₀ l Z).mapIso (WeilSheaf.toComplex.mapIso eH.symm).op)⟩

end WeilComplex

end AlgebraicGeometry
