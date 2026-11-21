/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Cohomology.Kunneth
public import WeilConjectures.AlgebraicGeometry.Cohomology.Affine.LerayNatural
public import WeilConjectures.AlgebraicGeometry.GlobalSectionsBijective

/-!
# `H¹` of the structure sheaf of a product

Let `X`, `Y` be proper schemes over a field `K` with `H⁰(X, 𝒪_X) = H⁰(Y, 𝒪_Y) = K`, and let
`x`, `y` be `K`-points of `X`, `Y`. Restriction to the slices `X × {y}` and `{x} × Y` identifies
`H¹(X ×_K Y, 𝒪)` with `H¹(X, 𝒪_X) ⊕ H¹(Y, 𝒪_Y)`.

## Main statements

- `AlgebraicGeometry.Scheme.Modules.bijective_H_one_unit_prod`

## Implementation details

The restriction of `H¹(X ×_K Y, 𝒪)` to the slice `i : X ⟶ X ×_K Y` is spelled as the map
`H¹(X ×_K Y, 𝒪) ⟶ H¹(X ×_K Y, i_* 𝒪_X)` induced by `i^♯ : 𝒪 ⟶ i_* 𝒪_X`. Its target is
`H¹(X, 𝒪_X)`, since `i` is affine
(`AlgebraicGeometry.Scheme.Modules.nonempty_cohomologyFunctor_iso_pushforward_of_isAffineHom`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Modules

variable {K : Type u} [Field K] {X Y : Scheme.{u}} [X.Over (Spec (.of K))]
  [Y.Over (Spec (.of K))]

/-- The slice `X × {y} ⟶ X ×_K Y` at a `K`-point `y` of `Y`. -/
noncomputable def sliceLeft (y : Spec (.of K) ⟶ Y) (hy : y ≫ Y ↘ Spec (.of K) = 𝟙 _) :
    X ⟶ Limits.pullback (X ↘ Spec (.of K)) (Y ↘ Spec (.of K)) :=
  pullback.lift (𝟙 X) (X ↘ Spec (.of K) ≫ y) (by rw [Category.assoc, hy]; simp)

/-- The slice `{x} × Y ⟶ X ×_K Y` at a `K`-point `x` of `X`. -/
noncomputable def sliceRight (x : Spec (.of K) ⟶ X) (hx : x ≫ X ↘ Spec (.of K) = 𝟙 _) :
    Y ⟶ Limits.pullback (X ↘ Spec (.of K)) (Y ↘ Spec (.of K)) :=
  pullback.lift (Y ↘ Spec (.of K) ≫ x) (𝟙 Y) (by rw [Category.assoc, hx]; simp)

/-- **`H¹` of the structure sheaf of a product.** Let `X`, `Y` be proper over a field `K` with
`H⁰(X, 𝒪_X) = H⁰(Y, 𝒪_Y) = K`, and let `x`, `y` be `K`-points of `X`, `Y`. Then restriction to
the slices `X × {y}` and `{x} × Y` is a bijection
`H¹(X ×_K Y, 𝒪) → H¹(X ×_K Y, i_* 𝒪_X) × H¹(X ×_K Y, j_* 𝒪_Y)`, where `i`, `j` are the slice
inclusions. -/
theorem bijective_H_one_unit_prod [IsProper (X ↘ Spec (.of K))] [IsProper (Y ↘ Spec (.of K))]
    [GlobalSectionsBijective K X] [GlobalSectionsBijective K Y]
    (x : Spec (.of K) ⟶ X) (hx : x ≫ X ↘ Spec (.of K) = 𝟙 _)
    (y : Spec (.of K) ⟶ Y) (hy : y ≫ Y ↘ Spec (.of K) = 𝟙 _) :
    Function.Bijective fun c : (Modules.unit
        (Limits.pullback (X ↘ Spec (.of K)) (Y ↘ Spec (.of K)))).H 1 ↦
      (H.map (SheafOfModules.unitToPushforwardObjUnit (sliceLeft y hy).toRingCatSheafHom) 1 c,
        H.map (SheafOfModules.unitToPushforwardObjUnit (sliceRight x hx).toRingCatSheafHom) 1 c) :=
  sorry

end AlgebraicGeometry.Scheme.Modules
