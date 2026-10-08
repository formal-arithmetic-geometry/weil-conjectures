/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Charts
public import WeilConjectures.Compactification.Defs

/-!
# Affine space is compactified by projective space

The relative affine space `𝔸(n; S) ⟶ S` in finitely many variables admits a compactification:
it is the standard open chart `D₊(T_none)` of the projective space `ℙ(Option n; S)`, which is
proper over `S`. This is what makes the exceptional inverse image `Rπ^!` along the projection
of affine space, and of the trivial vector bundles of the purity chapter, available.

## Main definitions

- `AlgebraicGeometry.AffineSpace.reindexIso`: the isomorphism `𝔸(n; S) ≅ 𝔸(m; S)` induced by a
  bijection `m ≃ n` of the coordinates.
- `AlgebraicGeometry.AffineSpace.compactification`: the compactification
  `𝔸(n; S) ↪ ℙ(Option n; S) ⟶ S`.

## Main statements

- `AlgebraicGeometry.AffineSpace.hasCompactification`
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

namespace AffineSpace

variable {m n : Type u} (S : Scheme.{u})

/-- Relabelling the coordinates along a bijection `e : m ≃ n` is an isomorphism of affine
spaces `𝔸(n; S) ≅ 𝔸(m; S)` over `S`. -/
noncomputable def reindexIso (e : m ≃ n) : 𝔸(n; S) ≅ 𝔸(m; S) where
  hom := reindex e S
  inv := reindex e.symm S
  hom_inv_id := by apply hom_ext <;> simp
  inv_hom_id := by apply hom_ext <;> simp

/-- The coordinates of `ℙ(Option n; S)` other than `none` are the coordinates of `𝔸(n; S)`. -/
def optionSubtypeNeNoneEquiv (n : Type u) : {j : Option n // j ≠ none} ≃ n where
  toFun j := j.1.get (Option.ne_none_iff_isSome.mp j.2)
  invFun i := ⟨some i, Option.some_ne_none i⟩
  left_inv j := Subtype.ext (by simp)
  right_inv i := by simp

/-- The compactification `𝔸(n; S) ↪ ℙ(Option n; S) ⟶ S` of relative affine space: the open
immersion is the inverse of the standard chart `D₊(T_none) ≅ 𝔸(n; S)`, and projective space is
proper over `S`. -/
noncomputable def compactification [Finite n] : Compactification (𝔸(n; S) ↘ S) where
  Z := ℙ(Option n; S)
  g := ℙ(Option n; S) ↘ S
  i := (reindexIso S (optionSubtypeNeNoneEquiv n)).hom ≫
    (ProjectiveSpace.standardOpenIso (Option n) S none).inv ≫
      (ProjectiveSpace.standardOpen (Option n) S none).ι
  comm := by
    simp only [Category.assoc, ProjectiveSpace.standardOpenIso_inv_ι_over]
    exact (reindex_over _ S).symm
  isProper := inferInstance
  isOpenImmersion := inferInstance

/-- Relative affine space in finitely many variables admits a compactification. -/
instance hasCompactification [Finite n] : HasCompactification (𝔸(n; S) ↘ S) :=
  (compactification S).hasCompactification

end AffineSpace

end AlgebraicGeometry
