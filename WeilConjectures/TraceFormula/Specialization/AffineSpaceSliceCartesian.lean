/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.AffineSpaceSlice

/-!

# The coordinate generic slice is cartesian

For a coordinate `i : Fin (n + 1)`, let `πᵢ : 𝔸ⁿ⁺¹_S ⟶ 𝔸¹_S` be the `i`-th coordinate projection
over `S = Spec k'⟦t⟧` (`AlgebraicGeometry.affineSpaceCoordinate`). The coordinate generic slice
`hᵢ : 𝔸ⁿ_{K⟦t⟧} ⟶ 𝔸ⁿ⁺¹_S` (`AlgebraicGeometry.affineSpaceSlice`) identifies `𝔸ⁿ_{K⟦t⟧}` with the
base change of `πᵢ` along the generic slice `σ : Spec K⟦t⟧ ⟶ 𝔸¹_S`
(`AlgebraicGeometry.traitSlice`): the square
```
𝔸ⁿ_{K⟦t⟧} ──hᵢ──→ 𝔸ⁿ⁺¹_S
    │                │ πᵢ
Spec K⟦t⟧ ───σ───→ 𝔸¹_S
```
is cartesian (`AlgebraicGeometry.isPullback_affineSpaceSlice`).

-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {k' : Type u} [Field k'] {K : Type u} [Field K] [Algebra k' K]

variable (k') in
/-- The `i`-th coordinate projection `πᵢ : 𝔸ⁿ⁺¹_S ⟶ 𝔸¹_S` over `S = Spec k'⟦t⟧`. -/
noncomputable def affineSpaceCoordinate (n : ℕ) (i : Fin (n + 1)) :
    𝔸(ULift.{u} (Fin (n + 1)); trait k') ⟶ 𝔸(ULift.{u} (Fin 1); trait k') :=
  AffineSpace.homOfVector (𝔸(ULift.{u} (Fin (n + 1)); trait k') ↘ trait k')
    fun _ ↦ AffineSpace.coord (trait k') (ULift.up i)

@[reassoc (attr := simp)]
lemma affineSpaceCoordinate_over (n : ℕ) (i : Fin (n + 1)) :
    affineSpaceCoordinate k' n i ≫ 𝔸(ULift.{u} (Fin 1); trait k') ↘ trait k' =
      𝔸(ULift.{u} (Fin (n + 1)); trait k') ↘ trait k' :=
  AffineSpace.homOfVector_over _ _

instance (n : ℕ) (i : Fin (n + 1)) : LocallyOfFiniteType (affineSpaceCoordinate k' n i) :=
  sorry

instance (n : ℕ) (i : Fin (n + 1)) : QuasiCompact (affineSpaceCoordinate k' n i) :=
  sorry

instance (n : ℕ) (i : Fin (n + 1)) : IsSeparated (affineSpaceCoordinate k' n i) :=
  sorry

/-- The `i`-th coordinate of the coordinate generic slice is the generic slice: `πᵢ ∘ hᵢ = σ`
on `𝔸ⁿ_{K⟦t⟧}`. -/
@[reassoc]
lemma affineSpaceSlice_comp_affineSpaceCoordinate (n : ℕ) (i : Fin (n + 1)) (x : K) :
    affineSpaceSlice n i x ≫ affineSpaceCoordinate k' n i =
      𝔸(ULift.{u} (Fin n); trait K) ↘ trait K ≫ traitSlice x :=
  sorry

/-- **The coordinate generic slice is cartesian**: `𝔸ⁿ_{K⟦t⟧} = 𝔸ⁿ⁺¹_S ×_{πᵢ, 𝔸¹_S, σ} Spec K⟦t⟧`. -/
lemma isPullback_affineSpaceSlice (n : ℕ) (i : Fin (n + 1)) (x : K) :
    IsPullback (affineSpaceSlice n i x) (𝔸(ULift.{u} (Fin n); trait K) ↘ trait K)
      (affineSpaceCoordinate k' n i) (traitSlice x) :=
  sorry

end AlgebraicGeometry
