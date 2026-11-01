/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientSourcePullback
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.DiagonalBaseSquares

/-! # The Cartesian square of the relative projective diagonal

Source: blueprint diagonal coefficient changes, paragraph (3).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

/-- The relative projective diagonal commutes with arbitrary base change.
Source: blueprint diagonal coefficient changes, paragraph (3)
(blueprint: lem-diagonal-base-change-cartesian).
Proof: for a test scheme mapping to the bottom left and top right corners,
project the map to the product on its first factor. The two factor projections
have the same image in the original projective line by the assumed cone equation,
and the same image in the new base by the product condition. The Cartesian square
for projective space identifies those two projections. Thus the first projection
lifts the cone. Uniqueness follows by composing the diagonal with its first
projection. This proof includes the empty base and imposes no flatness condition. -/
theorem diagonalBaseChange_cartesian {Y Y' : Scheme.{u}} (g : Y' ⟶ Y) :
    IsPullback (baseP g) (diagonalImmersion Y') (diagonalImmersion Y) (baseW g) := by
  let q := (ProjectiveLine Y ↘ Y)
  let q' := (ProjectiveLine Y' ↘ Y')
  let a' := pullback.fst q' q'
  let b' := pullback.snd q' q'
  have hp := ProjectiveSpace.isPullback_map (ULift.{u} (Fin 2)) g
  refine IsPullback.mk' (diagonalBaseSquares g).diagonal_square.symm ?_ ?_
  · intro T φ ψ _ h₂
    exact (cancel_mono (diagonalImmersion Y')).1 h₂
  · intro T a b hab
    have ha : (b ≫ a') ≫ baseP g = a := by
      have h := congrArg (fun t ↦ t ≫ pullback.fst q q) hab
      simpa [q, q', a', diagonalImmersion, baseW, Category.assoc] using h.symm
    have hb : (b ≫ b') ≫ baseP g = a := by
      have h := congrArg (fun t ↦ t ≫ pullback.snd q q) hab
      simpa [q, q', b', diagonalImmersion, baseW, Category.assoc] using h.symm
    have he : b ≫ a' = b ≫ b' := by
      apply hp.hom_ext
      · exact ha.trans hb.symm
      · simpa only [Category.assoc] using congrArg (fun t ↦ b ≫ t)
          (pullback.condition (f := q') (g := q'))
    refine ⟨b ≫ a', ha, ?_⟩
    apply pullback.hom_ext
    · simp only [diagonalImmersion, Category.assoc, pullback.diagonal_fst,
        Category.comp_id]
      rfl
    · simpa only [diagonalImmersion, Category.assoc, pullback.diagonal_snd,
        Category.comp_id] using he

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
