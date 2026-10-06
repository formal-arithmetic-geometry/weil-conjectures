/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.AlgClosed.Basic

/-!
# Points of finite schemes over algebraically closed fields

Let `K` be an algebraically closed field. A nonempty finite `K`-scheme has a `K`-point, and
consequently a finite surjective morphism `f : X ⟶ Y` is surjective on `K`-valued points: every
`y : Spec K ⟶ Y` lifts along `f`.

## Main results

- `AlgebraicGeometry.exists_comp_eq_id_of_isFinite`: a nonempty finite scheme over an
  algebraically closed field `K` has a `K`-point.
- `AlgebraicGeometry.exists_comp_eq_of_isFinite_of_surjective`: a finite surjective morphism is
  surjective on points with values in an algebraically closed field.
-/

@[expose] public section

open CategoryTheory Limits

namespace AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}} {K : Type u} [Field K] [IsAlgClosed K]

/-- Blueprint `lem-sc-finite-nonempty-point`: Finite schemes over algebraically closed fields.

A nonempty finite scheme `X` over an algebraically closed field `K` has a `K`-point: a closed
point of `X` has residue field `K`. -/
theorem exists_comp_eq_id_of_isFinite (f : X ⟶ Spec (.of K)) [IsFinite f] [Nonempty X] :
    ∃ s : Spec (.of K) ⟶ X, s ≫ f = 𝟙 _ := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  obtain ⟨x, -, hx⟩ := isClosed_univ.exists_closed_singleton (X := X) Set.univ_nonempty
  exact ⟨pointOfClosedPoint f x hx, pointOfClosedPoint_comp f x hx⟩

/-- Blueprint `lem-sc-finite-flat-surj-points`: Finite flat surjections are surjective on
`K`-points.

Let `f : X ⟶ Y` be finite and surjective and `K` algebraically closed. Then every `K`-point
`y : Spec K ⟶ Y` lifts to a `K`-point of `X`: the fibre `X ×_Y Spec K` is a nonempty finite
`K`-scheme, so it has a `K`-point by `exists_comp_eq_id_of_isFinite`. (Flatness, assumed in the
blueprint, is not needed.) -/
theorem exists_comp_eq_of_isFinite_of_surjective (f : X ⟶ Y) [IsFinite f] [Surjective f]
    (y : Spec (.of K) ⟶ Y) : ∃ x : Spec (.of K) ⟶ X, x ≫ f = y := by
  have : Nonempty ↥(pullback f y) :=
    ⟨((pullback.snd f y).surjective (IsLocalRing.closedPoint K)).choose⟩
  obtain ⟨s, hs⟩ := exists_comp_eq_id_of_isFinite (pullback.snd f y)
  exact ⟨s ≫ pullback.fst f y, by rw [Category.assoc, pullback.condition, reassoc_of% hs]⟩

end AlgebraicGeometry
