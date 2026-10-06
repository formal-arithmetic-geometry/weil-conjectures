/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.RingTheory.Smooth.StandardSmoothOfFree
public import WeilConjectures.Mathlib.RingTheory.Extension.Presentation.Submersive

/-!
# Étale algebras and square Jacobian presentations

An `R`-algebra is étale if and only if it admits a square Jacobian presentation
`R[x₁, …, xₘ] / (f₁, …, fₘ)` with invertible Jacobian determinant.

## Main statements

- `Algebra.Etale.iff_exists_squareJacobianPresentation`: an algebra is étale if and only if it
  admits a square Jacobian presentation.

## References

- Stacks Project, Tag `00U9`, <https://stacks.math.columbia.edu/tag/00U9>
-/

@[expose] public section

universe u v

namespace Algebra

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/-- A square Jacobian presentation is standard smooth of relative dimension `0`. -/
lemma SquareJacobianPresentation.isStandardSmoothOfRelativeDimension_zero {ι : Type*} [Finite ι]
    (P : SquareJacobianPresentation R S ι) : IsStandardSmoothOfRelativeDimension 0 R S :=
  P.toSubmersivePresentation.isStandardSmoothOfRelativeDimension (by
    simp [Presentation.dimension])

/-- An algebra admitting a square Jacobian presentation is étale. -/
lemma SquareJacobianPresentation.etale {ι : Type*} [Finite ι]
    (P : SquareJacobianPresentation R S ι) : Etale R S :=
  have := P.isStandardSmoothOfRelativeDimension_zero
  inferInstance

/-- An `R`-algebra `S` is étale if and only if it admits a square Jacobian presentation
`S = R[x₁, …, xₘ] / (f₁, …, fₘ)` with `det (∂fᵢ / ∂xⱼ)` a unit in `S` (blueprint
`lem-exc-etale-jacobian-presentation`).

The forward direction starts from a submersive presentation of relative dimension `0`, given
by `Algebra.Etale.iff_isStandardSmoothOfRelativeDimension_zero`: its injective map from the
relations to the variables is then a bijection, along which the variables are reindexed. -/
@[stacks 00U9]
theorem Etale.iff_exists_squareJacobianPresentation :
    Etale R S ↔ ∃ (ι : Type) (_ : Finite ι), Nonempty (SquareJacobianPresentation R S ι) := by
  refine ⟨fun h ↦ ?_, fun ⟨_, _, ⟨P⟩⟩ ↦ P.etale⟩
  obtain ⟨ι, σ, _, _, P, hP⟩ :=
    (Etale.iff_isStandardSmoothOfRelativeDimension_zero.mp h).out
  have hcard : Nat.card ι ≤ Nat.card σ := by
    simpa [Presentation.dimension, Nat.sub_eq_zero_iff_le] using hP
  let e : σ ≃ ι := Equiv.ofBijective P.map (P.map_inj.bijective_of_nat_card_le hcard)
  let Q := P.toPreSubmersivePresentation.reindex e (Equiv.refl σ)
  refine ⟨σ, inferInstance, ⟨
    { toPreSubmersivePresentation := Q
      jacobian_isUnit := by
        simpa [Q, PreSubmersivePresentation.jacobian_reindex] using P.jacobian_isUnit
      map_eq_id := ?_ }⟩⟩
  ext i
  simp [Q, PreSubmersivePresentation.reindex_map, e]

end Algebra
