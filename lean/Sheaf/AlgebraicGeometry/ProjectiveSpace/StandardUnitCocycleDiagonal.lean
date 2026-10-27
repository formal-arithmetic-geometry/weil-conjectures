module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.TransitionUnits

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.ProjectiveSpace

/-- The diagonal equations left after the off-diagonal normalization.

Source: Stacks Project, divisors.tex, Tag 0BXJ, lemma-Pic-projective-space-UFD.
(blueprint: new-sfb-projective-standard-unit-cocycle-diagonal)

Proof: apply the cocycle equation with repeated indices to obtain the diagonal
unit relation and use the inverse of that unit to cancel. Apply the same
repeated-index calculation to the standard transition cocycle. Substituting
the off-diagonal equations on a pair and its reverse, and then cancelling the
chart unit, gives the required equation on the diagonal overlap.
-/
theorem standardUnitCocycle_diagonal_normalization (k : Type u) [Field k]
    (r : ℕ) (hr : 3 ≤ r)
    (t : ∀ i j : ULift.{u} (Fin r),
      Γ(ℙ(ULift.{u} (Fin r); Spec (.of k)),
        standardOpen _ (Spec (.of k)) i ⊓ standardOpen _ (Spec (.of k)) j)ˣ)
    (ht : ∀ (i j l : ULift.{u} (Fin r))
      (W : ℙ(ULift.{u} (Fin r); Spec (.of k)).Opens)
      (hi : W ≤ standardOpen _ (Spec (.of k)) i)
      (hj : W ≤ standardOpen _ (Spec (.of k)) j)
      (hl : W ≤ standardOpen _ (Spec (.of k)) l),
      (ℙ(ULift.{u} (Fin r); Spec (.of k))).presheaf.map
          (homOfLE (le_inf hi hj)).op (t i j).val *
        (ℙ(ULift.{u} (Fin r); Spec (.of k))).presheaf.map
          (homOfLE (le_inf hj hl)).op (t j l).val =
        (ℙ(ULift.{u} (Fin r); Spec (.of k))).presheaf.map
          (homOfLE (le_inf hi hl)).op (t i l).val)
    (d : ℤ)
    (a : ∀ i : ULift.{u} (Fin r),
      Γ(ℙ(ULift.{u} (Fin r); Spec (.of k)), standardOpen _ (Spec (.of k)) i)ˣ)
    (hoff : ∀ i j : ULift.{u} (Fin r), i ≠ j →
      (ℙ(ULift.{u} (Fin r); Spec (.of k))).presheaf.map
          (homOfLE inf_le_left).op (a i).val * (t i j).val =
        (transitionUnit _ (Spec (.of k)) d i j).val *
          (ℙ(ULift.{u} (Fin r); Spec (.of k))).presheaf.map
            (homOfLE inf_le_right).op (a j).val) :
    ∀ i : ULift.{u} (Fin r),
      (ℙ(ULift.{u} (Fin r); Spec (.of k))).presheaf.map
          (homOfLE inf_le_left).op (a i).val * (t i i).val =
        (transitionUnit _ (Spec (.of k)) d i i).val *
          (ℙ(ULift.{u} (Fin r); Spec (.of k))).presheaf.map
            (homOfLE inf_le_right).op (a i).val := by
  sorry

end AlgebraicGeometry.ProjectiveSpace
