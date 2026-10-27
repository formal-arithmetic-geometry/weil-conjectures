/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.TransitionUnits
public import Sheaf.AlgebraicGeometry.ProjectiveSpace.PairwiseLaurentUnitExpansion

/-! # Cocycle comparison for pairwise Laurent expansions

Source: Stacks Project, divisors.tex, Tag 0BXJ, lemma-Pic-projective-space-UFD.
(blueprint: new-sfb-projective-pairwise-cocycle-normalization)
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.ProjectiveSpace

/-- The cocycle equation makes the exponents in pairwise Laurent expansions
constant and the scalar coefficients a chart coboundary.

Source: Stacks Project, divisors.tex, Tag 0BXJ, the triple-overlap calculation.
(blueprint: new-sfb-projective-pairwise-cocycle-normalization)

Proof: restrict the cocycle equation to a triple overlap with three distinct
indices.  The two independent Laurent coordinates force the three exponents to
agree.  The graph of distinct pairs is connected because `r ≥ 3`, so one integer
works for every pair.  Comparing scalar coefficients gives a multiplicative
coboundary; fixing a base chart supplies the chart scalars.  Substitution into
the pairwise expansions yields the displayed normalization equation.
-/
theorem exists_standardUnitCocycle_normalization_of_pairwise_laurent
    (k : Type u) [Field k] (r : ℕ) (hr : 3 ≤ r)
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
    (e : ∀ i j : ULift.{u} (Fin r), ℤ)
    (c : ∀ i j : ULift.{u} (Fin r), kˣ)
    (hpair : ∀ i j : ULift.{u} (Fin r), i ≠ j →
      (t i j).val =
        (ℙ(ULift.{u} (Fin r); Spec (.of k))).presheaf.map
          (homOfLE inf_le_left).op (standardOpenConstUnit k r i (c i j)).val *
          (transitionUnit _ (Spec (.of k)) (e i j) i j).val) :
    ∃ d : ℤ, ∃ a : ∀ i : ULift.{u} (Fin r),
      Γ(ℙ(ULift.{u} (Fin r); Spec (.of k)), standardOpen _ (Spec (.of k)) i)ˣ,
      ∀ i j : ULift.{u} (Fin r), i ≠ j →
        (ℙ(ULift.{u} (Fin r); Spec (.of k))).presheaf.map
            (homOfLE inf_le_left).op (a i).val * (t i j).val =
          (transitionUnit _ (Spec (.of k)) d i j).val *
            (ℙ(ULift.{u} (Fin r); Spec (.of k))).presheaf.map
              (homOfLE inf_le_right).op (a j).val := by
  sorry

end AlgebraicGeometry.ProjectiveSpace
