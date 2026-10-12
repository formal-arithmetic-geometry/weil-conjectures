/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group X3
-/
module

public import Sheaf.RingTheory.PopescuLiftInduction
import Sheaf.RingTheory.PopescuDesingularizeLiftingApply
import Sheaf.RingTheory.PopescuResolution
import Sheaf.RingTheory.SingularIdeal
import Sheaf.RingTheory.StrictlyStandardElement

/-!
# Lifting a Popescu resolution for one element

Source: Stacks Project, Lemma 07F8 (lemma-lift-solution), case r = 1.
(blueprint: lem-weil-pbc-popescu-lift-one)
-/

@[expose] public section

universe u v w

namespace Algebra

/-- The one-element case of lifting a resolution.
Source: Stacks Project, Lemma 07F8 (lemma-lift-solution), case r = 1, using Lemma 07F0.
(blueprint: lem-weil-pbc-popescu-lift-one)

Proof:
1. Unpack the reduced resolution as A/π⁸ → C → Λ/π⁸. For the unique index, the
preceding-powers ideals are zero. Transport the two annihilator equalities across the
quotient-by-zero equivalences to obtain Ann(π) = Ann(π²) in R and Λ.
2. Apply popescu_desingularize_lifting_apply to this factorization, these equalities and
strict standardness. It gives a finitely presented factorization A → B → Λ, smooth
on inverting π, and inclusion of the image of H(C) in the image of h(B).
3. Smoothness on inverting π implies π belongs to H(B): compose the smooth map from
R to R[1/π] with R[1/π] → B[1/π], and identify B[1/π] with the principal localization.
Thus π⁸Λ is contained in h(B). Since h(B) is radical, its quotient is radical, and the
containment from step 2 extends to h(C).
4. Singular ideals map into singular ideals under base change: each generator with
smooth principal localization retains that property after base change, by smooth base
change and localization base change; then take radicals. Therefore the image of h(A)
in Λ/π⁸ lies in h(A/π⁸), hence in h(C), and its inverse image lies in h(B) by step 3.
5. Lift an element of h(C) outside the reduced prime. It lies in h(B) and outside q,
so h(B) is not contained in q. The factorization is a resolution.
6. Represent B in universe max u v by a finite polynomial presentation over R,
transporting both maps and their singular ideals along the resulting algebra equivalence.
This ensures the carrier bound in CanBePopescuResolved. -/
theorem popescuEighthPowerLifting_one : PopescuEighthPowerLifting.{u, v, w} 1 := by
  sorry

end Algebra
