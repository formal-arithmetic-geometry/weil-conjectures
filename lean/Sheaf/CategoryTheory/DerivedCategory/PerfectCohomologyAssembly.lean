/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q16
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
import Sheaf.CategoryTheory.TruncationTriangle

import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Mathlib.Algebra.Homology.Single
import Mathlib.CategoryTheory.Triangulated.Triangulated
/-!
# Perfectness from bounded perfect cohomology

Source: Stacks Project, More on Algebra, Tag 066U, lemma-cohomology-perfect
(blueprint: lem-sf-perfect-cohomology-assembly).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits

namespace DerivedCategory

/-- An object with bounded cohomology, each cohomology module being perfect in degree zero,
is perfect. Source: Stacks Project, More on Algebra, Tag 066U, lemma-cohomology-perfect
(blueprint: lem-sf-perfect-cohomology-assembly).

Proof plan:
1. Choose a complex C representing K and fix its derived isomorphism and the induced
   identifications of cohomology, using def-weil-abstract-derived-category. Choose cohomology
   bounds a, b, and put K_r = Q(tau_{<=r} C). Directly computing the canonical truncation gives
   H^i(K_r) = H^i(K) for i <= r and zero otherwise (lem-weil-pbc-truncation-triangle).
2. K_{a-1} is acyclic, hence isomorphic to the zero complex and perfect by
   def-pc-perfect-ring-complex. This also handles the case of entirely zero cohomology.
3. For each r in [a,b], shift a bounded finite-projective model of H^r(K)[0] by -r.
   Its terms remain finite projective, its bounds shift by r, and Q commutes with shifts.
   Thus H^r(K)[-r] is perfect, without requiring uniform resolution bounds over all integers.
4. The canonical truncation triangle of lem-weil-pbc-truncation-triangle has first term
   K_{r-1}, second term K_r, and third term H^r(C)[-r]. The fixed cohomology identifications
   identify this third term with H^r(K)[-r]. Induct over the finite interval [a,b], applying
   lem-sf-perfect-ring-triangle-closure to obtain perfectness of K_r at each step.
5. The inclusion tau_{<=b} C -> C is a quasi-isomorphism because it is the identity on
   cohomology in degrees <= b and both cohomologies vanish above b. Localize and compose
   with the fixed representative isomorphism to obtain K_b isomorphic to K. Transport the
   bounded finite-projective model of K_b to K, as in def-pc-perfect-ring-complex. -/
theorem isPerfectRingComplex_of_perfect_cohomology {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)] (K : DerivedCategory (ModuleCat.{u} A))
    (hbounded : ∃ a b : ℤ, ∀ i : ℤ, i < a ∨ b < i →
      IsZero ((homologyFunctor (ModuleCat.{u} A) i).obj K))
    (hperfect : ∀ i : ℤ, IsPerfectRingComplex
      ((singleFunctor (ModuleCat.{u} A) 0).obj
        ((homologyFunctor (ModuleCat.{u} A) i).obj K))) :
    IsPerfectRingComplex K := by
  sorry

end DerivedCategory
