/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.Topology.KrullDimension
import WeilConjectures.Mathlib.Topology.KrullDimension

/-!
# A global complete intersection has the expected dimension at every point

Source: literature/stacks-project/algebra.tex, Algebra, Section 00S8
(blueprint: lem-weil-pbc-global-complete-intersection-equidimensional).
-/

universe u

namespace AlgebraicGeometry

/-- A nonzero quotient of a polynomial ring over a field by `t` equations whose
spectrum has dimension `m - t` has that local dimension at every prime.

Source: literature/stacks-project/algebra.tex, Algebra, Section 00S8, the paragraph
following Definition 00S9 (lines 35834--35849), using Lemma 00OT.
(blueprint: lem-weil-pbc-global-complete-intersection-equidimensional)

The conjunct `t ≤ m` in `hDim` expresses the nonnegativity forced by the
integer equality `dim T = m - t` for a nonzero ring; it prevents natural
subtraction from admitting presentations with more equations than variables.

Proof (the five DAG steps):
1. Put `J = Ideal.span (Set.range f)`, `T = Q / J`, and `X = Spec T`.
   The quotient is finite type over `k` (`def-weil-pbc-finite-type-algebra`),
   and `Q` is Noetherian (`lem-weil-pbc-finite-type-algebra-noetherian`).
   Nontriviality gives a maximal ideal, so `X` is nonempty and its dimension
   is nonnegative (`def-kun-topological-krull-dimension`).
2. The whole spectrum is an open neighbourhood of any prime `p`. The infimum
   defining `topologicalKrullDimAt` (`def-kun-topological-dimension-at-point`)
   therefore gives the upper bound `dim_p X ≤ dim X = m - t`.
3. Write an open neighbourhood `U` of `p` as the complement of `V(I)`
   (`lem-weil-pbc-spec-irreducible-closed-subsets-primes`), and choose
   `g ∈ I` outside `p`. The Jacobson property of the finite-type algebra
   (`lem-weil-pbc-finite-type-over-field-prime-intersection-maximal`)
   supplies a maximal ideal `M` containing `p` and avoiding `g`, hence in `U`.
4. Pull `M` back to a maximal ideal `M'` of `Q`. Its localization has dimension
   `m` (`lem-weil-pbc-polynomial-ring-maximal-localization-dimension`).
   Localization dimensions are heights
   (`lem-weil-pbc-localization-dimension-chains-below-prime`), and the
   Noetherian height bound for the `t` generators of `J`
   (`lem-weil-pbc-noetherian-height-quotient-bound`) gives
   `m ≤ dim T_M + t`, thus `dim T_M ≥ m - t`.
5. Since `M ∈ U`, `dim U ≥ dim_M X`. The dimension at a closed point equals
   that of its local ring (`lem-weil-pbc-closed-point-dimension-local-ring`),
   so step 4 gives `dim U ≥ m - t`. Taking the infimum over all `U` gives
   the lower bound at `p`; combine it with step 2.
-/
theorem topologicalKrullDimAt_spec_quotient_mvPolynomial_of_eq
    (k : Type u) [Field k] (m t : ℕ)
    (f : Fin t → MvPolynomial (Fin m) k)
    (hT : Nontrivial (MvPolynomial (Fin m) k ⧸ Ideal.span (Set.range f)))
    (hDim : t ≤ m ∧
      topologicalKrullDim
          (Spec (CommRingCat.of (MvPolynomial (Fin m) k ⧸ Ideal.span (Set.range f)))) =
        ((m - t : ℕ) : WithBot ℕ∞)) :
    ∀ p : PrimeSpectrum (MvPolynomial (Fin m) k ⧸ Ideal.span (Set.range f)),
      topologicalKrullDimAt
          (⟨p, inferInstance⟩ :
            Spec (CommRingCat.of (MvPolynomial (Fin m) k ⧸ Ideal.span (Set.range f)))) =
        ((m - t : ℕ) : WithBot ℕ∞) := by
  sorry

end AlgebraicGeometry
