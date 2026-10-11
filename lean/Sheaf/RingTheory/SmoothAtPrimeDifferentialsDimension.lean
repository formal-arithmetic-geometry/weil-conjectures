/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import WeilConjectures.Mathlib.Topology.KrullDimension
import Sheaf.RingTheory.SingularIdeal

/-!
# Dimension of differentials at a smooth point over a field

Source: Stacks Project, Algebra, Lemma 00TT, implication (1) implies (3)
(blueprint: lem-weil-pbc-smooth-over-field-dimension-differentials).
-/

universe u v

open scoped TensorProduct

namespace Algebra

/-- At a smooth prime of a finite type algebra over a field, the fibre of the module of
Kähler differentials is finite-dimensional, with dimension equal to the topological
Krull dimension at that point. Scalar extension places the residue field on the left;
the tensor-product commutor identifies this with `Ω[S⁄k] ⊗[S] κ(q)`.
Source: Stacks Project, Algebra, Lemma 00TT, implication (1) implies (3)
(blueprint: lem-weil-pbc-smooth-over-field-dimension-differentials).

Proof:
1. Smoothness at `q` (`def-weil-pbc-singular-ideal`) gives a principal localization `S_u`
   smooth over `k` (`def-weil-pbc-smooth-ring-map`). By
   `lem-weil-pbc-smooth-ring-map-locally-standard-smooth`, shrink again to a standard
   smooth presentation (`def-weil-pbc-standard-smooth-algebra`) with `n` variables and
   `c` equations. Write the second localization element as `a/u^m`. Since `a` and `u`
   lie outside `q`, successive localization agrees with localization at `f = u*a`,
   also outside `q`, by the universal property of localization.
2. By `lem-weil-pbc-standard-smooth-kahler-basis`, the differentials of the last `n-c`
   variables form a basis of the localized differential module. Its fibre over the
   residue field (`def-weil-pbc-localization-at-prime`) has a basis of cardinality `n-c`.
3. By `lem-weil-pbc-kahler-differentials-localization`, localized differentials are
   the localization of the original differentials (`def-weil-pbc-kahler-differentials`).
   Tensor associativity identifies their residue-field fibres, proving finiteness and
   dimension `n-c` for the original fibre.
4. The standard open `D(f)` is homeomorphic to `Spec S_f`. The point dimension
   (`def-kun-topological-dimension-at-point`) is unchanged by this open restriction
   (`lem-weil-pbc-dimension-at-point-open-subspace`). By
   `lem-weil-pbc-standard-smooth-over-field-dimension-at-points`, its dimension is `n-c`.
   Comparing with step 3 proves the equality. -/
theorem finiteDimensional_and_finrank_kaehlerDifferential_eq_of_isSmoothAtPrime
    {k : Type u} [Field k] {S : Type v} [CommRing S] [Algebra k S] [FiniteType k S]
    (q : PrimeSpectrum S) (h : IsSmoothAtPrime k q) :
    FiniteDimensional q.asIdeal.ResidueField
      (q.asIdeal.ResidueField ⊗[S] KaehlerDifferential k S) ∧
    (Module.finrank q.asIdeal.ResidueField
      (q.asIdeal.ResidueField ⊗[S] KaehlerDifferential k S) : WithBot ℕ∞) =
        topologicalKrullDimAt q := by
  sorry

end Algebra
