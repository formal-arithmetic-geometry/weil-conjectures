/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.Topology.KrullDimension
import Sheaf.RingTheory.ClosedPointDimensionLocalRing
import Sheaf.RingTheory.PolynomialRingMaximalLocalizationDimension
import Sheaf.Topology.DimensionSupremumLocalDimensions

/-!
# Dimension lower bound for a polynomial quotient over a field

Source: Stacks Project, Algebra, paragraph following Definition Tag 00S9, using
Tags 00OP and 00KW (blueprint: lem-weil-pbc-polynomial-quotient-dimension-lower-bound).
-/

@[expose] public section

universe u

namespace AlgebraicGeometry

/-- A nonzero quotient of an `m`-variable polynomial ring over a field by `t ≤ m`
equations has spectrum of Krull dimension at least `m - t`.
Source: Stacks Project, Algebra, paragraph following Definition Tag 00S9.
(blueprint: lem-weil-pbc-polynomial-quotient-dimension-lower-bound)

Proof:
1. Put `P = k[x₁, …, xₘ]` and `J = (f₁, …, fₜ)`. The nonzero quotient `T = P/J`
   has a maximal ideal `n` by lem-weil-pbc-proper-ideal-contained-in-maximal.
   Its inverse image `M` in `P` is maximal, contains `J`, and satisfies `n = M/J`
   under the quotient correspondence, since `P/M` is the field `T/n`.
2. By lem-weil-pbc-polynomial-ring-maximal-localization-dimension, `dim P_M = m`.
   The lemma lem-weil-pbc-localization-dimension-chains-below-prime identifies this
   with `ht M` and identifies `dim T_n` with `ht n`. The ring `P` is Noetherian by
   lem-weil-pbc-finite-type-algebra-noetherian. Apply
   lem-weil-pbc-noetherian-height-quotient-bound to `J ⊆ M` to obtain
   `m = ht M ≤ ht (M/J) + t = dim T_n + t`, hence `m - t ≤ dim T_n`.
   This is the iteration of Tag 00KW at `M`, with Tag 00OP giving `dim P_M`.
3. The quotient `T` is a finite type `k`-algebra. The lemma
   lem-weil-pbc-closed-point-dimension-local-ring identifies the dimension at `n`
   in `Spec T` with `dim T_n`. The lemma
   lem-weil-pbc-dimension-supremum-local-dimensions bounds that point dimension
   above by `dim (Spec T)`. Combining with step 2 proves the claimed bound. -/
theorem sub_le_topologicalKrullDim_spec_mvPolynomial_quotient
    (k : Type u) [Field k] (m t : ℕ) (htm : t ≤ m)
    (f : Fin t → MvPolynomial (Fin m) k)
    [Nontrivial (MvPolynomial (Fin m) k ⧸ Ideal.span (Set.range f))] :
    ((m - t : ℕ) : WithBot ℕ∞) ≤ topologicalKrullDim
      (Spec (CommRingCat.of (MvPolynomial (Fin m) k ⧸ Ideal.span (Set.range f)))) := by
  sorry

end AlgebraicGeometry
