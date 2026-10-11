/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.RingTheory.Spectrum.Maximal.Defs

/-!
# Normalization of a one-dimensional semilocal domain

Source: Stacks Project, Varieties, Lemma 09N2, opening normalization clause, and
Algebra, Lemma 09IG (blueprint: lem-sc-semilocal-dim-one-normalization).
-/

universe u v

namespace integralClosure

/-- The normalization of a semilocal Noetherian domain of dimension one in its fraction
field is semilocal, Noetherian, an integrally closed domain of dimension one, and has
that same fraction field. Mathlib's Dedekind predicate permits dimension zero, so
dimension one is stated separately to retain the node's convention.
Source: Stacks Project, Varieties Lemma 09N2, opening normalization clause, invoking
Algebra Lemma 09IG (`lemma-integral-closure-Dedekind`).
(blueprint: lem-sc-semilocal-dim-one-normalization).

Proof:
1. Apply `lem-sc-integral-closure-dedekind-surjective-fibres` with `L = K`.
   The integral closure is Dedekind of dimension one, and its spectrum maps
   surjectively to the spectrum of `B` with finite fibres. By
   `lem-weil-pbc-integral-maximal-contracts-maximal`, maximal ideals contract to
   maximal ideals under the integral inclusion.
2. Since `B` has finitely many maximal ideals and each spectral fibre is finite,
   the maximal ideals of its integral closure form a finite union of finite sets.
   Thus the integral closure is semilocal, using the same two cited nodes.
3. The inclusions `B ⊆ integralClosure B K ⊆ K` show that its fraction field is
   contained in `K` and contains the fraction field `K` of `B`, hence equals `K`. -/
theorem semilocal_normalization_dim_one
    (B : Type u) [CommRing B] [IsDomain B] [IsNoetherianRing B]
    [Finite (MaximalSpectrum B)] (hdim : ringKrullDim B = 1)
    (K : Type v) [Field K] [Algebra B K] [IsFractionRing B K] :
    Finite (MaximalSpectrum (integralClosure B K)) ∧
      IsDedekindDomain (integralClosure B K) ∧ ringKrullDim (integralClosure B K) = 1 ∧
      IsFractionRing (integralClosure B K) K := by
  sorry

end integralClosure
