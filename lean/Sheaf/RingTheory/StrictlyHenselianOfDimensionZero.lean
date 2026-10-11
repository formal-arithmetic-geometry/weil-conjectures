/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
import WeilConjectures.Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.Idempotents
import Mathlib.RingTheory.KrullDimension.Basic

/-!
# Zero-dimensional local rings with separably closed residue field

Source: Stacks Project, Algebra, Tags 06RS, 04GG and 04GF
(blueprint: lem-weil-pbc-dimension-zero-local-strictly-henselian).
-/

universe u v

/-- A zero-dimensional local ring with separably closed residue field is strictly henselian;
idempotents lift uniquely in every finite algebra modulo the extended maximal ideal.
Source: Stacks Project, Algebra, Tag 06RS, Tag 04GG (10) implies (1), and Definition Tag 04GF
(blueprint: lem-weil-pbc-dimension-zero-local-strictly-henselian).

The hypothesis that `m` is the only prime of `R` is `ringKrullDim R = 0`
(`def-weil-pbc-krull-dimension-ring`), equivalent for a local ring.

Proof: (1) By `lem-weil-pbc-finite-over-zero-dim-local-discrete-spectrum`, a finite
`R`-algebra `B` has finitely many prime ideals, all maximal and over the unique prime of `R`;
their intersection is nil. The zero algebra is included, with no primes.
(2) By `lem-weil-pbc-product-of-localizations-at-maximal`, `B` is the product of its
localizations at these maximal ideals, as an `R`-algebra.
(3) Reduction modulo the extended maximal ideal is computed factorwise. In each local
factor the extended ideal lies in its maximal ideal, so the quotient is nonzero and local.
(4) The only idempotents of a local ring are zero and one: for `e * (1 - e) = 0`, one of
`e`, `1 - e` is a unit. Thus idempotents on both sides of reduction are exactly the same
zero/one vectors, and reduction is bijective on them. Empty products cover the zero algebra.
This is the henselian condition of `def-weil-pbc-henselian-terminology` (equivalently the
root-lifting condition, as in `lem-weil-pbc-henselian-local-root-lifting`).
(5) The residue field is separably closed by hypothesis (`def-pc-separably-closed`), giving
the strict condition of `def-weil-pbc-henselian-terminology`. -/
theorem isStrictlyHenselianLocalRing_of_ringKrullDim_eq_zero
    (R : Type u) [CommRing R] [IsLocalRing R] (hdim : ringKrullDim R = 0)
    [IsSepClosed (IsLocalRing.ResidueField R)] :
    IsStrictlyHenselianLocalRing R ∧
      ∀ (B : Type v) [CommRing B] [Algebra R B] [Module.Finite R B],
        ∀ e : B ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R B),
          IsIdempotentElem e →
            ∃! b : B, IsIdempotentElem b ∧
              Ideal.Quotient.mk ((IsLocalRing.maximalIdeal R).map (algebraMap R B)) b = e := by
  sorry
