/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NC
-/
module

public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.GroupTheory.MonoidLocalization.Away
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.LocalRing.Quotient
import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!+# A parameter identifying a local curve's principal localization with its total fractions

Source: Stacks Project, Varieties, Tag 0C3R, Lemma 33.39.1, existence and condition (5)
for a reduced ring (blueprint: lem-exc-local-curve-principal-total-fractions).
-/

@[expose] public section

universe u

namespace IsLocalRing

/-- A reduced Noetherian local ring of dimension one has a regular parameter whose
canonical map from the principal localization to the total fraction ring is an isomorphism.
Source: Stacks Project, Tag 0C3R, existence and condition (5)
(blueprint: lem-exc-local-curve-principal-total-fractions).

Proof:
1. Apply `lem-weil-pbc-noetherian-local-system-of-parameters` in dimension one to choose
   `f` in the maximal ideal with the radical of `(f)` equal to the maximal ideal.
2. Every prime lies in the maximal ideal by `lem-weil-pbc-local-ring-unit-criterion`.
   Dimension one rules out a chain of three distinct primes. Hence every other prime
   is minimal, and the maximal ideal is not minimal. A minimal prime containing `f`
   would contain the radical of `(f)`, so would equal the maximal ideal. Thus none does.
3. By `lem-weil-pbc-reduced-zerodivisors-union-minimal-primes`, `f` is a nonzerodivisor.
   Nonzerodivisors form a multiplicative set, containing every power of `f`.
4. The universal property of localization gives the canonical algebra map, sending
   `r / f^n` to the same fraction in the total ring of fractions. Its fraction formula
   is well defined by the equality criterion of `def-weil-pbc-module-localization`
   and `def-weil-ring-localization-away`.
5. Every nonzerodivisor `s` divides some power of `f`: for a unit use the zeroth power;
   otherwise `s` lies in the maximal ideal and in no minimal prime, so that ideal is
   the only prime containing `(s)`. The radical-intersection clause of
   `lem-weil-pbc-zero-locus-eq-iff-radical-eq` gives `radical (s) = maximalIdeal R`.
   Thus `f^n = s * a` for some positive `n` and some `a`.
6. The canonical map is injective: a fraction mapping to zero has numerator killed
   by a nonzerodivisor, hence zero. It is surjective: writing `f^n = s * a` as in
   step 5, the total fraction `r / s` is the image of `(r * a) / f^n`. A bijective
   algebra homomorphism is an algebra isomorphism, proving all clauses for this `f`.
-/
theorem exists_parameter_principal_total_fractions
    (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R] [IsReduced R]
    (hdim : ringKrullDim R = 1) :
    ∃ (f : R) (hf : f ∈ nonZeroDivisors R),
      f ∈ maximalIdeal R ∧
      (∀ p ∈ minimalPrimes R, f ∉ p) ∧
      (Ideal.span ({f} : Set R)).radical = maximalIdeal R ∧
      Function.Bijective
        (IsLocalization.Away.liftAlgHom (S := Localization.Away f)
          (f := Algebra.ofId R (FractionRing R)) f
          (IsLocalization.map_units (FractionRing R) ⟨f, hf⟩)) := by
  sorry

end IsLocalRing
