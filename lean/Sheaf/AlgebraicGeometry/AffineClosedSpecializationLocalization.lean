/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NQ
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
public import Mathlib.RingTheory.Localization.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.Spectrum.Prime.Topology
import WeilConjectures.Mathlib.RingTheory.Etale.Weakly
import Sheaf.RingTheory.IndPrincipalZariski
import Mathlib.RingTheory.Ideal.Maximal

/-! # Affine localization near an arbitrary closed subset

Source: Stacks Project, Tag 096V, Lemma `lemma-localization`, with `f = 1`, and Tag 092B
(blueprint: lem-weil-pbc-affine-closed-specialization-localization).
-/

@[expose] public section

universe u

namespace AlgebraicGeometry

/-- Localization at the elements invertible modulo `I` is weakly etale and identifies its
spectrum with the points specializing to `V(I)`. Every source point specializes to a point
above `V(I)`. Source: Stacks Project, Tags 096V and 092B
(blueprint: lem-weil-pbc-affine-closed-specialization-localization).

Proof:
1. The quotient-unit condition defines a multiplicative set. Apply
   `lem-weil-pbc-localization-ring-weakly-etale` and the affine equivalence in
   `def-weil-pbc-ind-etale-algebra` to obtain weak etaleness of the spectrum morphism.
2. `lem-weil-pbc-localization-spectrum-embedding` embeds the localization spectrum with
   image the primes disjoint from `S`.
3. If `p ≤ q` and `I ≤ q`, a member `s` of `S` cannot lie in `p`: lift an inverse of `s`
   modulo `I`; then `s * t - 1 ∈ I` would force `1 ∈ q`.
4. Conversely, if `p` avoids `S`, the ideal `p + I` is proper, since an equality
   `1 = a + i` with `a ∈ p` and `i ∈ I` makes `a` invertible modulo `I`. Use
   `lem-weil-pbc-proper-ideal-contained-in-maximal` to put `p + I` inside a maximal,
   hence prime, ideal `q`. This identifies the image; taking `p = q` includes `V(I)`.
5. Given a source point, choose such a `q` and lift it to the source using the image
   description. By `lem-weil-pbc-spec-localization-away-basic-open`, test specialization
   on basic opens. The denominator of a fraction is a unit, so its basic open equals
   that of its numerator. The inclusion `p ≤ q` gives the required specialization.
No finite-generation assumption on `I` is used. -/
theorem affineClosedSpecializationLocalization (A : Type u) [CommRing A] (I : Ideal A)
    (S : Submonoid A) (hS : ∀ a : A, a ∈ S ↔ IsUnit (Ideal.Quotient.mk I a)) :
    WeaklyEtale (Spec.map (CommRingCat.ofHom (algebraMap A (Localization S)))) ∧
    Topology.IsEmbedding (PrimeSpectrum.comap (algebraMap A (Localization S))) ∧
    Set.range (PrimeSpectrum.comap (algebraMap A (Localization S))) =
      {p : PrimeSpectrum A | ∃ q : PrimeSpectrum A, I ≤ q.asIdeal ∧ p.asIdeal ≤ q.asIdeal} ∧
    {q : PrimeSpectrum A | I ≤ q.asIdeal} ⊆
      Set.range (PrimeSpectrum.comap (algebraMap A (Localization S))) ∧
    ∀ x : PrimeSpectrum (Localization S), ∃ y : PrimeSpectrum (Localization S),
      Specializes x y ∧ I ≤ (PrimeSpectrum.comap (algebraMap A (Localization S)) y).asIdeal := by
  sorry

end AlgebraicGeometry
