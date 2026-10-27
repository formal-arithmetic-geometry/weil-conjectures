/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q119
-/
module

public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Spectrum.Maximal.Basic
import Mathlib.RingTheory.Support
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Localization decomposition for a finite module with finite maximal support

Source: Stacks Project, Tags 00L2 and 00JA, applied to the quotient by the module annihilator.
(blueprint: lem-sfb-finite-maximal-support-localization)
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace Module

/-- The canonical linear map from a finite module to the product of its localizations at a
finite list of distinct maximal ideals containing its support is bijective. Listed ideals
with zero localization are allowed, as is the empty list.

Source: Stacks Project, Tag 00L2 (`lemma-support-closed`) and Tag 00JA
(`lemma-product-local`), with the localization fractions of Tag 07JZ.
(blueprint: lem-sfb-finite-maximal-support-localization)

Proof plan:
1. Set `I = Ann_R(M)` and `B = R/I`. By `lem-weil-pbc-finite-module-support-annihilator`,
   the primes containing `I` are precisely the listed maximal ideals containing `I`.
   Quotient ideal correspondence therefore identifies all primes of `B` with this sublist.
2. By `lem-weil-pbc-zero-locus-eq-iff-radical-eq` at the zero ideal of `B`, the intersection
   of these primes is the nilradical. If the sublist is empty, `1` is nilpotent, hence `B`
   and `M` are zero. All localizations are then zero, including when the whole list is empty.
3. Otherwise `lem-weil-pbc-product-of-localizations-at-maximal` gives the canonical product
   decomposition of `B`. Pulling back the coordinate units gives orthogonal idempotents
   `e_i` whose sum is one.
4. The maps `m ↦ (e_i m)_i` and `(x_i)_i ↦ ∑ i, x_i` identify `M` with the product of
   the modules `e_i M`, by orthogonality and the sum-one identity.
5. For each retained index, `e_i M → M_{m_i}`, `x ↦ x/1`, is bijective. A representative
   of `e_i` lies outside `m_i` and kills `(1-e_i)M`, so `(e_i m)/1 = m/1`. For `s ∉ m_i`,
   the product decomposition supplies `b ∈ B` with `s b = e_i` and `b e_i = b`.
   If `x/1 = 0`, choose `s ∉ m_i` with `s x = 0`; then `x = b s x = 0`.
   Conversely `b e_i m` maps to the fraction `m/s`, proving surjectivity.
6. Compose these identifications; the components are exactly `m ↦ m/1`. At an omitted
   listed ideal, an element of `I` outside that ideal kills `M` and is invertible after
   localization, so the corresponding factor is zero. Inserting these zero factors
   preserves bijectivity and yields the canonical map for the entire list. -/
theorem bijective_pi_localization_of_finite_maximal_support
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (r : ℕ) (m : Fin r → MaximalSpectrum R) (hdistinct : Function.Injective m)
    (hsupport : ∀ q : PrimeSpectrum R, (∀ i : Fin r, q.asIdeal ≠ (m i).asIdeal) →
      Subsingleton (LocalizedModule q.asIdeal.primeCompl M)) :
    Function.Bijective (LinearMap.pi fun i : Fin r ↦
      LocalizedModule.mkLinearMap (m i).asIdeal.primeCompl M) := by
  sorry

end Module
