/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q48
-/
module

public import Sheaf.RingTheory.HeightOneFractionOrder
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Localization.Submodule
public import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
import Mathlib.RingTheory.Length
import WeilConjectures.AlgebraicGeometry.Regular
import WeilConjectures.RingTheory.NormalDomainPrincipalQuotientAssociatedHeight
import WeilConjectures.RingTheory.InjectivePiLocalizationAssociatedPrimes

/-!
# Principal divisors of a normal Noetherian domain

Source: Stacks Project, Algebra, Tags 00PD, 031S, 031T and 02MD; Divisors,
Tags 02RL, 0BE3 and 02RP (blueprint: lem-trf-normal-domain-principal-divisor-kernel).
-/

@[expose] public section

universe u

namespace Ring

/-- The canonical inclusion of a height-one localization into the fraction field.
This is notation for Mathlib's algebra map of the instance
`IsLocalization.instAlgebraLocalizationAtPrime` (the localization map for the inclusion
of denominator monoids), not a separate construction.
Source: Stacks Project, Algebra, Tag 031T, localization inside the fraction field
(blueprint: lem-trf-normal-domain-principal-divisor-kernel). -/
noncomputable abbrev weilHeightOneLocalizationMap {R : Type u} [CommRing R] [IsDomain R]
    (q : WeilHeightOnePrime R) : Localization.AtPrime q.1.asIdeal →+* FractionRing R :=
  algebraMap (Localization.AtPrime q.1.asIdeal) (FractionRing R)

/-- The local orders are normalized additive valuations, and their finitely supported
principal divisor homomorphism has precisely the global units as its kernel.
The fraction field is the canonical `FractionRing R`; `Additive` expresses a homomorphism
from its multiplicative unit group to the additive divisor group.

Source: Stacks Project, Algebra, Tags 00PD, 031S, 031T and 02MD; Divisors,
Tags 02RL, 0BE3 and 02RP (blueprint: lem-trf-normal-domain-principal-divisor-kernel).

Proof (the eight steps of the DAG node):
1. Localization is Noetherian and normal by lem-weil-pbc-localization-noetherian and
   lem-weil-pbc-localization-normal-domain. The primes below a height-one prime are
   zero and itself, so lem-weil-pbc-localization-dimension-chains-below-prime gives
   dimension one. Lemma lem-sc-normal-dim1-dvr (00PD) makes the local ring a DVR.
2. Lemma lem-weil-pbc-dvr-unit-times-uniformizer-power writes nonzero local elements
   as unit times a uniformizer power. Cancellation proves exponent uniqueness.
   Cross multiplication proves that the exponent difference for fractions is
   independent of presentation, additive on products and normalized on all integer
   powers. Nonnegative exponent characterizes local membership; exponent zero
   characterizes local units. Factoring out the minimum exponent proves the
   valuation inequality for a nonzero sum.
3. The sequences from multiplication by the uniformizer and reduction modulo it
   give length(B/(pi^n)) = n by lem-weil-pbc-length-additive-short-exact, starting
   from length(B/B) = 0 and length(B/(pi)) = 1. Hence the exponent difference is
   exactly the length-difference order in def-trf-affine-weil-divisor-class-group.
4. If x = a/b, any height-one prime outside a and b has order zero. Height-one
   primes containing a nonzero a are minimal over (a); the same holds for b.
   Lemma lem-sc-finite-minimal-primes-over-ideal therefore gives finite support.
5. These coordinates define an affine Weil divisor. Coordinatewise additivity
   makes this a homomorphism, with exactly the stated length-order coordinates.
6. To intersect the height-one localizations, write z = b/a. By
   lem-weil-pbc-normal-domain-principal-quotient-associated-height every associated
   prime of R/(a) has height one. Local membership gives s outside that prime
   with sb in (a). The elementwise criterion of
   lem-weil-pbc-module-injects-localizations-associated-primes gives b in (a),
   hence z in R. This criterion also includes an empty associated-prime set.
7. A zero divisor puts x and its inverse in every height-one localization, hence
   both in R by step 6. Their product is one, so x is a global unit. Conversely
   a global unit is a unit in every localization and all its orders vanish.
8. For a field there are no nonzero primes. The divisor group is zero, and every
   fraction-field unit comes from a global unit, verifying the empty case. -/
theorem normalDomain_principalDivisor_kernel
    (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] :
    (∀ q : WeilHeightOnePrime R, IsDiscreteValuationRing (Localization.AtPrime q.1.asIdeal)) ∧
    (∀ (q : WeilHeightOnePrime R) (π : Localization.AtPrime q.1.asIdeal),
      Irreducible π → ∀ (a : (Localization.AtPrime q.1.asIdeal)ˣ) (e : ℤ),
        weilFractionOrder q
          (weilHeightOneLocalizationMap q a * weilHeightOneLocalizationMap q π ^ e) = e) ∧
    (∀ (q : WeilHeightOnePrime R) (x : (FractionRing R)ˣ),
      ((∃ a : Localization.AtPrime q.1.asIdeal,
        weilHeightOneLocalizationMap q a = (x : FractionRing R)) ↔
          0 ≤ weilFractionOrder q (x : FractionRing R)) ∧
      ((∃ a : (Localization.AtPrime q.1.asIdeal)ˣ,
        weilHeightOneLocalizationMap q a = (x : FractionRing R)) ↔
          weilFractionOrder q (x : FractionRing R) = 0)) ∧
    (∀ (q : WeilHeightOnePrime R) (x y : FractionRing R),
      x ≠ 0 → y ≠ 0 → x + y ≠ 0 →
        min (weilFractionOrder q x) (weilFractionOrder q y) ≤ weilFractionOrder q (x + y)) ∧
    (∀ x : (FractionRing R)ˣ,
      {q : WeilHeightOnePrime R | weilFractionOrder q (x : FractionRing R) ≠ 0}.Finite) ∧
    (∀ (q : WeilHeightOnePrime R) (a b : R), a ≠ 0 → b ≠ 0 →
      weilFractionOrder q (algebraMap R (FractionRing R) a / algebraMap R (FractionRing R) b) =
        weilOrder q a - weilOrder q b) ∧
    (∃ div : Additive (FractionRing R)ˣ →+ AffineWeilDivisor R,
      (∀ (x : (FractionRing R)ˣ) (q : WeilHeightOnePrime R),
        div (Additive.ofMul x) q = weilFractionOrder q (x : FractionRing R)) ∧
      (∀ x : (FractionRing R)ˣ, div (Additive.ofMul x) = 0 ↔
        ∃ a : Rˣ, Units.map (algebraMap R (FractionRing R)).toMonoidHom a = x)) ∧
    (IsField R → IsEmpty (WeilHeightOnePrime R) ∧ Subsingleton (AffineWeilDivisor R)) := by
  sorry

end Ring
