/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
module

public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Algebra.ZMod
public import Mathlib.Data.Finset.Union

/-!
# Subfields of the fraction field of a power-series polynomial ring

Source: Stacks Project, More on Algebra, Lemmas 07P5 and 07P4
(blueprint: lem-weil-pbc-power-series-ring-subfields).
-/

@[expose] public section

set_option autoImplicit false

universe u v w

attribute [local instance] ZMod.algebra

namespace RingTheory

open Classical in
/-- The subfields cut out by a p-basis in a power-series polynomial ring.
Source: Stacks Project, More on Algebra, Lemmas 07P5 and 07P4
(blueprint: lem-weil-pbc-power-series-ring-subfields).

The ring A is written out as `MvPolynomial (Fin m) (MvPowerSeries (Fin n) k)`.
The families `kJ`, `AJ`, and `KJ` are specified by exact defining conditions:
field generation, coefficients supported on p-divisible exponents, and quotients.
No finiteness or intersection conclusion is assumed.

Proof (the eight steps of the node):
1. A is a domain by `lem-weil-pbc-power-series-domain` and
   `lem-weil-pbc-polynomial-ring-domain`. Its fraction map is injective. Quotients
   of elements of a subring form a subfield, since nonzero denominators multiply.
2. Expand h in polynomial y-monomials with power-series coefficients. Addition
   is coefficientwise and multiplication is convolution. The coefficient condition
   defining AJ contains 1 and is closed under addition, negatives and multiplication:
   sums of p-divisible exponents remain p-divisible and kJ is a subfield.
3. The p-basis monomials off J span kJ over k^p: this span is a ring, and each
   element lies in a finite-dimensional subring, where multiplication by a nonzero
   element is bijective, giving its inverse. Splitting monomial supports into J
   and its complement gives a kJ-basis of k indexed by bounded monomials on J.
   Uniqueness of p-basis coordinates gives intersection_J kJ = k^p. Enlarging J
   removes generators, so kJ is decreasing.
4. Divide every x- and y-exponent by p with remainder. Group the coefficients
   using the kJ-basis from step 3. This gives the finite AJ-basis t^E x^e y^g,
   with E supported on J and all exponents below p. Coefficient comparison proves
   independence. Thus A is finite over AJ (`def-weil-finitely-generated-module`).
5. By `lem-weil-pbc-power-series-frobenius-coefficientwise`, Frobenius raises
   coefficients to p-th powers and multiplies exponents by p. Conversely, taking
   coefficient roots gives a p-th root of every element supported on p-divisible
   exponents with coefficients in k^p. Hence a^p and b^p lie in every AJ, giving
   (a/b)^p in every KJ.
6. Clear denominators in the finite basis of step 4 to prove its independence
   over KJ. Comparing the expansion of h in A intersect KJ with h times the basis
   vector 1 gives A intersect KJ = AJ.
7. Write z in every KJ as f/b^p, with f in A and b nonzero. Since b^p lies in
   every AJ, step 6 puts f in every AJ. Step 3 puts its coefficients in k^p,
   and step 5 gives f = h^p. Thus z = (h/b)^p, proving the intersection equality.
8. The generators of kJ for J union J' lie in both smaller fields. The coefficient
   conditions imply the same inclusions for AJ, and taking quotients gives the
   required inclusion for KJ. -/
theorem powerSeriesRingSubfields
    (p : ℕ) [Fact p.Prime]
    (k : Type u) [Field k] [CharP k p]
    (I : Type w) (t : I → k)
    (hpb : ∃ b : Module.Basis
      {E : I →₀ ℕ // ∀ i : I, E i < p}
      (IntermediateField.adjoin (ZMod p) (Set.range (fun x : k => x ^ p))) k,
      ∀ E, b E = (E : I →₀ ℕ).prod (fun i e => t i ^ e))
    (n m : ℕ)
    (K : Type v) [Field K]
    [Algebra (MvPolynomial (Fin m) (MvPowerSeries (Fin n) k)) K]
    [IsFractionRing (MvPolynomial (Fin m) (MvPowerSeries (Fin n) k)) K]
    (kJ : Finset I → Subfield k)
    (hkJ : ∀ J, kJ J = Subfield.closure
      (Set.range (fun x : k => x ^ p) ∪ {x : k | ∃ i : I, i ∉ J ∧ t i = x}))
    (AJ : Finset I → Subring (MvPolynomial (Fin m) (MvPowerSeries (Fin n) k)))
    (hAJ : ∀ J f, f ∈ AJ J ↔
      ∀ (a : Fin n →₀ ℕ) (g : Fin m →₀ ℕ),
        MvPowerSeries.coeff a (MvPolynomial.coeff g f) ∈ kJ J ∧
        (MvPowerSeries.coeff a (MvPolynomial.coeff g f) ≠ 0 →
          (∀ i, p ∣ a i) ∧ (∀ j, p ∣ g j)))
    (KJ : Finset I → Subfield K)
    (hKJ : ∀ J z, z ∈ KJ J ↔
      ∃ a b : AJ J, (b : MvPolynomial (Fin m) (MvPowerSeries (Fin n) k)) ≠ 0 ∧
        z = algebraMap (MvPolynomial (Fin m) (MvPowerSeries (Fin n) k)) K a /
          algebraMap (MvPolynomial (Fin m) (MvPowerSeries (Fin n) k)) K b) :
    (∀ J : Finset I,
      Module.Finite (AJ J) (MvPolynomial (Fin m) (MvPowerSeries (Fin n) k))) ∧
      (∀ J : Finset I, Set.range (fun x : K => x ^ p) ⊆ (KJ J : Set K)) ∧
      (Set.range (fun x : K => x ^ p) = ⋂ J : Finset I, (KJ J : Set K)) ∧
      (∀ J J' : Finset I, KJ (J ∪ J') ≤ KJ J ⊓ KJ J') := by
  sorry

end RingTheory
