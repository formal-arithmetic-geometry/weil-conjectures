module

public import Mathlib.RingTheory.Localization.Defs
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
public import Mathlib.Algebra.Polynomial.Degree.TrailingDegree
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Order.Interval.Finset.Nat

/-! # Integral localization and comparison with a fraction field

Source: Stacks Project, Tags 00GS and 00CP; the explicit coefficient certificate is
an expansion of the blueprint proof (blueprint: lem-sfb-integral-localization-fraction-comparison).
-/

@[expose] public section

set_option autoImplicit false

universe u v w z

namespace IsLocalization

/-- An integral extension of domains localized at the nonzero base elements has the
specified monic-equation inverse certificates and is canonically the fraction field.
Here `p.natDegree` is the equation degree, `p.natTrailingDegree` is its least nonzero
coefficient index, and the sum over `Finset.Ioc` is the element called `d` in the source.
`Ring.inverse` denotes the inverse of a unit in the commutative ring `C`.

Source: Stacks Project, Tag 00GS (lemma-integral-over-field, part 2), with the explicit
certificate expanded from the blueprint proof, and Tag 00CP for the comparison map
(blueprint: lem-sfb-integral-localization-fraction-comparison).

Proof:
1. The monic leading coefficient is 1, so a least nonzero coefficient exists. If its
   index were the degree, the equation would be `b ^ n = 0`, contrary to `b ≠ 0`
   in the domain, including `n = 0`. Factor out `b ^ i` and cancel it to obtain
   `φ(a_i) + b * d = 0` (def-weil-polynomial-ring).
2. Injectivity makes `φ(a_i)` nonzero. It belongs to the localization submonoid,
   so its image is a unit. Apply the localization map to the preceding equation
   and multiply by the negative inverse to obtain the displayed inverse certificate.
   Integrality supplies an equation for each nonzero `b`, proving the unit assertion
   (lem-weil-pbc-ring-localization-universal-property).
3. The images in `L` of all denominators are nonzero, hence units. The localization
   universal property constructs the unique comparison extending `j`, with the
   asserted fraction formula (def-weil-field and the localization dependency).
4. Represent two elements of `C` as fractions. Equality of their images in `L`
   gives equality of cross-products by injectivity of `j`. The localization fraction
   equality criterion, with multiplier 1, gives equality in `C`.
5. Write any element of `L` as `j(u) / j(v)` with `v ≠ 0`. The certificate gives an
   inverse of the image of `v` in `C`, which the comparison sends to `j(v)⁻¹`.
   Multiplying it by the image of `u` proves surjectivity. No finiteness or
   Noetherian condition is used.
-/
theorem integral_localization_fraction_comparison
    (A : Type u) (B : Type v) (C : Type w)
    [CommRing A] [IsDomain A] [CommRing B] [IsDomain B] [CommRing C]
    [Algebra A B] [Algebra B C]
    [IsLocalization (Algebra.algebraMapSubmonoid B (nonZeroDivisors A)) C]
    (hφ : Function.Injective (algebraMap A B))
    (hIntegral : ∀ b : B, IsIntegral A b) :
    (∀ (b : B), b ≠ 0 → ∀ (p : Polynomial A), p.Monic →
      p.eval₂ (algebraMap A B) b = 0 →
      p.natTrailingDegree < p.natDegree ∧
      algebraMap A B (p.coeff p.natTrailingDegree) +
        b * (∑ j ∈ Finset.Ioc p.natTrailingDegree p.natDegree,
          algebraMap A B (p.coeff j) * b ^ (j - p.natTrailingDegree - 1)) = 0 ∧
      algebraMap B C b *
        (-algebraMap B C (∑ j ∈ Finset.Ioc p.natTrailingDegree p.natDegree,
          algebraMap A B (p.coeff j) * b ^ (j - p.natTrailingDegree - 1)) *
          Ring.inverse (algebraMap B C (algebraMap A B (p.coeff p.natTrailingDegree)))) = 1) ∧
    (∀ b : B, b ≠ 0 → IsUnit (algebraMap B C b)) ∧
    (∀ (L : Type z) [Field L] [Algebra B L],
      Function.Injective (algebraMap B L) →
      (∀ ℓ : L, ∃ b b' : B, b' ≠ 0 ∧
        ℓ = algebraMap B L b * (algebraMap B L b')⁻¹) →
      ∃ q : C →+* L,
        q.comp (algebraMap B C) = algebraMap B L ∧
        (∀ q' : C →+* L, q'.comp (algebraMap B C) = algebraMap B L → q' = q) ∧
        Function.Bijective q ∧
        ∀ (b : B) (a : A), a ≠ 0 →
          q (algebraMap B C b * Ring.inverse (algebraMap B C (algebraMap A B a))) =
            algebraMap B L b * (algebraMap B L (algebraMap A B a))⁻¹) := by
  sorry

end IsLocalization
