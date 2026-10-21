/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NI
-/
module

public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Mathlib.LinearAlgebra.FreeModule.Basic
import Sheaf.NumberTheory.Padics.LocalFieldIntegralBasis
import Mathlib.Topology.Algebra.Valued.LocallyCompact

/-!
# Ramified finite coefficient stages of local fields

Source: Weil blueprint, main-20261015, smooth-purity,
`sk-lem-sp-field-extension-towers.proof.md`, Part (1)
(blueprint: lem-pur-local-field-coefficient-stages).
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace Padic

/-- Finite extensions of coefficient fields give finite free integer rings and
finite free ramified coefficient stages, independently of unit changes of uniformizers.

Source: Weil blueprint, main-20261015,
`sk-lem-sp-field-extension-towers.proof.md`, Part (1), and rational/qbar purity,
Steps 1–2 (blueprint: lem-pur-local-field-coefficient-stages).

Proof:
1. The coefficient-extension DVR theorem identifies both integer rings and their
   maximal ideals with the closed and open unit balls. Compatibility of absolute
   values therefore restricts the field inclusion to the ring homomorphism `f`.
2. Apply `lem-sfb-local-field-integral-basis` to obtain a finite integral basis;
   this proves `Module.Free` and `Module.Finite` for the scalar action given by `f`.
3. Apply `lem-weil-pbc-dvr-unit-times-uniformizer-power` in the upper DVR to `f t`.
   It is nonzero; its absolute value is less than one, so the exponent is positive.
   Raising `f t = u * v^e` to the nth power gives equality of the principal ideals.
4. Reduce the integral basis modulo `t^n`. Coordinates prove surjectivity; if a
   linear combination lies in `t^n S`, divide its coordinates by `t^n` to prove
   injectivity. The scalar map is the unique map taking `[r]` to `[f r]`.
5. Apply `lem-weil-valued-dvr-finite-quotients` at exponents `n` and `e*n`.
   The rings are finite and local. The image of the coefficient prime has
   positive valuation, so `l = w*t^a` for a unit and `a ≥ 1`. Consequently `l^n`
   vanishes in both level-n rings.
6. For a positive `k`, take `n = k` to see `k ≤ e*n`. Quotient transition maps
   for `m ≤ n` are induced by the identity on representatives.
7. Multiplication of either uniformizer by a unit leaves every principal-power
   ideal unchanged. Equal ideals give the canonical identity-on-representatives
   quotient equivalences. The quotient projections are heterogeneously equal,
   as are the scalar maps, which are specified on representatives. Transition
   maps are determined by their composites with these projections, so commute
   with the same identifications. This concerns the rings and maps,
   independently of any integral basis.
-/
theorem local_field_coefficient_stages
    (l : ℕ) [Fact l.Prime] (E : Type u) (F : Type v) [Field E] [Field F]
    [Algebra (Padic l) E] [Algebra (Padic l) F] [Algebra E F]
    [IsScalarTower (Padic l) E F]
    [FiniteDimensional (Padic l) E] [FiniteDimensional (Padic l) F]
    (hcompat : ∀ x : E,
      coefficientExtensionAbsoluteValue l F (algebraMap E F x) =
        coefficientExtensionAbsoluteValue l E x)
    (t : coefficientExtensionIntegers l E) (v : coefficientExtensionIntegers l F)
    (ht : Ideal.span ({t} : Set (coefficientExtensionIntegers l E)) =
      coefficientExtensionMaximalIdeal l E)
    (hv : Ideal.span ({v} : Set (coefficientExtensionIntegers l F)) =
      coefficientExtensionMaximalIdeal l F) :
    ∃ f : coefficientExtensionIntegers l E →+* coefficientExtensionIntegers l F,
      (∀ x, (f x : F) = algebraMap E F (x : E)) ∧
      @Module.Free _ _ _ _ f.toAlgebra.toModule ∧
      @Module.Finite _ _ _ _ f.toAlgebra.toModule ∧
      ∃ (e : ℕ) (w : (coefficientExtensionIntegers l F)ˣ),
        1 ≤ e ∧ f t = (w : coefficientExtensionIntegers l F) * v ^ e ∧
        (∀ n : ℕ, 1 ≤ n →
          Ideal.span ({f t ^ n} : Set (coefficientExtensionIntegers l F)) =
            Ideal.span ({v ^ (e * n)} : Set (coefficientExtensionIntegers l F)) ∧
          Finite (coefficientExtensionIntegers l E ⧸ Ideal.span {t ^ n}) ∧
          IsLocalRing (coefficientExtensionIntegers l E ⧸ Ideal.span {t ^ n}) ∧
          Finite (coefficientExtensionIntegers l F ⧸ Ideal.span {f t ^ n}) ∧
          IsLocalRing (coefficientExtensionIntegers l F ⧸ Ideal.span {f t ^ n}) ∧
          (∃ N : ℕ, 1 ≤ N ∧
            (l : coefficientExtensionIntegers l E ⧸ Ideal.span {t ^ n}) ^ N = 0 ∧
            (l : coefficientExtensionIntegers l F ⧸ Ideal.span {f t ^ n}) ^ N = 0) ∧
          ∃ g : (coefficientExtensionIntegers l E ⧸ Ideal.span {t ^ n}) →+*
              (coefficientExtensionIntegers l F ⧸ Ideal.span {f t ^ n}),
            (∀ x, g (Ideal.Quotient.mk (Ideal.span {t ^ n}) x) =
              Ideal.Quotient.mk (Ideal.span {f t ^ n}) (f x)) ∧
            @Module.Free _ _ _ _ g.toAlgebra.toModule ∧
            @Module.Finite _ _ _ _ g.toAlgebra.toModule) ∧
        (∀ k : ℕ, 1 ≤ k → ∃ n : ℕ, 1 ≤ n ∧ k ≤ e * n) ∧
        (∀ m n : ℕ, 1 ≤ m → m ≤ n →
          ∃ (qR : (coefficientExtensionIntegers l E ⧸ Ideal.span {t ^ n}) →+*
                (coefficientExtensionIntegers l E ⧸ Ideal.span {t ^ m}))
            (qS : (coefficientExtensionIntegers l F ⧸ Ideal.span {f t ^ n}) →+*
                (coefficientExtensionIntegers l F ⧸ Ideal.span {f t ^ m}))
            (qV : (coefficientExtensionIntegers l F ⧸ Ideal.span {v ^ n}) →+*
                (coefficientExtensionIntegers l F ⧸ Ideal.span {v ^ m})),
            (∀ x, qR (Ideal.Quotient.mk (Ideal.span {t ^ n}) x) =
              Ideal.Quotient.mk (Ideal.span {t ^ m}) x) ∧
            (∀ x, qS (Ideal.Quotient.mk (Ideal.span {f t ^ n}) x) =
              Ideal.Quotient.mk (Ideal.span {f t ^ m}) x) ∧
            (∀ x, qV (Ideal.Quotient.mk (Ideal.span {v ^ n}) x) =
              Ideal.Quotient.mk (Ideal.span {v ^ m}) x)) ∧
        (∀ (a : (coefficientExtensionIntegers l E)ˣ)
            (b : (coefficientExtensionIntegers l F)ˣ),
          (∀ n : ℕ,
            Ideal.span ({(↑a * t) ^ n} :
                Set (coefficientExtensionIntegers l E)) = Ideal.span {t ^ n} ∧
            Ideal.span ({f (↑a * t) ^ n} :
                Set (coefficientExtensionIntegers l F)) = Ideal.span {f t ^ n} ∧
            Ideal.span ({(↑b * v) ^ n} :
                Set (coefficientExtensionIntegers l F)) = Ideal.span {v ^ n}) ∧
          (∀ (n : ℕ)
              (g : (coefficientExtensionIntegers l E ⧸ Ideal.span {t ^ n}) →+*
                (coefficientExtensionIntegers l F ⧸ Ideal.span {f t ^ n}))
              (g' : (coefficientExtensionIntegers l E ⧸ Ideal.span {(↑a * t) ^ n}) →+*
                (coefficientExtensionIntegers l F ⧸ Ideal.span {f (↑a * t) ^ n})),
            (∀ x, g (Ideal.Quotient.mk (Ideal.span {t ^ n}) x) =
              Ideal.Quotient.mk (Ideal.span {f t ^ n}) (f x)) →
            (∀ x, g' (Ideal.Quotient.mk (Ideal.span {(↑a * t) ^ n}) x) =
              Ideal.Quotient.mk (Ideal.span {f (↑a * t) ^ n}) (f x)) → HEq g g') ∧
          (∀ n : ℕ,
            HEq (Ideal.Quotient.mk (Ideal.span {(↑a * t) ^ n}))
              (Ideal.Quotient.mk (Ideal.span {t ^ n})) ∧
            HEq (Ideal.Quotient.mk (Ideal.span {f (↑a * t) ^ n}))
              (Ideal.Quotient.mk (Ideal.span {f t ^ n})) ∧
            HEq (Ideal.Quotient.mk (Ideal.span {(↑b * v) ^ n}))
              (Ideal.Quotient.mk (Ideal.span {v ^ n})))) := by
  sorry

end Padic
