/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NB
-/
module

public import Mathlib.RingTheory.Valuation.ValuationRing
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Localization.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Residue comparison for relative integral closure

Source: Temkin, *Stable modification of relative curves*, Theorem 3.5.5, Step 4,
printed pp. 23–24 (blueprint: lem-trf-valuation-finite-height-composition).

The localization is represented by its subalgebra in the generic algebra. `IsLocalization`
characterizes that subalgebra by the usual localization universal property. Images of ideals
are set images in the common ambient ring, retaining the assertion that no new elements of
the extended prime appear upon localization.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warn.sorry false

universe u v w

open scoped TensorProduct

/-- Residue comparison for relative integral closure over a valuation ring.
Source: Temkin, *Stable modification of relative curves*, Theorem 3.5.5, Step 4,
printed pp. 23–24 (blueprint: lem-trf-valuation-finite-height-composition).

Proof plan: if `A` is zero, every algebra and quotient here is zero. Otherwise, for
`q ∈ p` and `t ∉ p`, valuation-ring divisibility implies `q/t ∈ V`: the alternative
`t/q ∈ V` contradicts `t ∉ p`. Primality then gives `q/t ∈ p` (and `q = 0` is immediate).
Writing elements of `pS` as finite sums of `q * (a/t)` shows that its underlying set
is the image of `pA`. Every element of the integral closure is integral over `S`, so
relative integral closedness puts it in `S`; squeezing the three extended primes gives
the two set equalities. The common ideal lies in `A` and in its integral closure, hence
the restrictions of the quotient map have precisely the indicated kernels and induce
the two injective quotient maps. Reducing a monic equation gives the forward integral
closure inclusion on quotients. Conversely, lift an integral residue to `z ∈ S` and
lift a monic equation to `P ∈ A[X]`. Its error `P(z)` lies in `pS = pA`, so comes from
`e ∈ A`. The monic polynomial `P - e` vanishes at `z`, proving `z` belongs to the
integral closure. These steps use only `def-trf-valuation-ring` and
`def-weil-pbc-integral-closure`, with no height or finiteness restriction. -/
theorem valuation_finite_height_composition
    (V : Type u) [CommRing V] [IsDomain V] [ValuationRing V]
    (K : Type v) [Field K] [Algebra V K] [IsFractionRing V K]
    (A : Type w) [CommRing A] [Algebra V A] [Module.IsTorsionFree V A]
    (p : Ideal V) [p.IsPrime] (hp0 : p ≠ ⊥)
    (S : Subalgebra A (A ⊗[V] K))
    [IsLocalization (p.primeCompl.map (algebraMap V A)) S]
    (hclosed : IsIntegrallyClosedIn S (A ⊗[V] K)) :
    ∃ hB : integralClosure A (A ⊗[V] K) ≤ S,
      (algebraMap A (A ⊗[V] K)) '' (Ideal.map (algebraMap V A) p : Set A) =
        (algebraMap (integralClosure A (A ⊗[V] K)) (A ⊗[V] K)) ''
          (Ideal.map (algebraMap A (integralClosure A (A ⊗[V] K)))
            (Ideal.map (algebraMap V A) p) : Set (integralClosure A (A ⊗[V] K))) ∧
      (algebraMap (integralClosure A (A ⊗[V] K)) (A ⊗[V] K)) ''
          (Ideal.map (algebraMap A (integralClosure A (A ⊗[V] K)))
            (Ideal.map (algebraMap V A) p) : Set (integralClosure A (A ⊗[V] K))) =
        (algebraMap S (A ⊗[V] K)) ''
          (Ideal.map (algebraMap A S) (Ideal.map (algebraMap V A) p) : Set S) ∧
      (∃ f : (A ⧸ Ideal.map (algebraMap V A) p) →+*
          ((integralClosure A (A ⊗[V] K)) ⧸
            Ideal.map (algebraMap A (integralClosure A (A ⊗[V] K)))
              (Ideal.map (algebraMap V A) p)),
        Function.Injective f ∧ ∀ x : A,
          f (Ideal.Quotient.mk (Ideal.map (algebraMap V A) p) x) =
            Ideal.Quotient.mk _ (algebraMap A (integralClosure A (A ⊗[V] K)) x)) ∧
      (∃ g : ((integralClosure A (A ⊗[V] K)) ⧸
            Ideal.map (algebraMap A (integralClosure A (A ⊗[V] K)))
              (Ideal.map (algebraMap V A) p)) →+*
          (S ⧸ Ideal.map (algebraMap A S) (Ideal.map (algebraMap V A) p)),
        Function.Injective g ∧ ∀ x : integralClosure A (A ⊗[V] K),
          g (Ideal.Quotient.mk _ x) =
            Ideal.Quotient.mk _ (Subalgebra.inclusion hB x)) ∧
      (∀ z : S ⧸ Ideal.map (algebraMap A S) (Ideal.map (algebraMap V A) p),
        IsIntegral (A ⧸ Ideal.map (algebraMap V A) p) z ↔
          ∃ x : integralClosure A (A ⊗[V] K),
            Ideal.Quotient.mk _ (Subalgebra.inclusion hB x) = z) := by
  sorry

end
