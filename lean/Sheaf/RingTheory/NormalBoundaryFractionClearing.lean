/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N8
-/
module

public import Sheaf.RingTheory.HeightOneFractionOrder
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
import WeilConjectures.RingTheory.NormalDomainPrincipalQuotientAssociatedHeight
import WeilConjectures.RingTheory.InjectivePiLocalizationAssociatedPrimes

/-!
# Clearing a boundary-supported fraction and its inverse

Source: Stacks Project, Algebra, Tags 00PD, 031S and 031T; the simultaneous
valuation-clearing consequence extracted from the boundary-class injectivity proof
(blueprint: lem-trf-normal-boundary-fraction-clearing).
-/

@[expose] public section

universe u v

namespace Ring

/-- A boundary-supported fraction and its inverse can be cleared by powers of a
ring element positive at precisely the listed height-one primes. Every pair of
nonnegative exponents satisfying the two valuation inequalities works.

Source: Stacks Project, Algebra, Tags 00PD, 031S and 031T
(blueprint: lem-trf-normal-boundary-fraction-clearing).

Proof (the four steps of the DAG node):
1. Write `a_i = v_i(f)` and `b_i = v_i(τ) > 0`, so `b_i ≥ 1`. The maxima of
   `{0} ∪ {-a_i}` and `{0} ∪ {a_i}` give admissible natural exponents `N,H`.
   The sets are finite, even when the index type is empty.
2. For any admissible pair, valuation additivity makes `f τ^N` and `f⁻¹ τ^H`
   nonnegative at each listed prime and zero at every other height-one prime.
   The DVR membership criterion of lem-trf-normal-domain-principal-divisor-kernel
   puts both elements in every height-one localization.
3. For either element write `g = a/b`, with `b ≠ 0`. The theorem
   lem-weil-pbc-normal-domain-principal-quotient-associated-height puts every
   associated prime of `R/bR` in height one. Membership in its localization
   gives `a/b = c/s` with `s` outside that prime, hence `sa = bc`. Thus `s`
   kills the class of `a`. The elementwise criterion in
   lem-weil-pbc-module-injects-localizations-associated-primes gives `a ∈ bR`,
   proving `g ∈ R`. The associated-prime set may be empty.
4. In the fraction field cancellation gives the product `τ^(N+H)`. Injectivity
   of the algebra map gives the equality in `R`. For an empty boundary the
   maxima are zero, and the same proof gives `f,f⁻¹ ∈ R` with product one. -/
theorem normal_boundary_fraction_clearing
    (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]
    (I : Type v) [Finite I] (p : I → WeilHeightOnePrime R)
    (hdistinct : Function.Injective p) (τ : R) (hτ : τ ≠ 0)
    (hpositive : ∀ i : I,
      0 < weilFractionOrder (p i) (algebraMap R (FractionRing R) τ))
    (hτoutside : ∀ q : WeilHeightOnePrime R, q ∉ Set.range p →
      weilFractionOrder q (algebraMap R (FractionRing R) τ) = 0)
    (f : (FractionRing R)ˣ)
    (hfoutside : ∀ q : WeilHeightOnePrime R, q ∉ Set.range p →
      weilFractionOrder q (f : FractionRing R) = 0) :
    (∃ N H : ℕ, ∃ h h' : R,
      algebraMap R (FractionRing R) h =
        (f : FractionRing R) * algebraMap R (FractionRing R) τ ^ N ∧
      algebraMap R (FractionRing R) h' =
        ((f⁻¹ : (FractionRing R)ˣ) : FractionRing R) *
          algebraMap R (FractionRing R) τ ^ H ∧
      h * h' = τ ^ (N + H)) ∧
    (∀ N H : ℕ,
      (∀ i : I,
        0 ≤ weilFractionOrder (p i) (f : FractionRing R) +
          (N : ℤ) * weilFractionOrder (p i) (algebraMap R (FractionRing R) τ) ∧
        0 ≤ -weilFractionOrder (p i) (f : FractionRing R) +
          (H : ℤ) * weilFractionOrder (p i) (algebraMap R (FractionRing R) τ)) →
      ∃ h h' : R,
        algebraMap R (FractionRing R) h =
          (f : FractionRing R) * algebraMap R (FractionRing R) τ ^ N ∧
        algebraMap R (FractionRing R) h' =
          ((f⁻¹ : (FractionRing R)ˣ) : FractionRing R) *
            algebraMap R (FractionRing R) τ ^ H ∧
        h * h' = τ ^ (N + H)) := by
  sorry

end Ring
