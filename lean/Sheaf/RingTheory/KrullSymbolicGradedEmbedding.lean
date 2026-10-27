module

public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.AsSubring
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.LinearAlgebra.Quotient.Basic
import WeilConjectures.AlgebraicGeometry.Regular
import Mathlib.RingTheory.DiscreteValuationRing.Basic

/-!
# Consecutive symbolic powers in a Krull domain

Source: Swanson–Huneke, Integral Closure of Ideals, Rings, and Modules,
Definition 4.10.1 and Theorem 4.10.7, first two proof paragraphs, pp.92–93
(blueprint: lem-per-krull-symbolic-graded-embedding).
-/

@[expose] public section

universe u v

namespace Ideal

/-- Consecutive symbolic-power quotients at a height-one prime of a Krull domain
embed linearly into its prime quotient. Source: Swanson–Huneke, Definition 4.10.1
and Theorem 4.10.7, first two proof paragraphs, pp.92–93
(blueprint: lem-per-krull-symbolic-graded-embedding).

Height one is written as nonzero with no nonzero prime strictly below it.
The symbolic power is the comap of the ordinary power of the extended ideal.
The denominator in the quotient is pulled back along the subtype of the numerator,
so both quotient modules have their natural `D`-actions.

Proof (the node's denominator-clearing variant of the cited argument):
1. The localization-prime correspondence (`lem-weil-pbc-primes-of-localization`)
   makes each height-one localization one-dimensional. Hypothesis `hlocal` and
   `lem-sc-normal-dim1-dvr` make it a DVR (`def-sc-discrete-valuation-ring`).
2. Choose a nonzero `a ∈ P` generating the maximal ideal of `D_P`, by clearing
   the denominator of a uniformizer. Let `S` be the other height-one primes
   containing `a`; `hfinite` makes `S` finite.
3. For each `Q ∈ S`, choose `b_Q ∈ Q` outside `P`. Write the valuations of `a`
   and `b_Q` as positive exponents `e_Q` and `f_Q`, using
   `lem-weil-pbc-dvr-unit-times-uniformizer-power`. Set `s = ∏ Q ∈ S, b_Q^(n*e_Q)`.
   Then `s` is outside `P`, and `s/a^n` belongs to every other height-one localization:
   at `Q ∈ S` its valuation is nonnegative since `f_Q ≥ 1`; elsewhere `a` is a unit.
4. For `x ∈ P^(n)`, `s*x/a^n` also belongs to `D_P`. Thus `hinter` puts it in `D`.
   Multiplication by this fixed fraction followed by reduction modulo `P` is linear.
5. Contraction of the localized maximal ideal is `P`. Since `s` is a unit at `P`,
   the kernel condition is equivalent to `x ∈ a^(n+1)D_P`, hence to `x ∈ P^(n+1)`.
6. Powers decrease, and comap preserves inclusions, so the symbolic powers decrease.
   The linear map descends to the indicated quotient and is injective by step 5.
   Empty products and `n = 0` are included; finite generation of `D` is never used. -/
theorem exists_injective_symbolicPow_quot_succ
    (D : Type u) [CommRing D] [IsDomain D]
    (F : Type v) [Field F] [Algebra D F] [IsFractionRing D F]
    (hlocal : ∀ Q : PrimeSpectrum D,
      Q.asIdeal ≠ ⊥ ∧ (∀ q : PrimeSpectrum D, q.asIdeal < Q.asIdeal → q.asIdeal = ⊥) →
        IsNoetherianRing (Localization.AtPrime Q.asIdeal) ∧
        IsDomain (Localization.AtPrime Q.asIdeal) ∧
        IsIntegrallyClosed (Localization.AtPrime Q.asIdeal))
    (hinter : Set.range (algebraMap D F) =
      ⋂ (Q : PrimeSpectrum D)
        (_ : Q.asIdeal ≠ ⊥ ∧
          (∀ q : PrimeSpectrum D, q.asIdeal < Q.asIdeal → q.asIdeal = ⊥)),
        (Localization.subalgebra F Q.asIdeal.primeCompl
          Q.asIdeal.primeCompl_le_nonZeroDivisors : Set F))
    (hfinite : ∀ a : D, a ≠ 0 →
      {Q : PrimeSpectrum D | Q.asIdeal ≠ ⊥ ∧
        (∀ q : PrimeSpectrum D, q.asIdeal < Q.asIdeal → q.asIdeal = ⊥) ∧
        a ∈ Q.asIdeal}.Finite)
    (P : Ideal D) [P.IsPrime]
    (hP : P ≠ ⊥ ∧ (∀ q : PrimeSpectrum D, q.asIdeal < P → q.asIdeal = ⊥))
    (n : ℕ) :
    ∃ f :
      ((Ideal.comap (algebraMap D (Localization.AtPrime P))
        ((P.map (algebraMap D (Localization.AtPrime P))) ^ n)) ⧸
        Submodule.comap
          (Ideal.comap (algebraMap D (Localization.AtPrime P))
            ((P.map (algebraMap D (Localization.AtPrime P))) ^ n)).subtype
          (Ideal.comap (algebraMap D (Localization.AtPrime P))
            ((P.map (algebraMap D (Localization.AtPrime P))) ^ (n + 1)))) →ₗ[D] (D ⧸ P),
      Function.Injective f := by
  sorry

end Ideal
