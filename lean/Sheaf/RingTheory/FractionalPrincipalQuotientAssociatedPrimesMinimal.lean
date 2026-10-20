module

public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
import Sheaf.RingTheory.FractionalPrincipalQuotientAssociatedPrimesHeight

/-!
# Minimality of associated primes of a fractional principal quotient

Source: Stacks Project, Algebra, Lemma 10.157.6, Tag 031T, clause (3).
(blueprint: lem-weil-pbc-normal-domain-fractional-principal-quotient-ass-minimal)
-/

@[expose] public section
universe u v
namespace Ideal

/-- Minimal-prime part of the fractional principal quotient associated-prime argument.
Source: Stacks Project, Algebra, Lemma 10.157.6, Tag 031T, clause (3).
(blueprint: lem-weil-pbc-normal-domain-fractional-principal-quotient-ass-minimal)
The proof identifies the annihilator of an associated class, observes that it contains
`A ∩ yA`, and excludes a strictly smaller prime using the nonzero numerator and the
height-one conclusion. -/
theorem associatedPrimes_fractionalPrincipalQuotient_minimal
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsDomain A] [IsIntegrallyClosed A]
    (K : Type v) [Field K] [Algebra A K] [IsFractionRing A K] (y : K) (hy : y ≠ 0) :
    ∀ p ∈ associatedPrimes A
        (A ⧸ (Submodule.span A ({y} : Set K)).comap (Algebra.linearMap A K)),
      p ∈ Ideal.minimalPrimes
        ((Submodule.span A ({y} : Set K)).comap (Algebra.linearMap A K)) := by
  intro p hp
  let J : Ideal A :=
    (Submodule.span A ({y} : Set K)).comap (Algebra.linearMap A K)
  have hpPrime : p.IsPrime := hp.isPrime
  have hpHeight : p.height = 1 :=
    associatedPrimes_fractionalPrincipalQuotient_height A K y hy p hp
  have hpFinite : p.FiniteHeight := by
    simp [Ideal.finiteHeight_iff, hpHeight]
  have hJp : J ≤ p := by
    simpa only [Submodule.annihilator_top, Ideal.annihilator_quotient] using
      hp.annihilator_le
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective A y
  have ha : a ≠ 0 := by
    intro h
    apply hy
    rw [← hab, h, map_zero, zero_div]
  have haJ : a ∈ J := by
    change algebraMap A K a ∈ Submodule.span A ({y} : Set K)
    apply Submodule.mem_span_singleton.mpr
    refine ⟨b, ?_⟩
    rw [Algebra.smul_def, ← hab, mul_div_cancel₀]
    exact IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
  have hJ : J ≠ ⊥ := by
    intro h
    exact ha (by simpa [h] using haJ)
  have hJHeight : 1 ≤ J.height := by
    rw [Order.one_le_iff_ne_zero]
    exact Ideal.height_eq_zero_iff_eq_bot.not.mpr hJ
  exact Ideal.mem_minimalPrimes_of_height_le hJp (hpHeight ▸ hJHeight)

end Ideal
