module

public import Sheaf.RingTheory.AdicRingCompletionMap
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Spectrum.Maximal.Basic
public import Mathlib.RingTheory.Spectrum.Prime.RingHom
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic

/-!
# Semilocal completions and normalized principal boundaries

Source: Kurano–Shimomoto, Ideal-adic completion of quasi-excellent rings (after Gabber),
Theorem 5.3, printed p. 11 (blueprint: def-per-rotthaus-boundary-system).
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace RingTheory.Rotthaus

/-- Denominators outside every maximal ideal in the finite set.
Source: Kurano–Shimomoto, Theorem 5.3 (blueprint: def-per-rotthaus-boundary-system). -/
def denominators {B : Type u} [CommRing B] (γ : Finset (MaximalSpectrum B)) :
    Submonoid B :=
  ⨅ m : γ, m.val.toPrimeSpectrum.asIdeal.primeCompl

/-- The semilocal ring of fractions with the specified denominators.
Source: Kurano–Shimomoto, Theorem 5.3 (blueprint: def-per-rotthaus-boundary-system). -/
abbrev Semilocalization {B : Type u} [CommRing B] (γ : Finset (MaximalSpectrum B)) :=
  Localization (denominators γ)

/-- Principal completion of the localization at a maximal ideal.
Source: Kurano–Shimomoto, Theorem 5.3 (blueprint: def-per-rotthaus-boundary-system). -/
abbrev LocalCompletion {B : Type u} [CommRing B] (x : B) (n : MaximalSpectrum B) :=
  AdicCompletion (Ideal.span {algebraMap B (Localization.AtPrime n.asIdeal) x})
    (Localization.AtPrime n.asIdeal)

/-- Principal completion of the semilocal ring of fractions.
Source: Kurano–Shimomoto, Theorem 5.3 (blueprint: def-per-rotthaus-boundary-system). -/
abbrev Completion {B : Type u} [CommRing B] (x : B) (γ : Finset (MaximalSpectrum B)) :=
  AdicCompletion (Ideal.span {algebraMap B (Semilocalization γ) x}) (Semilocalization γ)

/-- Canonical localization map when the finite set contains the chosen maximal ideal.
Source: Kurano–Shimomoto, Theorem 5.3 (blueprint: def-per-rotthaus-boundary-system). -/
noncomputable def toLocal {B : Type u} [CommRing B] (n : MaximalSpectrum B)
    (γ : Finset (MaximalSpectrum B)) (hn : n ∈ γ) :
    Semilocalization γ →ₐ[B] Localization.AtPrime n.asIdeal :=
  IsLocalization.liftAlgHom (M := denominators γ) (f := Algebra.ofId B _)
    (fun y ↦ IsLocalization.map_units (M := n.asIdeal.primeCompl) (Localization.AtPrime n.asIdeal)
      ⟨y.val, (iInf_le (fun m : γ ↦ m.val.toPrimeSpectrum.asIdeal.primeCompl)
        ⟨n, hn⟩) y.property⟩)

/-- Canonical map of principal completions, induced on every residue by `toLocal`.
Source: Kurano–Shimomoto, Theorem 5.3 (blueprint: def-per-rotthaus-boundary-system). -/
noncomputable def completionToLocal {B : Type u} [CommRing B] (x : B)
    (n : MaximalSpectrum B) (γ : Finset (MaximalSpectrum B)) (hn : n ∈ γ) :
    Completion x γ →+* LocalCompletion x n := by
  have h : (toLocal n γ hn).toRingHom (algebraMap B (Semilocalization γ) x) =
      algebraMap B (Localization.AtPrime n.asIdeal) x := (toLocal n γ hn).commutes x
  change AdicCompletion (Ideal.span {algebraMap B (Semilocalization γ) x})
    (Semilocalization γ) →+*
      AdicCompletion (Ideal.span {algebraMap B (Localization.AtPrime n.asIdeal) x})
        (Localization.AtPrime n.asIdeal)
  rw [← h]
  exact AdicCompletion.principalRingMap (toLocal n γ hn).toRingHom
    (algebraMap B (Semilocalization γ) x)

/-- Contraction of a prime of the local completion to a semilocal completion.
Source: Kurano–Shimomoto, Theorem 5.3 (blueprint: def-per-rotthaus-boundary-system). -/
noncomputable def contractedPrime {B : Type u} [CommRing B] (x : B)
    (n : MaximalSpectrum B) (s : PrimeSpectrum (LocalCompletion x n))
    (γ : Finset (MaximalSpectrum B)) (hn : n ∈ γ) : PrimeSpectrum (Completion x γ) :=
  PrimeSpectrum.comap (completionToLocal x n γ hn) s

/-- Normalization of the contracted-prime quotient in its own fraction field.
Source: Kurano–Shimomoto, Theorem 5.3 (blueprint: def-per-rotthaus-boundary-system). -/
noncomputable abbrev Normalization {B : Type u} [CommRing B] (x : B)
    (n : MaximalSpectrum B) (s : PrimeSpectrum (LocalCompletion x n))
    (γ : Finset (MaximalSpectrum B)) (hn : n ∈ γ) :=
  integralClosure (Completion x γ ⧸ (contractedPrime x n s γ hn).asIdeal)
    (FractionRing (Completion x γ ⧸ (contractedPrime x n s γ hn).asIdeal))

/-- The composite from the original ring to the normalized quotient.
Source: Kurano–Shimomoto, Theorem 5.3 (blueprint: def-per-rotthaus-boundary-system). -/
noncomputable def normalizationMap {B : Type u} [CommRing B] (x : B)
    (n : MaximalSpectrum B) (s : PrimeSpectrum (LocalCompletion x n))
    (γ : Finset (MaximalSpectrum B)) (hn : n ∈ γ) : B →+* Normalization x n s γ hn :=
  (algebraMap (Completion x γ ⧸ (contractedPrime x n s γ hn).asIdeal)
    (Normalization x n s γ hn)).comp
      ((Ideal.Quotient.mk (contractedPrime x n s γ hn).asIdeal).comp
        (algebraMap B (Completion x γ)))

/-- Union of contractions of primes minimal over the principal ideal in each normalization.
Source: Kurano–Shimomoto, Theorem 5.3 (blueprint: def-per-rotthaus-boundary-system). -/
noncomputable def boundary {B : Type u} [CommRing B] (x : B)
    (n : MaximalSpectrum B) (s : PrimeSpectrum (LocalCompletion x n)) : Set (Ideal B) :=
  {p | ∃ (γ : Finset (MaximalSpectrum B)) (hn : n ∈ γ)
      (Q : Ideal (Normalization x n s γ hn)),
    Q ∈ (Ideal.span {normalizationMap x n s γ hn x}).minimalPrimes ∧
      Q.comap (normalizationMap x n s γ hn) = p}

end RingTheory.Rotthaus
