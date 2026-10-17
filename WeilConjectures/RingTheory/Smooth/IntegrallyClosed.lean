/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.RingTheory.Etale.IntegrallyClosed
public import Mathlib.RingTheory.Polynomial.IsIntegral
public import Mathlib.RingTheory.RingHom.StandardSmooth
public import Mathlib.RingTheory.Smooth.StandardSmoothOfFree
public import Mathlib.RingTheory.Localization.LocalizationLocalization

/-!
# Smooth algebras over a normal domain are normal

Let `R` be an integrally closed domain and `B` a smooth `R`-algebra. Every localization of `B` at
a prime ideal is an integrally closed domain
(`Algebra.Smooth.isDomain_and_isIntegrallyClosed_localization`, [Stacks 033C]): locally `B` is
étale over a polynomial ring over `R`, which is normal, and étale algebras over a normal domain
are normal (`Algebra.Etale.isDomain_and_isIntegrallyClosed_of_isLocalization`).
-/

@[expose] public section

universe u

/-- A polynomial ring in finitely many variables over an integrally closed domain is integrally
closed. -/
instance MvPolynomial.isIntegrallyClosed_fin {R : Type u} [CommRing R] [IsDomain R]
    [IsIntegrallyClosed R] (n : ℕ) : IsIntegrallyClosed (MvPolynomial (Fin n) R) := by
  induction n with
  | zero => exact .of_equiv (MvPolynomial.isEmptyAlgEquiv R (Fin 0)).toRingEquiv.symm
  | succ n ih => exact .of_equiv (MvPolynomial.finSuccEquiv R n).toRingEquiv.symm

namespace Algebra

/-- **Smooth algebras over a normal domain are normal** ([Stacks 033C]). The localizations of a
smooth algebra `B` over an integrally closed domain `R` at its primes are integrally closed
domains. -/
theorem Smooth.isDomain_and_isIntegrallyClosed_localization (R B : Type u) [CommRing R]
    [IsDomain R] [IsIntegrallyClosed R] [CommRing B] [Algebra R B] [Smooth R B] (P : Ideal B)
    [P.IsPrime] :
    IsDomain (Localization.AtPrime P) ∧ IsIntegrallyClosed (Localization.AtPrime P) := by
  obtain ⟨s, hs, H⟩ := Smooth.exists_span_eq_top_isStandardSmooth R B
  obtain ⟨x, hxs, hxP⟩ : ∃ x ∈ s, x ∉ P := by
    by_contra! h
    exact Ideal.IsPrime.ne_top inferInstance (top_le_iff.mp (hs ▸ Ideal.span_le.mpr h :))
  obtain ⟨ι, σ, _, _, Q⟩ := (H x hxs).out
  have := Q.some.isStandardSmoothOfRelativeDimension rfl
  obtain ⟨g, hg⟩ := IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial
    Q.some.dimension R (Localization.Away x)
  algebraize [g.toRingHom]
  have hdisj : Disjoint (Submonoid.powers x : Set B) P := by
    rw [Set.disjoint_left]
    rintro _ ⟨n, rfl⟩ hn
    exact hxP (Ideal.IsPrime.mem_of_pow_mem inferInstance n hn)
  set P' := P.map (algebraMap B (Localization.Away x))
  have : P'.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers x) _ P
    inferInstance hdisj
  have hP' : P'.comap (algebraMap B (Localization.Away x)) = P :=
    IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers x) (Localization.Away x)
      inferInstance hdisj
  clear_value P'
  obtain ⟨h1, h2⟩ := Etale.isDomain_and_isIntegrallyClosed_of_isLocalization
    (R := MvPolynomial (Fin Q.some.dimension) R) P' (Localization.AtPrime P')
  subst hP'
  let e := (IsLocalization.localizationLocalizationAtPrimeIsoLocalization
    (Submonoid.powers x) P').toRingEquiv.symm
  exact ⟨e.isDomain_iff.1 h1, .of_equiv e⟩

end Algebra
