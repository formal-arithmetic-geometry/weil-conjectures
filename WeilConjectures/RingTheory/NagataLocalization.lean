/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.NagataRing
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
import WeilConjectures.RingTheory.LocalizationJapaneseDomain
import WeilConjectures.RingTheory.N2AscendsFiniteDomainExtension
import Mathlib.RingTheory.Localization.Submodule

/-!
# Localizations of Nagata rings

A localization of a Nagata ring is Nagata.

## Implementation details

The localization is Noetherian. For a prime `q` of the localization with inverse image `p`, the
quotient by `q` is a localization of `A/p`, which is N-2 since `A/p` is; this property is
transported along the isomorphism by identifying fraction fields, finite extensions and integral
closures.

## References

* [Stacks, Tag 032U]
-/

@[expose] public section

universe u

/-- A localization of a Nagata ring is Nagata, including the localizations at prime ideals
and the principal localizations. `IsNagataRing` asserts both Noetherianity and the N-2
property of every prime quotient. -/
theorem isNagataRing_localization (A : Type u) [CommRing A] (T : Submonoid A)
    (hA : IsNagataRing A) :
    IsNagataRing (Localization T) ∧
      (∀ (p : Ideal A) [p.IsPrime], IsNagataRing (Localization.AtPrime p)) ∧
      (∀ f : A, IsNagataRing (Localization.Away f)) := by
  have localized (U : Submonoid A) : IsNagataRing (Localization U) := by
    have : IsNoetherianRing A := hA.1
    refine ⟨inferInstance, ?_⟩
    intro q hq
    let p := q.under A
    have : p.IsPrime := inferInstance
    let S := Algebra.algebraMapSubmonoid (A ⧸ p) U
    have hS : (0 : A ⧸ p) ∉ S := by
      rintro ⟨t, ht, hzero⟩
      have hmem : t ∈ p := Ideal.Quotient.eq_zero_iff_mem.mp hzero
      exact Set.disjoint_left.mp
        ((IsLocalization.isPrime_iff_isPrime_disjoint U (Localization U) q).mp hq).2 ht hmem
    have heq : p.map (algebraMap A (Localization U)) = q :=
      IsLocalization.map_under U (Localization U) q
    have : IsLocalization S ((Localization U) ⧸ q) :=
      IsLocalization.of_surjective U (Localization U)
        (Ideal.Quotient.mk p) Ideal.Quotient.mk_surjective
        (Ideal.Quotient.mk q) Ideal.Quotient.mk_surjective rfl (by simp [heq])
    obtain ⟨hD, a, hF, _, _, _, _, hn2⟩ :=
      localization_isN1_isN2 (A ⧸ p) (FractionRing (A ⧸ p)) S hS
    let : IsDomain (Localization S) := hD
    let : Algebra (Localization S) (FractionRing (A ⧸ p)) := a
    let : IsFractionRing (Localization S) (FractionRing (A ⧸ p)) := hF
    have : IsNoetherianRing (A ⧸ p) := IsNoetherianRing.of_finite A (A ⧸ p)
    have hN2 := hn2 (hA.2 p)
    let e := (IsLocalization.algEquiv S (Localization S) ((Localization U) ⧸ q)).toRingEquiv
    let : Algebra (Localization S) ((Localization U) ⧸ q) := e.toRingHom.toAlgebra
    have : Module.Finite (Localization S) ((Localization U) ⧸ q) :=
      RingHom.Finite.of_surjective e.toRingHom e.surjective
    exact isN2_of_finite_domain_extension (Localization S) ((Localization U) ⧸ q)
      (FractionRing (A ⧸ p)) (FractionRing ((Localization U) ⧸ q)) e.injective hN2
  refine ⟨localized T, ?_, ?_⟩
  · intro p
    exact localized p.primeCompl
  · intro f
    exact localized (Submonoid.powers f)
