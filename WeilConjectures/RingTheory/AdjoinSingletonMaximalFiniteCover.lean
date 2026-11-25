/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.NagataRing
public import WeilConjectures.RingTheory.AnalyticallyUnramified
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Localization.Submodule
import WeilConjectures.RingTheory.AdjoinSingletonFiniteCoverCore
import WeilConjectures.RingTheory.AdicCompletionRingEquiv
import Mathlib.RingTheory.LocalRing.RingHom.Basic

/-!
# A finite cover of a maximal localization of a fractional monogenic algebra

Assuming the local statement for maximal ideals containing the generator, a maximal localization
`R[x]_m` of a fractional monogenic algebra over a Nagata normal domain has a finite injective
domain extension with a normal principal open and analytically unramified maximal localizations.

## References

* [Stacks Project, Tag 0334], Step 5
-/

@[expose] public section

universe u v

/-- Transport analytic unramifiedness along a local ring isomorphism. -/
private theorem unramified_of_equiv {C D : Type*} [CommRing C] [CommRing D]
    [IsLocalRing C] [IsLocalRing D] [IsNoetherianRing C] [IsNoetherianRing D]
    (e : C ≃+* D) (h : IsAnalyticallyUnramified D) : IsAnalyticallyUnramified C := by
  obtain ⟨E, _⟩ := AdicCompletion.exists_ringEquiv
    (IsLocalRing.maximalIdeal C) (IsLocalRing.maximalIdeal D) e
    (IsLocalRing.map_ringEquiv_maximalIdeal e).symm
  have : IsReduced (AdicCompletion (IsLocalRing.maximalIdeal D) D) := h
  exact isReduced_of_injective E.toRingHom E.injective

/-- Let `R` be a Nagata normal domain with fraction field `K`, `x ∈ K`, and `m` a maximal ideal of
`R[x]`. Assume that `R'[y]_q` is analytically unramified whenever `R'` is a Noetherian Nagata
normal domain with fraction field `K'`, `y ∈ K'` with `R'[y]` Noetherian, and `q` is a maximal
ideal of `R'[y]` containing `y`. Then there is a Noetherian domain `B`, finite over `R[x]_m` with
injective structure map, having a nonzero `f` such that all prime localizations of `B_f` are
normal domains, and whose local rings at maximal ideals are analytically unramified. -/
theorem exists_finite_cover_adjoin_singleton_atPrime
    (R : Type u) (K : Type v) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [Field K] [Algebra R K] [IsFractionRing R K] (hR : IsNagataRing R) (x : K)
    (m : Ideal (Algebra.adjoin R ({x} : Set K))) [m.IsMaximal]
    (hLocal : ∀ (R' K' : Type (max u v)) [CommRing R'] [IsDomain R']
      [IsIntegrallyClosed R'] [IsNoetherianRing R'] [Field K'] [Algebra R' K']
      [IsFractionRing R' K'], IsNagataRing R' → ∀ (y : K')
      [IsNoetherianRing (Algebra.adjoin R' ({y} : Set K'))]
      (q : Ideal (Algebra.adjoin R' ({y} : Set K'))) [q.IsMaximal],
      (⟨y, Algebra.subset_adjoin (Set.mem_singleton y)⟩ :
        Algebra.adjoin R' ({y} : Set K')) ∈ q →
      IsAnalyticallyUnramified (Localization.AtPrime q)) :
    ∃ (B : Type (max u v)) (_ : CommRing B) (_ : IsDomain B)
      (_ : Algebra (Localization.AtPrime m) B) (_ : IsNoetherianRing B),
      Function.Injective (algebraMap (Localization.AtPrime m) B) ∧
      Module.Finite (Localization.AtPrime m) B ∧
      (∃ f : B, f ≠ 0 ∧ ∀ (p : Ideal (Localization.Away f)) [p.IsPrime],
        IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p)) ∧
      (∀ (q : Ideal B) [q.IsMaximal],
        IsAnalyticallyUnramified (Localization.AtPrime q))  := by
  obtain ⟨B, hBCR, hBDom, hBAlg, hBNoeth, hinj, hfin, hnormalB, hpresent⟩ :=
    exists_finite_cover_adjoin_singleton_core R K hR x m
  let : CommRing B := hBCR
  let : IsDomain B := hBDom
  let : Algebra (Localization.AtPrime m) B := hBAlg
  let : IsNoetherianRing B := hBNoeth
  refine ⟨B, hBCR, hBDom, hBAlg, hBNoeth, hinj, hfin, hnormalB, ?_⟩
  intro q hq
  obtain ⟨R', K', hCR, hDom, hNormal, hNoeth, hField, hAlg, hFrac,
    hNagata, y, hSNoeth, n, hn, hy, ⟨e⟩⟩ := hpresent q
  let : CommRing R' := hCR
  let : IsDomain R' := hDom
  let : IsIntegrallyClosed R' := hNormal
  let : IsNoetherianRing R' := hNoeth
  let : Field K' := hField
  let : Algebra R' K' := hAlg
  let : IsFractionRing R' K' := hFrac
  let : IsNoetherianRing (Algebra.adjoin R' ({y} : Set K')) := hSNoeth
  let : n.IsMaximal := hn
  exact unramified_of_equiv e (hLocal R' K' hNagata y n hy)

