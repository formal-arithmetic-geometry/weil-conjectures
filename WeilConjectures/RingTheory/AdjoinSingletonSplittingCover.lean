/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.NagataRing
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Localization.AtPrime.Basic

import WeilConjectures.RingTheory.AdjoinSingletonSplittingPolynomialCover
import Mathlib.RingTheory.Ideal.Operations

/-! # Splitting cover before constructing the normal principal open

For a Nagata normal domain `R` with fraction field `K`, `x ∈ K` and a maximal ideal `m` of
`R[x]`, we construct a localized monogenic algebra over a Nagata normal domain, finite over
`R[x]_m`, whose maximal ideals contract to maximal ideals containing `z - r` for some coefficient
`r`.

## References

* [Stacks Project, Tag 0334], Step 5
-/

@[expose] public section

universe u v

/-- Let `R` be a Nagata normal domain with fraction field `K`, `x ∈ K`, and `m` a maximal ideal of
`R[x]`. There are a Nagata normal domain `R'` with fraction field `K'`, `z ∈ K'`, and a submonoid
`M` of non-zero-divisors of `R'[z]` such that `M⁻¹ R'[z]` is a finite `R[x]_m`-algebra with
injective structure map, and every maximal ideal of `M⁻¹ R'[z]` contracts to a maximal ideal of
`R'[z]` containing `z - r` for some `r ∈ R'`. -/
theorem exists_adjoin_singleton_splitting_cover
    (R : Type u) (K : Type v) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [Field K] [Algebra R K] [IsFractionRing R K] (hR : IsNagataRing R) (x : K)
    (m : Ideal (Algebra.adjoin R ({x} : Set K))) [m.IsMaximal] :
    ∃ (R' K' : Type (max u v)) (_ : CommRing R') (_ : IsDomain R')
      (_ : IsIntegrallyClosed R') (_ : Field K') (_ : Algebra R' K')
      (_ : IsFractionRing R' K'),
      IsNagataRing R' ∧ ∃ (z : K') (M : Submonoid (Algebra.adjoin R' ({z} : Set K'))),
        M ≤ nonZeroDivisors (Algebra.adjoin R' ({z} : Set K')) ∧
        ∃ (_ : Algebra (Localization.AtPrime m) (Localization M)),
          Function.Injective (algebraMap (Localization.AtPrime m) (Localization M)) ∧
          Module.Finite (Localization.AtPrime m) (Localization M) ∧
          ∀ (q : Ideal (Localization M)) [q.IsMaximal],
            (q.comap (algebraMap (Algebra.adjoin R' ({z} : Set K'))
              (Localization M))).IsMaximal ∧
            ∃ r : R',
              (⟨z, Algebra.subset_adjoin (Set.mem_singleton z)⟩ :
                Algebra.adjoin R' ({z} : Set K')) -
                algebraMap R' (Algebra.adjoin R' ({z} : Set K')) r ∈
                q.comap (algebraMap (Algebra.adjoin R' ({z} : Set K'))
                  (Localization M)) := by
  obtain ⟨R', K', hCR, hDom, hNorm, hField, hAlg, hFrac, hNag, z, M, hM,
      hA, hinj, hfin, d, roots, hd, hpoly⟩ :=
    exists_adjoin_singleton_splitting_polynomial_cover R K hR x m
  let : CommRing R' := hCR
  let : IsDomain R' := hDom
  let : IsIntegrallyClosed R' := hNorm
  let : Field K' := hField
  let : Algebra R' K' := hAlg
  let : IsFractionRing R' K' := hFrac
  refine ⟨R', K', hCR, hDom, hNorm, hField, hAlg, hFrac, hNag, z, M, hM, hA,
    hinj, hfin, ?_⟩
  intro q hq
  obtain ⟨hmax, hprod⟩ := hpoly q
  refine ⟨hmax, ?_⟩
  have : (q.comap (algebraMap (Algebra.adjoin R' ({z} : Set K'))
    (Localization M))).IsPrime := hmax.isPrime
  obtain ⟨i, _, hi⟩ := Ideal.IsPrime.prod_mem_iff.mp hprod
  exact ⟨roots i, hi⟩
