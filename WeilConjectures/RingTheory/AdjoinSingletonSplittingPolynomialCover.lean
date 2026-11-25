/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.NagataRing
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Localization.AtPrime.Basic
import WeilConjectures.RingTheory.AdjoinSingletonFiniteSplitAlgebra
import WeilConjectures.RingTheory.FiniteAwayMaximalLocalization
import Mathlib.Algebra.BigOperators.Fin

/-! # Split polynomial data for a finite localized cover

For a Nagata normal domain `R` with fraction field `K`, `x ∈ K` and a maximal ideal `m` of
`R[x]`, we construct a localized monogenic algebra `M⁻¹ R'[z]`, finite over `R[x]_m`, together
with finitely many roots `rᵢ ∈ R'` such that `∏ (z - rᵢ)` lies in every maximal contraction.

## References

* [Stacks Project, Tag 0334], Step 5
-/

@[expose] public section

universe u v

private theorem exists_fin_roots_prod_aeval
    (R T : Type*) [CommRing R] [IsDomain R] [CommRing T] [Algebra R T]
    (f : Polynomial R) (hf : f.Monic) (hd : 0 < f.natDegree) (hsplit : f.Splits) :
    ∃ (d : ℕ) (roots : Fin d → R), 0 < d ∧
      ∀ t : T, (∏ i, (t - algebraMap R T (roots i))) = Polynomial.aeval t f := by
  classical
  let l := f.roots.toList
  refine ⟨l.length, l.get, ?_, ?_⟩
  · have hlen : l.length = f.natDegree := by
      simpa [l] using hsplit.natDegree_eq_card_roots.symm
    exact hlen.symm ▸ hd
  intro t
  conv_rhs => rw [hsplit.eq_prod_roots_of_monic hf]
  simp only [map_multiset_prod, Multiset.map_map, Function.comp_def, map_sub,
    Polynomial.aeval_X, Polynomial.aeval_C]
  rw [← List.prod_ofFn]
  have he : List.ofFn (fun i ↦ t - algebraMap R T (l.get i)) =
      l.map (fun a ↦ t - algebraMap R T a) := by
    simpa only [Function.comp_def, List.ofFn_get] using
      (List.map_ofFn (f := l.get) (g := fun a ↦ t - algebraMap R T a)).symm
  rw [he]
  simp [l]

private theorem splitting_polynomial_cover_of_finite_away
    (R S T : Type*) [CommRing R] [IsDomain R] [CommRing S] [IsDomain S]
    [CommRing T] [IsDomain T] [Algebra R T]
    (m : Ideal S) [m.IsMaximal] (s : S) (hs : s ∉ m)
    (g : Localization.Away s →+* T) (hg : Function.Injective g) (hfin : g.Finite)
    (t : T) (f : Polynomial R) (hf : f.Monic) (hd : 0 < f.natDegree) (hsplit : f.Splits)
    (hmem : Polynomial.aeval t f ∈ m.map (g.comp (algebraMap S (Localization.Away s)))) :
    ∃ M : Submonoid T, M ≤ nonZeroDivisors T ∧
      ∃ (_ : Algebra (Localization.AtPrime m) (Localization M)),
        Function.Injective (algebraMap (Localization.AtPrime m) (Localization M)) ∧
        Module.Finite (Localization.AtPrime m) (Localization M) ∧
        ∃ (d : ℕ) (roots : Fin d → R), 0 < d ∧
          ∀ (q : Ideal (Localization M)) [q.IsMaximal],
            (q.comap (algebraMap T (Localization M))).IsMaximal ∧
            (∏ i, (t - algebraMap R T (roots i))) ∈
              q.comap (algebraMap T (Localization M)) := by
  classical
  let h : S →+* T := g.comp (algebraMap S (Localization.Away s))
  let M := m.primeCompl.map h
  have hs0 : s ≠ 0 := fun e ↦ hs (e ▸ m.zero_mem)
  have hinj : Function.Injective h := hg.comp
    (IsLocalization.injective (Localization.Away s) (Submonoid.powers_le.mpr
      (mem_nonZeroDivisors_iff_ne_zero.mpr hs0)))
  have hM : M ≤ nonZeroDivisors T := by
    rintro t ⟨a, ha, rfl⟩
    apply mem_nonZeroDivisors_iff_ne_zero.mpr
    intro he
    have ha0 : a = 0 := hinj (he.trans h.map_zero.symm)
    exact ha (ha0 ▸ m.zero_mem)
  obtain ⟨alg, hi, hfinite, hq⟩ :=
    exists_finite_away_maximal_localization S T m s hs g hg hfin
  let := alg
  obtain ⟨d, roots, hd, heval⟩ := exists_fin_roots_prod_aeval R T f hf hd hsplit
  refine ⟨M, hM, alg, hi, hfinite, d, roots, hd, ?_⟩
  intro q hqmax
  refine ⟨(hq q).1, ?_⟩
  rw [heval]
  exact (hq q).2 hmem

/-- Let `R` be a Nagata normal domain with fraction field `K`, `x ∈ K`, and `m` a maximal ideal of
`R[x]`. There are a Nagata normal domain `R'` with fraction field `K'`, `z ∈ K'`, a submonoid `M`
of non-zero-divisors of `R'[z]` such that `M⁻¹ R'[z]` is a finite `R[x]_m`-algebra with injective
structure map, and elements `r₁, …, r_d ∈ R'` with `d > 0`, such that every maximal ideal of
`M⁻¹ R'[z]` contracts to a maximal ideal of `R'[z]` containing `∏ i, (z - rᵢ)`. -/
theorem exists_adjoin_singleton_splitting_polynomial_cover
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
          ∃ (d : ℕ) (roots : Fin d → R'), 0 < d ∧
            ∀ (q : Ideal (Localization M)) [q.IsMaximal],
              (q.comap (algebraMap (Algebra.adjoin R' ({z} : Set K'))
                (Localization M))).IsMaximal ∧
              (∏ i : Fin d,
                ((⟨z, Algebra.subset_adjoin (Set.mem_singleton z)⟩ :
                  Algebra.adjoin R' ({z} : Set K')) -
                  algebraMap R' (Algebra.adjoin R' ({z} : Set K')) (roots i))) ∈
                q.comap (algebraMap (Algebra.adjoin R' ({z} : Set K'))
                  (Localization M)) := by
  classical
  obtain ⟨s, hs, R', K', cR, dR, nR, cK, aK, frac, hR', z, g, hg, hfin, f, hf, hd, hsplit,
    hmem⟩ := exists_adjoin_singleton_finite_split_algebra R K hR x m
  refine ⟨R', K', cR, dR, nR, cK, aK, frac, hR', z, ?_⟩
  exact splitting_polynomial_cover_of_finite_away R'
    (Algebra.adjoin R ({x} : Set K)) (Algebra.adjoin R' ({z} : Set K'))
    m s hs g hg hfin ⟨z, Algebra.subset_adjoin (Set.mem_singleton z)⟩ f hf hd hsplit hmem
