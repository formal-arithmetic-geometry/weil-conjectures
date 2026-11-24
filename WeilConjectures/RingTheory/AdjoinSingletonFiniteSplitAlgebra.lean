/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.NagataRing
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.Algebra.Polynomial.Splits
import WeilConjectures.RingTheory.MonogenicResiduePolynomialModel
import WeilConjectures.RingTheory.MonogenicRelationFiniteSplitting

/-! # Finite split coefficient extension before maximal localization

For a Nagata normal domain `R` with fraction field `K`, `x ∈ K` and a maximal ideal `m` of
`R[x]`, we construct a finite injective map from a principal localization of `R[x]` to a monogenic
algebra over a Nagata normal domain, together with a split monic polynomial whose value at the
generator lies in the extension of `m`.

## References

* [Stacks Project, Tag 0334], Step 5
-/

@[expose] public section

universe u v

/-- Let `R` be a Nagata normal domain with fraction field `K`, `x ∈ K`, and `m` a maximal ideal of
`R[x]`. There are `s ∉ m`, a Nagata normal domain `R'` with fraction field `K'`, `z ∈ K'`, an
injective finite ring map `g : R[x]_s → R'[z]`, and a split monic polynomial `f` over `R'` of
positive degree with `f(z)` in the extension of `m` along `g`. -/
theorem exists_adjoin_singleton_finite_split_algebra
    (R : Type u) (K : Type v) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [Field K] [Algebra R K] [IsFractionRing R K] (hR : IsNagataRing R) (x : K)
    (m : Ideal (Algebra.adjoin R ({x} : Set K))) [m.IsMaximal] :
    ∃ (s : Algebra.adjoin R ({x} : Set K)), s ∉ m ∧
      ∃ (R' K' : Type (max u v)) (_ : CommRing R') (_ : IsDomain R')
        (_ : IsIntegrallyClosed R') (_ : Field K') (_ : Algebra R' K')
        (_ : IsFractionRing R' K'),
        IsNagataRing R' ∧ ∃ (z : K')
          (g : Localization.Away s →+* Algebra.adjoin R' ({z} : Set K')),
          Function.Injective g ∧ g.Finite ∧ ∃ f : Polynomial R',
            f.Monic ∧ 0 < f.natDegree ∧ f.Splits ∧
            Polynomial.aeval
              (⟨z, Algebra.subset_adjoin (Set.mem_singleton z)⟩ :
                Algebra.adjoin R' ({z} : Set K')) f ∈
              m.map (g.comp (algebraMap _ (Localization.Away s))) := by
  obtain ⟨s, hs, A, L, instCR, instD, instIC, instF, instA, instFR, hA, y, e, f,
      hf, hd, heval⟩ := exists_monogenic_residue_polynomial_model R K hR x m
  let : CommRing A := instCR
  let : IsDomain A := instD
  let : IsIntegrallyClosed A := instIC
  let : Field L := instF
  let : Algebra A L := instA
  let : IsFractionRing A L := instFR
  obtain ⟨R', K', instCR', instD', instIC', instF', instA', instFR', hR', z, g,
      hg, hgf, f', hf', hd', hs', heval'⟩ :=
    exists_monogenic_relation_finite_splitting A L hA y
      (m.map (e.toRingHom.comp (algebraMap _ (Localization.Away s)))) f hf hd heval
  refine ⟨s, hs, R', K', instCR', instD', instIC', instF', instA', instFR', hR', z,
    g.comp e.toRingHom, hg.comp e.injective, hgf.comp e.finite, f', hf', hd', hs', ?_⟩
  simpa only [Ideal.map_map, RingHom.comp_assoc] using heval'

