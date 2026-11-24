/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.Algebra.Algebra.Subalgebra.Lattice

import WeilConjectures.RingTheory.DvrUnitRootLocalSquare
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

/-! # A local unit-root cover of a DVR diagram

Given a local map `A ⟶ T` of discrete valuation rings and a unit `v` of `A`, an `e`-th root of
`v` (with `e` invertible in `A`) is adjoined compatibly above `A` and `T`
(`RingTheory.dvr_etale_unit_root_diagram`).

## Implementation details

The extensions are local factors of `C = A[X]/(X^e - v)`, finite étale over `A`, and of
`T ⊗_A C`. No ramification or residue-separability assumption on `T/A` is used.

## References

* Stacks Project, Tag 0BRM, the first claim in its proof.
-/

@[expose] public section

universe u
namespace RingTheory

/-- Adjoining a root of a unit simultaneously above the two DVRs of a local diagram. Let
`A ⟶ T` be a local map of discrete valuation rings, `F = Frac T`, `e ≥ 1` a unit in `A` and `v` a
unit of `A`. Then there are local extensions of discrete valuation rings `A ⟶ A'` (with separable
residue extension) and `T ⟶ T'`, a local map `A' ⟶ T'` making the square commute, an element
`r ∈ A'` with `r^e = v`, and a field map `F ⟶ F' = Frac T'` compatible with all the maps, such that
`F'` is generated as an `A'`-algebra by the image of `F`. -/

theorem dvr_etale_unit_root_diagram
    (A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (e : ℕ) (hepos : 0 < e) (he : IsUnit (e : A)) (v : Aˣ)
    (T : Type u) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T]
    [Algebra A T] [IsLocalHom (algebraMap A T)]
    (F : Type u) [Field F] [Algebra A F] [Algebra T F]
    [IsFractionRing T F] [IsScalarTower A T F] :
    ∃ (A' : Type u) (_ : CommRing A') (_ : IsDomain A')
      (_ : IsDiscreteValuationRing A') (aAA' : Algebra A A'),
    letI := aAA'
    ∃ (hAA' : IsLocalHom (algebraMap A A')) (r : A'),
    letI := hAA'
    r ^ e = algebraMap A A' (v : A) ∧
    Algebra.IsSeparable (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField A') ∧
    ∃ (T' : Type u) (_ : CommRing T') (_ : IsDomain T')
      (_ : IsDiscreteValuationRing T') (aTT' : Algebra T T') (aA'T' : Algebra A' T'),
    letI := aTT'
    letI := aA'T'
    ∃ (_ : IsLocalHom (algebraMap T T')) (_ : IsLocalHom (algebraMap A' T')),
    (∀ a : A, algebraMap T T' (algebraMap A T a) =
      algebraMap A' T' (algebraMap A A' a)) ∧
    ∃ (F' : Type u) (_ : Field F') (aA'F' : Algebra A' F') (aT'F' : Algebra T' F'),
    letI := aA'F'
    letI := aT'F'
    ∃ (_ : IsFractionRing T' F') (_ : IsScalarTower A' T' F') (iF : F →+* F'),
    (∀ a : A, iF (algebraMap A F a) = algebraMap A' F' (algebraMap A A' a)) ∧
    (∀ t : T, iF (algebraMap T F t) = algebraMap T' F' (algebraMap T T' t)) ∧
    Algebra.adjoin A' (Set.range iF) = ⊤ := by
  classical
  obtain ⟨A', hcommA', hdomA', hdvrA', aAA', hAA', r, hr, hsep,
    T', hcommT', hdomT', hdvrT', aTT', aA'T', hTT', hA'T', hsquare, hinj, hrepr⟩ :=
    dvr_unit_root_local_square A e hepos he v T
  let := hcommA'
  let := hdomA'
  let := hdvrA'
  let := aAA'
  let := hAA'
  let := hcommT'
  let := hdomT'
  let := hdvrT'
  let := aTT'
  let := aA'T'
  let := hTT'
  let := hA'T'
  refine ⟨A', hcommA', hdomA', hdvrA', aAA', hAA', r, hr, hsep,
    T', hcommT', hdomT', hdvrT', aTT', aA'T', hTT', hA'T', hsquare, ?_⟩
  let K := FractionRing T'
  let : Algebra A' K := inferInstance
  have : IsScalarTower A' T' K := inferInstance
  let g : T →+* K := (algebraMap T' K).comp (algebraMap T T')
  have hg : Function.Injective g := (IsFractionRing.injective T' K).comp hinj
  let iF : F →+* K := IsFractionRing.lift hg
  have hiF (t : T) : iF (algebraMap T F t) =
      algebraMap T' K (algebraMap T T' t) := IsFractionRing.lift_algebraMap hg t
  have hiA (a : A) : iF (algebraMap A F a) =
      algebraMap A' K (algebraMap A A' a) := by
    rw [IsScalarTower.algebraMap_apply A T F, hiF, hsquare,
      ← IsScalarTower.algebraMap_apply A' T' K]
  refine ⟨K, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, iF, hiA, hiF, ?_⟩
  let : Algebra F K := iF.toAlgebra
  let s : K := algebraMap A' K r
  let S : Subalgebra F K := Algebra.adjoin F {s}
  have hs : s ∈ S := Algebra.subset_adjoin (Set.mem_singleton s)
  have hsint : IsIntegral F s := by
    apply IsIntegral.of_pow hepos
    have hpow : s ^ e = algebraMap F K (algebraMap A F (v : A)) := by
      change (algebraMap A' K r) ^ e = iF (algebraMap A F (v : A))
      rw [← map_pow, hr, hiA]
    rw [hpow]
    exact isIntegral_algebraMap
  have : Algebra.IsIntegral F S := Algebra.IsIntegral.adjoin (by
    intro x hx
    obtain rfl := Set.mem_singleton_iff.mp hx
    exact hsint)
  have hpoly (p : Polynomial T) :
      algebraMap T' K (p.eval₂ (algebraMap T T') (algebraMap A' T' r)) ∈ S := by
    induction p using Polynomial.induction_on' with
    | add p q hp hq =>
      simpa only [Polynomial.eval₂_add, map_add] using S.add_mem hp hq
    | monomial n t =>
      simp only [Polynomial.eval₂_monomial, map_mul, map_pow]
      apply S.mul_mem
      · rw [← hiF]
        exact S.algebraMap_mem (algebraMap T F t)
      · exact S.pow_mem (by
          simpa only [← IsScalarTower.algebraMap_apply A' T' K] using hs) n
  have hT' (x : T') : algebraMap T' K x ∈ S := by
    obtain ⟨p, q, hq, hx⟩ := hrepr x
    have hqK : algebraMap T' K
        (q.eval₂ (algebraMap T T') (algebraMap A' T' r)) ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective T' K)).mpr hq
    have hxK := congrArg (algebraMap T' K) hx
    rw [map_mul] at hxK
    rw [(eq_div_iff hqK).mpr hxK]
    simpa only [div_eq_mul_inv] using
      S.mul_mem (hpoly p) (Algebra.IsIntegral.inv_mem (hpoly q))
  have hS : S = ⊤ := by
    apply top_unique
    intro x _
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective T' x
    simpa only [div_eq_mul_inv] using
      S.mul_mem (hT' a) (Algebra.IsIntegral.inv_mem (hT' b))
  let B : Subalgebra A' K := Algebra.adjoin A' (Set.range iF)
  have hSB (x : K) (hx : x ∈ S) : x ∈ B := by
    induction hx using Algebra.adjoin_induction with
    | mem x hx =>
      obtain rfl := Set.mem_singleton_iff.mp hx
      exact B.algebraMap_mem r
    | algebraMap f => exact Algebra.subset_adjoin ⟨f, rfl⟩
    | add x y hx hy hix hiy => exact B.add_mem hix hiy
    | mul x y hx hy hix hiy => exact B.mul_mem hix hiy
  apply top_unique
  intro x _
  apply hSB x
  rw [hS]
  trivial

end RingTheory
