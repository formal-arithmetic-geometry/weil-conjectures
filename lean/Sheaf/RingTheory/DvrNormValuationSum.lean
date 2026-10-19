/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q116
-/
module

public import Mathlib.RingTheory.OrderOfVanishing.Noetherian
public import Mathlib.RingTheory.Localization.LocalizationLocalization
public import Mathlib.RingTheory.Spectrum.Maximal.Defs
public import Mathlib.RingTheory.Ideal.Over
public import Mathlib.RingTheory.Norm.Defs

import Sheaf.RingTheory.DvrLatticeDistanceDeterminant
import Sheaf.RingTheory.SemilocalRestrictionLength
import Mathlib.Algebra.Module.LocalizedModule.Submodule
import Mathlib.Data.ENat.BigOperators
import Mathlib.RingTheory.Localization.Integral

/-!
# Valuation of a field norm over a finite semilocal DVR algebra

Source: Stacks Project, Algebra, Tag 02MJ (`lemma-finite-extension-dim-1`), specialized
to discrete valuation rings (blueprint: lem-exc-dvr-norm-valuation-sum).

The normalized integer valuation is `WithZero.log (Ring.ordFrac R x)`: the order of a
uniformizer is `WithZero.exp 1` by `Ring.ordFrac_irreducible`, so its integer value is `1`.
The field norm is `Algebra.norm`, the determinant of multiplication by the element.
-/

@[expose] public section

universe u v w z

private theorem residue_degree_comparison
    (A : Type u) [CommRing A] [IsLocalRing A]
    (B : Type v) [CommRing B] [Algebra A B]
    (q : MaximalSpectrum B)
    (hq : q.asIdeal.under A = IsLocalRing.maximalIdeal A)
    [Module.Finite (A ⧸ q.asIdeal.under A) (B ⧸ q.asIdeal)] :
    let f := Ideal.ResidueField.map (IsLocalRing.maximalIdeal A) q.asIdeal
      (algebraMap A B) hq.symm
    let := f.toAlgebra
    Module.Finite (IsLocalRing.maximalIdeal A).ResidueField q.asIdeal.ResidueField ∧
      Module.finrank (IsLocalRing.maximalIdeal A).ResidueField q.asIdeal.ResidueField =
        Module.finrank (A ⧸ q.asIdeal.under A) (B ⧸ q.asIdeal) := by
  let f := Ideal.ResidueField.map (IsLocalRing.maximalIdeal A) q.asIdeal
    (algebraMap A B) hq.symm
  let := f.toAlgebra
  let i : (A ⧸ q.asIdeal.under A) ≃+* (IsLocalRing.maximalIdeal A).ResidueField :=
    (Ideal.quotEquivOfEq hq).trans
      (RingEquiv.ofBijective (algebraMap (A ⧸ IsLocalRing.maximalIdeal A)
        (IsLocalRing.maximalIdeal A).ResidueField)
        (Ideal.bijective_algebraMap_quotient_residueField _))
  let j : (B ⧸ q.asIdeal) ≃+* q.asIdeal.ResidueField :=
    RingEquiv.ofBijective (algebraMap (B ⧸ q.asIdeal) q.asIdeal.ResidueField)
      (Ideal.bijective_algebraMap_quotient_residueField _)
  have hc : (algebraMap (IsLocalRing.maximalIdeal A).ResidueField
      q.asIdeal.ResidueField).comp i.toRingHom =
      j.toRingHom.comp (algebraMap (A ⧸ q.asIdeal.under A) (B ⧸ q.asIdeal)) := by
    ext x
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
      i, j, RingEquiv.trans_apply, RingEquiv.ofBijective_apply, Ideal.quotEquivOfEq_mk,
      Ideal.algebraMap_quotient_residueField_mk]
    change f (algebraMap A _ x) = algebraMap B _ (algebraMap A B x)
    exact Ideal.ResidueField.map_algebraMap _ _ _ _ x
  let e : (B ⧸ q.asIdeal) →ₛₗ[i.toRingHom] q.asIdeal.ResidueField :=
    { j.toAddEquiv.toAddMonoidHom with
      map_smul' := by
        intro a b
        simp only [Algebra.smul_def]
        change j ((algebraMap (A ⧸ q.asIdeal.under A) (B ⧸ q.asIdeal)) a * b) = _
        rw [map_mul]
        rw [show j (algebraMap (A ⧸ q.asIdeal.under A) (B ⧸ q.asIdeal) a) =
          algebraMap _ _ (i a) from (RingHom.congr_fun hc a).symm]
        rfl }
  exact ⟨Module.Finite.of_surjective e j.surjective,
    (Algebra.finrank_eq_of_equiv_equiv i j hc).symm⟩

private theorem log_ordFrac_algebraMap
    (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R] [Ring.KrullDimLE 1 R]
    (F : Type v) [Field F] [Algebra R F] [IsFractionRing R F]
    (r : R) (hr : r ≠ 0) :
    WithZero.log (Ring.ordFrac R (algebraMap R F r)) = ((Ring.ord R r).toNat : ℤ) := by
  rw [Ring.ordFrac_eq_ord R hr, Ring.ordMonoidWithZeroHom_eq_coe R
    (mem_nonZeroDivisors_iff_ne_zero.mpr hr)
    (ENat.natCast_toNat (Ring.ord_ne_top (mem_nonZeroDivisors_iff_ne_zero.mpr hr))).symm]
  rfl

private theorem localized_principal_length
    (B : Type u) [CommRing B] (q : MaximalSpectrum B) (b : B) :
    Module.length (Localization.AtPrime q.asIdeal)
      (LocalizedModule q.asIdeal.primeCompl (B ⧸ Ideal.span {b})) =
      Ring.ord (Localization.AtPrime q.asIdeal)
        (algebraMap B (Localization.AtPrime q.asIdeal) b) := by
  let R := Localization.AtPrime q.asIdeal
  let S := q.asIdeal.primeCompl
  let I : Submodule B B := Ideal.span {b}
  let f := Algebra.linearMap B R
  have heq : I.localized' R S f = Ideal.span {algebraMap B R b} := by
    change (Submodule.span B {b}).localized' R S f = _
    rw [Submodule.localized'_span]
    simp only [Set.image_singleton]
    rfl
  let e := (IsLocalizedModule.linearEquiv S
    (LocalizedModule.mkLinearMap S (B ⧸ I)) (I.toLocalizedQuotient' R S f)
    ).extendScalarsOfIsLocalization S R
  rw [e.length_eq]
  change Module.length R (R ⧸ I.localized' R S f) = _
  rw [heq]
  rfl

namespace IsDiscreteValuationRing

/-- The valuation of the norm is the sum of the local valuations weighted by residue degrees.
Source: Stacks Project, Algebra, Tag 02MJ (blueprint: lem-exc-dvr-norm-valuation-sum).

Here `A / q.under A` is the residue field of `A` by `hcontract`; its canonical algebra
structure on `B / q` is induced by the given inclusion. The fraction field of each localization
is canonically `FractionRing B`; `IsLocalization.algEquiv` transports `y` from the given `L`.

Proof (Stacks Tag 02MJ): first take a nonzero `b : B`. The image `M` of `B` in
`L` is finite over `A` and spans `L` over `K`; the latter follows by clearing
algebraic denominators. Multiplication by `b` sends `M` into itself, so the
lattice determinant formula identifies the order of its determinant, namely
`Algebra.norm K b`, with the finite length of `B / bB`.

This quotient has finite length over `B` as well. The semilocal restriction
formula expresses its `A`-length as the residue-degree-weighted sum of its
localized lengths. Canonical quotient-to-residue-field isomorphisms identify
the residue degrees in the two formulations. Localization of a principal
quotient is the quotient by the localized generator, whose length is the
order of that generator. `Ring.ordFrac_eq_ord` identifies this order with the
integer valuation, proving the formula for `b`.

Finally write `y = a / b` with both numerator and denominator nonzero. The norm
is multiplicative and all the orders are additive on nonzero products.
Subtract the identities for `a` and `b` to obtain the formula for `y`.
-/
theorem norm_valuation_sum
    (A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (K : Type v) [Field K] [Algebra A K] [IsFractionRing A K]
    (B : Type w) [CommRing B] [IsDomain B] [Algebra A B] [Module.Finite A B]
    (L : Type z) [Field L] [Algebra B L] [IsFractionRing B L]
    [Algebra K L] [FiniteDimensional K L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L]
    [Fintype (MaximalSpectrum B)]
    (hcontract : ∀ q : MaximalSpectrum B,
      q.asIdeal.under A = IsLocalRing.maximalIdeal A)
    [∀ q : MaximalSpectrum B, IsDiscreteValuationRing (Localization.AtPrime q.asIdeal)]
    [∀ q : MaximalSpectrum B, Module.Finite (A ⧸ q.asIdeal.under A) (B ⧸ q.asIdeal)]
    (y : Lˣ) :
    WithZero.log (Ring.ordFrac A (Algebra.norm K (y : L))) =
      ∑ q : MaximalSpectrum B,
        (Module.finrank (A ⧸ q.asIdeal.under A) (B ⧸ q.asIdeal) : ℤ) *
          WithZero.log (Ring.ordFrac (Localization.AtPrime q.asIdeal)
            (IsLocalization.algEquiv (nonZeroDivisors B) L (FractionRing B) (y : L))) := by
  classical
  let M := LinearMap.range (IsScalarTower.toAlgHom A B L).toLinearMap
  let e : B ≃ₗ[A] M := LinearEquiv.ofInjective
    (IsScalarTower.toAlgHom A B L).toLinearMap (IsFractionRing.injective B L)
  have : Module.Finite A M := Module.Finite.of_surjective e.toLinearMap e.surjective
  have hspan : Submodule.span K (M : Set L) = ⊤ := by
    change Submodule.span K (Set.range (algebraMap B L)) = ⊤
    apply top_unique
    intro x hx
    have hinj : Function.Injective (algebraMap A L) := by
      rw [IsScalarTower.algebraMap_eq A K L]
      exact (algebraMap K L).injective.comp (IsFractionRing.injective A K)
    have h := IsFractionRing.ideal_span_singleton_map_subset
      (R := A) (S := B) (K := K) (L := L) (a := 1) (b := Set.univ) hinj
      (by intro b hb; simp)
    simpa using h (by simp : x ∈ (Ideal.span ({algebraMap B L 1} : Set L) : Set L))
  have hn (b : B) (hb : b ≠ 0) :
      Module.length A (B ⧸ Ideal.span {b}) ≠ ⊤ ∧
        WithZero.log (Ring.ordFrac A (Algebra.norm K (algebraMap B L b))) =
          ((Module.length A (B ⧸ Ideal.span {b})).toNat : ℤ) := by
    let g := (Units.mk0 (algebraMap B L b)
      (by simpa using (IsFractionRing.injective B L).ne hb)).mulLeftLinearEquiv K L
    let N := M.map (g.toLinearMap.restrictScalars A)
    have hNM : N ≤ M := by
      rintro x ⟨z, hz, rfl⟩
      obtain ⟨c, rfl⟩ := hz
      exact ⟨b * c, by simp [g]⟩
    have hminus : M.comap N.subtype = ⊤ := by
      exact top_unique (fun x _ ↦ hNM x.property)
    have hmap : ((Ideal.span {b} : Submodule B B).restrictScalars A).map
        e.toLinearMap = N.comap M.subtype := by
      ext x
      constructor
      · rintro ⟨c, hc, rfl⟩
        obtain ⟨d, rfl⟩ := Ideal.mem_span_singleton.mp hc
        refine ⟨algebraMap B L d, ⟨d, rfl⟩, ?_⟩
        change algebraMap B L b * algebraMap B L d = algebraMap B L (b * d)
        exact (map_mul _ _ _).symm
      · rintro ⟨z, hz, he⟩
        obtain ⟨c, rfl⟩ := hz
        refine ⟨b * c, Ideal.mem_span_singleton.mpr (dvd_mul_right b c), ?_⟩
        apply Subtype.ext
        change algebraMap B L (b * c) = x.val
        simpa [g] using he
    let eqv := (Submodule.Quotient.restrictScalarsEquiv A (Ideal.span {b})).symm.trans
      (Submodule.Quotient.equiv _ _ e hmap)
    obtain ⟨hp, hm, hd⟩ := lattice_distance_determinant A K L M hspan g
    change Module.length A (M ⧸ N.comap M.subtype) ≠ ⊤ at hp
    have hlen := eqv.length_eq
    have hz : Module.length A (N ⧸ M.comap N.subtype) = 0 := by
      rw [hminus]
      exact Module.length_eq_zero
    change _ - ((Module.length A (N ⧸ M.comap N.subtype)).toNat : ℤ) = _ at hd
    rw [hz, ENat.toNat_zero, Int.natCast_zero, sub_zero, ← hlen] at hd
    exact ⟨by rwa [← hlen] at hp, hd.symm⟩
  have hs (b : B) (hb : b ≠ 0) :
      WithZero.log (Ring.ordFrac A (Algebra.norm K (algebraMap B L b))) =
        ∑ q : MaximalSpectrum B,
          (Module.finrank (A ⧸ q.asIdeal.under A) (B ⧸ q.asIdeal) : ℤ) *
            WithZero.log (Ring.ordFrac (Localization.AtPrime q.asIdeal)
              (algebraMap B (FractionRing B) b)) := by
    obtain ⟨hfin, hnorm⟩ := hn b hb
    obtain ⟨hnoeth, hart⟩ := isFiniteLength_iff_isNoetherian_isArtinian.mp
      (Module.length_ne_top_iff.mp hfin)
    have hB : IsFiniteLength B (B ⧸ Ideal.span {b}) :=
      isFiniteLength_iff_isNoetherian_isArtinian.mpr
        ⟨isNoetherian_of_tower A hnoeth, isArtinian_of_tower A hart⟩
    have hd := fun q ↦ residue_degree_comparison A B q (hcontract q)
    have hl := (semilocal_restriction_length A B Finset.univ (by simp)
      hcontract (fun q _ ↦ (hd q).1) (B ⧸ Ideal.span {b}) hB).2
    have hscalar : Module.compHom (B ⧸ Ideal.span {b}) (algebraMap A B) =
        (inferInstance : Module A (B ⧸ Ideal.span {b})) :=
      Module.ext' _ _ (fun a m ↦ IsScalarTower.algebraMap_smul B a m)
    rw [hscalar] at hl
    rw [hnorm, hl]
    rw [ENat.toNat_sum (ENat.sum_ne_top.mp (hl ▸ hfin)), Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro q hq
    rw [ENat.toNat_mul, Nat.cast_mul, ENat.toNat_natCast, (hd q).2,
      localized_principal_length]
    congr 1
    rw [IsScalarTower.algebraMap_apply B (Localization.AtPrime q.asIdeal) (FractionRing B)]
    exact (log_ordFrac_algebraMap _ _ _
      (by simpa only [map_zero] using
        (IsLocalization.injective (Localization.AtPrime q.asIdeal)
          q.asIdeal.primeCompl_le_nonZeroDivisors).ne hb)).symm
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective B (y : L)
  have hb' : b ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hb
  have hbL : algebraMap B L b ≠ 0 := by
    simpa only [map_zero] using (IsFractionRing.injective B L).ne hb'
  have ha : a ≠ 0 := by
    intro h
    simp only [h, map_zero, zero_div] at hab
    exact y.ne_zero hab.symm
  have hab' : (y : L) * algebraMap B L b = algebraMap B L a :=
    (eq_div_iff hbL).mp hab.symm
  have hnorm (x : L) (hx : x ≠ 0) : Algebra.norm K x ≠ 0 :=
    ((Units.mk0 x hx).isUnit.map (Algebra.norm K)).ne_zero
  have hg :
      WithZero.log (Ring.ordFrac A (Algebra.norm K (y : L))) +
        WithZero.log (Ring.ordFrac A (Algebra.norm K (algebraMap B L b))) =
      WithZero.log (Ring.ordFrac A (Algebra.norm K (algebraMap B L a))) := by
    rw [← WithZero.log_mul ((map_ne_zero _).mpr (hnorm _ y.ne_zero))
      ((map_ne_zero _).mpr (hnorm _ hbL)), ← map_mul, ← map_mul, hab']
  have hlocal (q : MaximalSpectrum B) :
      WithZero.log (Ring.ordFrac (Localization.AtPrime q.asIdeal)
        (IsLocalization.algEquiv (nonZeroDivisors B) L (FractionRing B) (y : L))) +
        WithZero.log (Ring.ordFrac (Localization.AtPrime q.asIdeal)
          (algebraMap B (FractionRing B) b)) =
      WithZero.log (Ring.ordFrac (Localization.AtPrime q.asIdeal)
        (algebraMap B (FractionRing B) a)) := by
    let e := IsLocalization.algEquiv (nonZeroDivisors B) L (FractionRing B)
    have hyF : e (y : L) ≠ 0 := by
      simpa only [map_zero] using e.injective.ne y.ne_zero
    have hbF : algebraMap B (FractionRing B) b ≠ 0 :=
      by simpa only [map_zero] using (IsFractionRing.injective B (FractionRing B)).ne hb'
    rw [← WithZero.log_mul ((map_ne_zero _).mpr hyF) ((map_ne_zero _).mpr hbF),
      ← map_mul]
    change WithZero.log (Ring.ordFrac (Localization.AtPrime q.asIdeal)
      (e (y : L) * algebraMap B (FractionRing B) b)) = _
    rw [← e.commutes b, ← map_mul, hab', e.commutes a]
  calc
    _ = WithZero.log (Ring.ordFrac A (Algebra.norm K (algebraMap B L a))) -
        WithZero.log (Ring.ordFrac A (Algebra.norm K (algebraMap B L b))) := by omega
    _ = _ := by
      rw [hs a ha, hs b hb', ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro q hq
      rw [← mul_sub]
      congr 1
      have := hlocal q
      omega

end IsDiscreteValuationRing
