/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q128
-/
module

public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.Algebra.Module.LocalizedModule.Exact
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.RingTheory.Localization.Module

/-!
# Restriction of scalars length for a semilocal algebra

Source: Stacks Project, Algebra, Tag 02M0 (blueprint: lem-exc-semilocal-restriction-length).
-/

@[expose] public section

universe u v w

open scoped BigOperators
open Ideal Module Localization

private theorem residue_restriction_length
    (A : Type u) (B : Type v) [CommRing A] [CommRing B] [IsLocalRing A]
    [Algebra A B] (q : MaximalSpectrum B)
    (hcon : q.asIdeal.comap (algebraMap A B) = IsLocalRing.maximalIdeal A)
    (hfin : @Module.Finite (IsLocalRing.maximalIdeal A).ResidueField q.asIdeal.ResidueField _ _
      (Module.compHom q.asIdeal.ResidueField
        (Ideal.ResidueField.map (IsLocalRing.maximalIdeal A) q.asIdeal
          (algebraMap A B) hcon.symm))) :
    Module.length A q.asIdeal.ResidueField =
      @Module.finrank (IsLocalRing.maximalIdeal A).ResidueField q.asIdeal.ResidueField
        _ _ (Module.compHom q.asIdeal.ResidueField
          (Ideal.ResidueField.map (IsLocalRing.maximalIdeal A) q.asIdeal
            (algebraMap A B) hcon.symm)) := by
  let k := (IsLocalRing.maximalIdeal A).ResidueField
  let K := q.asIdeal.ResidueField
  let : Algebra k K :=
    (Ideal.ResidueField.map (IsLocalRing.maximalIdeal A) q.asIdeal
      (algebraMap A B) hcon.symm).toAlgebra
  have : IsScalarTower A k K := IsScalarTower.of_algebraMap_eq' (by
    ext a
    exact (Ideal.ResidueField.map_algebraMap (IsLocalRing.maximalIdeal A)
      q.asIdeal (algebraMap A B) hcon.symm a).symm)
  rw [Module.length_eq_of_surjective (R := k) (M := K)
    (Ideal.algebraMap_residueField_surjective (IsLocalRing.maximalIdeal A))]
  exact Module.length_eq_finrank k K

private theorem localized_residue_length
    (B : Type v) [CommRing B] (q p : MaximalSpectrum B) :
    Module.length (Localization.AtPrime p.asIdeal)
      (LocalizedModule p.asIdeal.primeCompl q.asIdeal.ResidueField) =
        (by classical exact if q = p then 1 else 0) := by
  classical
  by_cases h : q = p
  · subst p
    let S := q.asIdeal.primeCompl
    let K := q.asIdeal.ResidueField
    have : IsLocalizedModule S (LinearMap.id : K →ₗ[B] K) :=
      isLocalizedModule_id S K (Localization.AtPrime q.asIdeal)
    let e := (IsLocalizedModule.iso S (LinearMap.id : K →ₗ[B] K)).extendScalarsOfIsLocalization
      S (Localization.AtPrime q.asIdeal)
    rw [e.length_eq]
    simp only [↓reduceIte]
    rw [Module.length_eq_of_surjective
      (R := K) (M := K) (IsLocalRing.residue_surjective)]
    exact Module.length_eq_one K K
  · have hle : ¬ q.asIdeal ≤ p.asIdeal := by
      intro hle
      exact h (MaximalSpectrum.ext (q.isMaximal.eq_of_le p.isMaximal.ne_top hle))
    obtain ⟨a, haq, hap⟩ := SetLike.not_le_iff_exists.mp hle
    have : Subsingleton (LocalizedModule p.asIdeal.primeCompl q.asIdeal.ResidueField) := by
      rw [LocalizedModule.subsingleton_iff]
      intro x
      refine ⟨a, hap, ?_⟩
      rw [Algebra.smul_def, Ideal.algebraMap_residueField_eq_zero.mpr haq, zero_mul]
    simp [h]


/-- Restriction of scalars from a semilocal algebra has residue-degree-weighted length.

Source: Stacks Project, Algebra, Tag 02M0 (`lemma-pushdown-module`)
(blueprint: lem-exc-semilocal-restriction-length).

Proof:
1. Apply `lem-weil-pbc-finite-length-module-simple-filtration` to choose a finite strict
   filtration of `M` by `B`-submodules with simple successive quotients. For `M = 0`,
   use the empty filtration.
2. A nonzero element of each simple quotient generates it. Its annihilator is a maximal
   ideal `q`: if `b` is outside the annihilator, simplicity gives `c` with `cb` acting
   as the identity on the generator. Thus the quotient is isomorphic to `B/q`.
3. Contraction to the maximal ideal of `A` makes `B/q` a vector space over `A/𝔪`.
   A finite basis gives a flag with successive factors `A/𝔪`. The latter has length one,
   since any nonzero vector generates it as an `A`-module.
4. By `lem-weil-pbc-length-additive-short-exact`, the flag gives `A`-length equal to
   the residue degree. Restriction of scalars preserves each short exact sequence in
   the original filtration. Repeated length additivity gives finite `A`-length of `M`,
   equal to the sum of the residue degrees of its simple factors.
5. Localize a factor `B/q'` at `q`. If `q' ≠ q`, an element of `q'` outside `q`
   annihilates the factor and becomes a unit, so the localization is zero. If `q' = q`,
   sending `z/s` to `z` divided by the nonzero residue of `s` identifies its localization
   with `B/q`, which has length one over `B_q` because `B_q → B/q` is surjective.
6. By `lem-weil-pbc-localization-module-exact`, localization preserves the filtration's
   short exact sequences, including zero endpoints. Apply
   `lem-weil-pbc-length-additive-short-exact` over `B_q`: its localized length counts
   exactly the factors supported at `q`. Zero factors need no strict filtration step.
7. Regroup the finite sum of residue degrees by the maximal ideals of `B`. This gives
   the weighted localization sum. For the zero ring `B`, its unital modules are zero,
   and the empty maximal spectrum gives the same zero equality.

The canonical residue fields used here agree with the quotient fields at maximal ideals
via `Ideal.bijective_algebraMap_quotient_residueField`; their scalar action is explicitly
induced by `Ideal.ResidueField.map`, never by an independently chosen field action. -/
theorem semilocal_restriction_length
    (A : Type u) (B : Type v) [CommRing A] [CommRing B] [IsLocalRing A]
    [Algebra A B] (X : Finset (MaximalSpectrum B))
    (hX : ∀ q : MaximalSpectrum B, q ∈ X)
    (hcon : ∀ q : MaximalSpectrum B,
      q.asIdeal.comap (algebraMap A B) = IsLocalRing.maximalIdeal A)
    (hdeg : ∀ q : MaximalSpectrum B, q ∈ X →
      @Module.Finite (IsLocalRing.maximalIdeal A).ResidueField q.asIdeal.ResidueField _ _
        (Module.compHom q.asIdeal.ResidueField
          (Ideal.ResidueField.map (IsLocalRing.maximalIdeal A) q.asIdeal
            (algebraMap A B) (hcon q).symm)))
    (M : Type w) [AddCommGroup M] [Module B M]
    (hM : IsFiniteLength B M) :
    @IsFiniteLength A _ M _
        (@Module.compHom B A M _ _ (inferInstance : Module B M) _ (algebraMap A B)) ∧
      @Module.length A M _ _
        (@Module.compHom B A M _ _ (inferInstance : Module B M) _ (algebraMap A B)) =
        ∑ q ∈ X,
          @Module.finrank (IsLocalRing.maximalIdeal A).ResidueField q.asIdeal.ResidueField
            _ _ (Module.compHom q.asIdeal.ResidueField
              (Ideal.ResidueField.map (IsLocalRing.maximalIdeal A) q.asIdeal
                (algebraMap A B) (hcon q).symm)) *
            Module.length (Localization.AtPrime q.asIdeal)
              (LocalizedModule q.asIdeal.primeCompl M) := by
  classical
  induction hM with
  | @of_subsingleton M _ _ _ =>
      let : Module A M := Module.compHom M (algebraMap A B)
      exact ⟨.of_subsingleton, by simp⟩
  | @of_simple_quotient M _ _ N hsimple hN ih =>
      let : Module A M := Module.compHom M (algebraMap A B)
      have : IsScalarTower A B M := ⟨fun a b m ↦ by
        change (a • b) • m = (algebraMap A B a) • (b • m)
        rw [Algebra.smul_def, mul_smul]⟩
      obtain ⟨q, hq, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp hsimple
      let q' : MaximalSpectrum B := ⟨q, hq⟩
      let e' : (M ⧸ N) ≃ₗ[B] q'.asIdeal.ResidueField := e.trans
        ((AlgEquiv.ofBijective (Algebra.ofId (B ⧸ q) q.ResidueField)
          q.bijective_algebraMap_quotient_residueField).toLinearEquiv.restrictScalars B)
      have hres := residue_restriction_length A B q' (hcon q') (hdeg q' (hX q'))
      have hsimpleA : Module.length A (M ⧸ N) =
          @Module.finrank (IsLocalRing.maximalIdeal A).ResidueField q'.asIdeal.ResidueField
            _ _ (Module.compHom q'.asIdeal.ResidueField
              (Ideal.ResidueField.map (IsLocalRing.maximalIdeal A) q'.asIdeal
                (algebraMap A B) (hcon q').symm)) :=
        (e'.restrictScalars A).length_eq.trans hres
      have hA := Module.length_eq_add_of_exact (N.subtype.restrictScalars A)
        (N.mkQ.restrictScalars A) N.subtype_injective N.mkQ_surjective
        (LinearMap.exact_subtype_mkQ N)
      have hlocal (p : MaximalSpectrum B) :
          Module.length (Localization.AtPrime p.asIdeal)
              (LocalizedModule p.asIdeal.primeCompl M) =
            Module.length (Localization.AtPrime p.asIdeal)
              (LocalizedModule p.asIdeal.primeCompl N) +
            (if q' = p then 1 else 0) := by
        let S := p.asIdeal.primeCompl
        rw [Module.length_eq_add_of_exact (LocalizedModule.map S N.subtype)
          (LocalizedModule.map S N.mkQ)
          (LocalizedModule.map_injective S N.subtype N.subtype_injective)
          (LocalizedModule.map_surjective S N.mkQ N.mkQ_surjective)
          (LocalizedModule.map_exact S N.subtype N.mkQ (LinearMap.exact_subtype_mkQ N))]
        congr 1
        let el := IsLocalizedModule.mapEquiv S (LocalizedModule.mkLinearMap S (M ⧸ N))
          (LocalizedModule.mkLinearMap S q'.asIdeal.ResidueField)
          (Localization.AtPrime p.asIdeal) e'
        exact el.length_eq.trans (localized_residue_length B q' p)
      constructor
      · apply Module.length_ne_top_iff.mp
        rw [hA, hsimpleA]
        exact (ENat.add_lt_top.mpr
          ⟨(Module.length_ne_top_iff.mpr ih.1).lt_top, by simp⟩).ne
      · rw [hA, hsimpleA, ih.2]
        simp_rw [hlocal, mul_add, Finset.sum_add_distrib]
        congr 1
        simp [hX q']

end
