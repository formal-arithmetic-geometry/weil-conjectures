/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NJ
-/
module

public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.Ideal.Over
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
import Mathlib.RingTheory.QuasiFinite.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Finite intermediate models of integral algebras at a finite prime fibre

Source: Stacks Project, More on Morphisms, Tag 0BSR,
`lemma-etale-makes-integral-split`, first proof, finite intermediate algebra;
fraction-numerator/denominator variant
(blueprint: lem-dl-a1-integral-finite-residue-model).
-/

@[expose] public section

universe u v

namespace Algebra

private theorem residue_fraction {D : Type v} [CommRing D]
    (r : Ideal D) [r.IsPrime] (x : r.ResidueField) :
    ∃ a b : D, algebraMap D r.ResidueField a / algebraMap D r.ResidueField b = x := by
  obtain ⟨a, b, -, h⟩ := IsFractionRing.div_surjective (D ⧸ r) x
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
  exact ⟨a, b, h⟩

private theorem residue_finite {A : Type u} {C : Type v}
    [CommRing A] [CommRing C] [Algebra A C] [Module.Finite A C]
    (p : Ideal A) [p.IsPrime] (q : Ideal C) [q.IsPrime] [q.LiesOver p] :
    let := (Ideal.ResidueField.map p q (algebraMap A C) (q.over_def p)).toAlgebra
    Module.Finite p.ResidueField q.ResidueField := by
  let := Localization.AtPrime.algebraOfLiesOver p q
  let h := Algebra.QuasiFinite.instFiniteResidueField p q
  have he : IsLocalRing.ResidueField.instModule =
      (Ideal.ResidueField.map p q (algebraMap A C) (q.over_def p)).toAlgebra.toModule := by
    apply Module.ext'
    intro x y
    obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective x
    obtain ⟨y, rfl⟩ := IsLocalRing.residue_surjective y
    rfl
  change @Module.Finite p.ResidueField q.ResidueField _ _
    (Ideal.ResidueField.map p q (algebraMap A C) (q.over_def p)).toAlgebra.toModule
  rw [← he]
  exact h

set_option maxHeartbeats 800000 in
-- Comparing the explicit residue-field scalar structures needs extra elaboration heartbeats.
set_option backward.isDefEq.respectTransparency false in
/-- A finite intermediate algebra preserves the prime fibre and captures the prescribed
finite separable residue subfields. The residue fields are fraction fields of prime
quotients. Their embeddings are `Ideal.ResidueField.map`; the intermediate fields in the
conclusion are exactly the images of these embeddings, not independently chosen fields.

Source: Stacks Project, More on Morphisms, Tag 0BSR, first proof, finite intermediate algebra
(blueprint: lem-dl-a1-integral-finite-residue-model).

Proof plan:
1. Integral incomparability (`lem-weil-pbc-integral-incomparability`) gives, for each pair
   of distinct primes over p, an element in one prime but outside the other.
2. Choose a finite spanning family of each F over k
   (`def-weil-finite-dimensional-subspace`). Write each element as a quotient in D/r,
   and lift its numerator and its nonzero denominator to D.
3. Adjoin all these lifts and the pairwise separators to A. This is a finite set, and its
   elements are integral. By `lem-sc-finite-generated-integral-subring` its generated
   subalgebra C is module-finite. For the empty fibre use the empty generating set.
4. Every monic relation over A is a monic relation over C, so D is integral over C.
   The separators make the contractions of the original fibre primes pairwise distinct.
5. Integral injective lying over (`lem-weil-pbc-integral-injective-lying-over`) lifts every
   prime of C over p to a prime of D over p. Thus contraction is bijective, also when the
   original fibre is empty.
6. Inside E, take the k-span of the images of finite A-module generators of C. This span
   contains 1 and is closed under products, hence is a finite-dimensional domain algebra.
   By `lem-weil-pbc-finite-dimensional-domain-is-field` it is a field. It therefore equals
   the image L of the fraction field of C/(r ∩ C), proving finite-dimensionality of L/k.
7. The chosen numerator and denominator lifts put every spanning element of F in L,
   so F is contained in L. Every p-power witnessing pure inseparability over F also lies
   in L (`def-weil-pbc-finite-purely-inseparable-extension`). In characteristic zero,
   E = F forces L = E. Empty-fibre residue conclusions have no indices. -/
theorem exists_integral_finite_residue_model
    {A : Type u} {D : Type v} [CommRing A] [CommRing D] [Algebra A D]
    [Algebra.IsIntegral A D] (p : Ideal A) [p.IsPrime]
    (hfibre : (p.primesOver D).Finite)
    (F : ∀ r : p.primesOver D,
      @IntermediateField p.ResidueField r.1.ResidueField _ _
        (Ideal.ResidueField.map p r.1 (algebraMap A D) (r.1.over_def p)).toAlgebra)
    (hfinite : ∀ r, @FiniteDimensional p.ResidueField (F r) _ _
      (@Subalgebra.algebra _ _ _ _
        (Ideal.ResidueField.map p r.1 (algebraMap A D) (r.1.over_def p)).toAlgebra
        (@IntermediateField.toSubalgebra _ _ _ _
          (Ideal.ResidueField.map p r.1 (algebraMap A D) (r.1.over_def p)).toAlgebra
          (F r))).toModule)
    (hseparable : ∀ r, @Algebra.IsSeparable p.ResidueField (F r) _ _
      (@Subalgebra.algebra _ _ _ _
        (Ideal.ResidueField.map p r.1 (algebraMap A D) (r.1.over_def p)).toAlgebra
        (@IntermediateField.toSubalgebra _ _ _ _
          (Ideal.ResidueField.map p r.1 (algebraMap A D) (r.1.over_def p)).toAlgebra (F r))))
    (hpure : ∀ r, IsPurelyInseparable (F r) r.1.ResidueField) :
    ∃ C : Subalgebra A D, Module.Finite A C ∧
      Set.BijOn (fun r : Ideal D ↦ r.comap C.val) (p.primesOver D) (p.primesOver C) ∧
      (∃ L : ∀ r : p.primesOver D,
        @IntermediateField p.ResidueField r.1.ResidueField _ _
          (Ideal.ResidueField.map p r.1 (algebraMap A D) (r.1.over_def p)).toAlgebra,
        ∀ r, (@IntermediateField.toSubfield _ _ _ _
          (Ideal.ResidueField.map p r.1 (algebraMap A D) (r.1.over_def p)).toAlgebra (L r)) =
            (Ideal.ResidueField.map (r.1.comap C.val) r.1 C.val rfl).fieldRange ∧
          (@IntermediateField.toSubfield _ _ _ _
            (Ideal.ResidueField.map p r.1 (algebraMap A D) (r.1.over_def p)).toAlgebra (F r)) ≤
          (@IntermediateField.toSubfield _ _ _ _
            (Ideal.ResidueField.map p r.1 (algebraMap A D) (r.1.over_def p)).toAlgebra (L r)) ∧
          @FiniteDimensional p.ResidueField (L r) _ _
            (@Subalgebra.algebra _ _ _ _
              (Ideal.ResidueField.map p r.1 (algebraMap A D) (r.1.over_def p)).toAlgebra
              (@IntermediateField.toSubalgebra _ _ _ _
                (Ideal.ResidueField.map p r.1 (algebraMap A D) (r.1.over_def p)).toAlgebra
                (L r))).toModule ∧
          IsPurelyInseparable (L r) r.1.ResidueField) ∧
      Algebra.IsIntegral C D := by
  classical
  have _hseparable := hseparable
  let : Finite (p.primesOver D) := hfibre.to_subtype
  have hspan (r : p.primesOver D) :
      let := (Ideal.ResidueField.map p r.1 (algebraMap A D) (r.1.over_def p)).toAlgebra
      let : Module p.ResidueField r.1.ResidueField := Algebra.toModule
      let : Algebra p.ResidueField (F r) := (F r).toSubalgebra.algebra
      let : Module p.ResidueField (F r) := Algebra.toModule
      ∃ s : Finset (F r), Submodule.span p.ResidueField (s : Set (F r)) = ⊤ := by
    let := (Ideal.ResidueField.map p r.1 (algebraMap A D) (r.1.over_def p)).toAlgebra
    let : Module p.ResidueField r.1.ResidueField := Algebra.toModule
    let : Algebra p.ResidueField (F r) := (F r).toSubalgebra.algebra
    let : Module p.ResidueField (F r) := Algebra.toModule
    exact (hfinite r).fg_top
  choose s hs using hspan
  let I := Σ r : p.primesOver D, {x : F r // x ∈ s r}
  have hfrac (i : I) := residue_fraction i.1.1 (i.2.1 : i.1.1.ResidueField)
  choose a b hab using hfrac
  have hsep : ∀ r t : p.primesOver D, ∃ z : D, r ≠ t → z ∈ r.1 ∧ z ∉ t.1 := by
    intro r t
    by_cases h : r = t
    · exact ⟨0, fun hne ↦ (hne h).elim⟩
    · have hnot : ¬r.1 ≤ t.1 := by
        intro hle
        have hlt := Ideal.IsIntegral.comap_lt_comap (R := A)
          (lt_of_le_of_ne hle (fun he ↦ h (Subtype.ext he)))
        change r.1.under A < t.1.under A at hlt
        rw [← r.1.over_def p, ← t.1.over_def p] at hlt
        exact lt_irrefl _ hlt
      obtain ⟨z, hz, hzt⟩ := SetLike.not_le_iff_exists.mp hnot
      exact ⟨z, fun _ ↦ ⟨hz, hzt⟩⟩
  choose z hz using hsep
  let T : Set D := Set.range a ∪ Set.range b ∪
    Set.range (fun rt : p.primesOver D × p.primesOver D ↦ z rt.1 rt.2)
  have hT : T.Finite := (Set.finite_range a).union (Set.finite_range b) |>.union
    (Set.finite_range _)
  let C := Algebra.adjoin A T
  have : Module.Finite A C := Algebra.finite_adjoin_of_finite_of_isIntegral hT
    (fun x _ ↦ Algebra.IsIntegral.isIntegral x)
  have : Algebra.IsIntegral C D := ⟨fun x ↦
    (Algebra.IsIntegral.isIntegral (R := A) x).tower_top⟩
  refine ⟨C, inferInstance, ?_, ?_, inferInstance⟩
  · refine ⟨?_, ?_, ?_⟩
    · intro r hr
      let : r.IsPrime := hr.1
      let : r.LiesOver p := hr.2
      exact ⟨inferInstance, ⟨by
        change p = (r.comap C.val).comap (algebraMap A C)
        exact r.over_def p⟩⟩
    · intro r hr t ht he
      change r.comap C.val = t.comap C.val at he
      by_contra hne
      have hrt : (⟨r, hr⟩ : p.primesOver D) ≠ ⟨t, ht⟩ := fun h ↦ hne congr($h.1)
      have hzc : z ⟨r, hr⟩ ⟨t, ht⟩ ∈ C := Algebra.subset_adjoin
        (Or.inr ⟨(⟨r, hr⟩, ⟨t, ht⟩), rfl⟩)
      have hm : (⟨z ⟨r, hr⟩ ⟨t, ht⟩, hzc⟩ : C) ∈ r.comap C.val :=
        (hz _ _ hrt).1
      rw [he] at hm
      exact (hz _ _ hrt).2 hm
    · intro q hq
      let : q.IsPrime := hq.1
      obtain ⟨r, _, hr, he⟩ := Ideal.exists_ideal_over_prime_of_isIntegral q (⊥ : Ideal D)
        (by simp)
      refine ⟨r, ⟨hr, ⟨?_⟩⟩, he⟩
      rw [Ideal.under, ← show q.comap (algebraMap A C) = p from hq.2.1.symm, ← he,
        Ideal.comap_comap]
      rfl
  · have hres : ∀ r : p.primesOver D,
        letI := (Ideal.ResidueField.map p r.1 (algebraMap A D) (r.1.over_def p)).toAlgebra
        ∃ L : IntermediateField p.ResidueField r.1.ResidueField,
        L.toSubfield = (Ideal.ResidueField.map (r.1.comap C.val) r.1 C.val rfl).fieldRange ∧
        (F r).toSubfield ≤ L.toSubfield ∧
        @FiniteDimensional p.ResidueField L _ _ L.toSubalgebra.algebra.toModule ∧
        IsPurelyInseparable L r.1.ResidueField := by
      intro r
      let := (Ideal.ResidueField.map p r.1 (algebraMap A D) (r.1.over_def p)).toAlgebra
      let : Module p.ResidueField r.1.ResidueField := Algebra.toModule
      let : Algebra p.ResidueField (F r) := (F r).toSubalgebra.algebra
      let : Module p.ResidueField (F r) := Algebra.toModule
      let q := r.1.comap C.val
      let : q.LiesOver p := ⟨r.1.over_def p⟩
      let := (Ideal.ResidueField.map p q (algebraMap A C) (q.over_def p)).toAlgebra
      let : Module p.ResidueField q.ResidueField := Algebra.toModule
      let f : q.ResidueField →ₐ[p.ResidueField] r.1.ResidueField :=
        { __ := Ideal.ResidueField.map q r.1 C.val rfl
          commutes' := by
            intro x
            have he : (Ideal.ResidueField.map q r.1 C.val rfl).comp
                (Ideal.ResidueField.map p q (algebraMap A C) (q.over_def p)) =
                Ideal.ResidueField.map p r.1 (algebraMap A D) (r.1.over_def p) := by
              apply Ideal.ResidueField.ringHom_ext
              ext a
              simp only [RingHom.comp_apply, Ideal.ResidueField.map_algebraMap]
              rfl
            exact RingHom.congr_fun he x }
      have : FiniteDimensional p.ResidueField q.ResidueField := residue_finite p q
      let : Algebra p.ResidueField f.fieldRange := f.fieldRange.toSubalgebra.algebra
      let : Module p.ResidueField f.fieldRange := Algebra.toModule
      have : FiniteDimensional p.ResidueField f.fieldRange :=
        f.equivFieldRange.toLinearEquiv.finiteDimensional
      have hcapture : (F r).toSubfield ≤ f.fieldRange.toSubfield := by
        have hgen : ∀ x ∈ s r, (x : r.1.ResidueField) ∈ f.fieldRange := by
          intro x hx
          let i : I := ⟨r, x, hx⟩
          have ha : a i ∈ C := Algebra.subset_adjoin (Or.inl (Or.inl ⟨i, rfl⟩))
          have hb : b i ∈ C := Algebra.subset_adjoin (Or.inl (Or.inr ⟨i, rfl⟩))
          rw [← hab i]
          apply f.fieldRange.div_mem
          · refine ⟨algebraMap C q.ResidueField ⟨a i, ha⟩, ?_⟩
            exact Ideal.ResidueField.map_algebraMap q r.1 C.val rfl _
          · refine ⟨algebraMap C q.ResidueField ⟨b i, hb⟩, ?_⟩
            exact Ideal.ResidueField.map_algebraMap q r.1 C.val rfl _
        have hle : Submodule.span p.ResidueField (s r : Set (F r)) ≤
            f.fieldRange.toSubalgebra.toSubmodule.comap (F r).val.toLinearMap :=
          Submodule.span_le.mpr hgen
        rw [hs r] at hle
        intro x hx
        exact hle (show (⟨x, hx⟩ : F r) ∈ ⊤ from trivial)
      refine ⟨f.fieldRange, rfl, hcapture, inferInstance, ?_⟩
      let : Algebra (F r) f.fieldRange := (IntermediateField.inclusion hcapture).toAlgebra
      let : IsScalarTower (F r) f.fieldRange r.1.ResidueField :=
        IsScalarTower.of_algebraMap_eq' rfl
      let := hpure r
      exact IsPurelyInseparable.tower_top (F r) f.fieldRange r.1.ResidueField
    choose L hL using hres
    exact ⟨L, hL⟩

end Algebra
