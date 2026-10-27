/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Properties
public import Sheaf.AlgebraicGeometry.IsRegularScheme
public import WeilConjectures.RingTheory.IsRegularSystemOfParameters
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Invertible
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import WeilConjectures.Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.Nilpotent.Lemmas
import Sheaf.RingTheory.TransversePrimeIdealParameters
import Sheaf.AlgebraicGeometry.StalkNonzerodivisorCartierSpreading
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Sheaf.AlgebraicGeometry.CartierDivisorNowhereDense

/-!
# Reduced Cartier divisors defined by products of regular parameters

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Expose VI, 1.4 and 1.7,
printed pp. 69--70, and VIII, 4.1.1--4.1.2, printed p. 117; Stacks Project,
Tags 00NP, 0BIA, 00CT, 01QO, 01J0, 0AG8 and 07ZU
(blueprint: lem-trf-parameter-product-reduced-cartier).
-/

@[expose] public section

set_option autoImplicit false

universe u

open scoped BigOperators

namespace AlgebraicGeometry

open CategoryTheory

/-- Pairwise nondividing primes have product ideal equal to their intersection. -/
private theorem prime_product_intersection {R : Type u} [CommRing R] [IsDomain R]
    {ι : Type*} [Fintype ι] (a : ι → R) (hp : ∀ i, Prime (a i))
    (hne : Pairwise fun i j ↦ ¬ a i ∣ a j) :
    Ideal.span {∏ i, a i} = ⨅ i, Ideal.span {a i} := by
  classical
  ext x
  simp only [Ideal.mem_span_singleton, Ideal.mem_iInf]
  constructor
  · intro hx i
    exact (Finset.dvd_prod_of_mem a (Finset.mem_univ i)).trans hx
  · intro hx
    have aux (s : Finset ι) : ∀ x : R,
        (∀ i ∈ s, a i ∣ x) → (∏ i ∈ s, a i) ∣ x := by
      induction s using Finset.induction_on with
      | empty => simp
      | @insert i s hi ih =>
        intro x h
        obtain ⟨b, hb⟩ := h i (Finset.mem_insert_self i s)
        rw [hb, Finset.prod_insert hi]
        apply mul_dvd_mul_left
        apply ih
        intro j hj
        have hjx := h j (Finset.mem_insert_of_mem hj)
        rw [hb] at hjx
        exact ((hp j).dvd_or_dvd hjx).resolve_left
          (hne (fun hji ↦ hi (hji ▸ hj)))
    exact aux Finset.univ x (fun i _ ↦ hx i)

/-- The stalk of the principal closed subscheme is the quotient by its germ ideal. -/
private theorem principal_subscheme_reduced (X : Scheme.{u}) (f : Γ(X, ⊤))
    (h : ∀ x : X, (Ideal.span {X.presheaf.germ ⊤ x trivial f}).IsRadical) :
    IsReduced (X.zeroLocusSubscheme {f}) := by
  let I := Scheme.IdealSheafData.ofIdealTop (Ideal.span {f})
  have (z : I.subscheme) : _root_.IsReduced (I.subscheme.presheaf.stalk z) := by
    obtain ⟨U, hU, hz, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp
      X.isBasis_affineOpens (TopologicalSpace.Opens.mem_top (I.subschemeι z))
    have hk : RingHom.ker (I.subschemeι.stalkMap z).hom =
        Ideal.span {X.presheaf.germ ⊤ (I.subschemeι z) trivial f} := by
      rw [I.subschemeι.ker_stalkMap ⟨U, hU⟩ z hz, I.ker_subschemeι]
      simp only [I, Scheme.IdealSheafData.ofIdealTop_ideal,
        Ideal.map_span, Set.image_singleton]
      congr 2
      exact X.presheaf.germ_res_apply _ _ _ _
    have : (RingHom.ker (I.subschemeι.stalkMap z).hom).IsRadical := hk ▸ h _
    exact (RingHom.ker_isRadical_iff_reduced_of_surjective
      (I.subschemeι.stalkMap_surjective z)).mp this
  exact isReduced_of_isReduced_stalk I.subscheme

open scoped Classical in
/-- A product of sections whose nonunit germs occupy distinct positions of a regular system
of parameters cuts out a reduced effective Cartier divisor with dense open complement.
The embedding of nonunit indices into `Fin d` records positions, including multiplicities
of the original indexed family; no choice of a parameter system is fixed globally.
`IsDomain` includes nonzeroness. The ideal intersection and product use the empty-index
conventions `⊤` and `1`.

Source: Travaux de Gabber, VI 1.4, 1.7 and VIII 4.1.1--4.1.2
(blueprint: lem-trf-parameter-product-reduced-cartier).

Proof plan:
1. At each point, regularity makes the stalk a nonzero domain by
   lem-sc-regular-local-domain (Stacks 00NP). Permute the selected parameter positions to
   the front of a full parameter system. Clause (b) of
   lem-sfb-transverse-prime-ideal-parameters gives incomparable principal prime ideals,
   their intersection equal to the selected product ideal, radicality and a nonzerodivisor
   product. This includes zero selected parameters. Each selected factor is nonzero, hence
   is a prime element; ideal incomparability rules out divisibility between distinct ones.
   The remaining germs are units, so the full product differs from the selected product
   by a unit and has the same ideal and nonzerodivisor property.
2. On an affine chart the closed subscheme is the spectrum of the quotient by the product.
   lem-weil-pbc-localization-at-prime-of-quotient (Stacks 00CT) identifies its stalk with the
   quotient of the ambient stalk by the computed principal ideal. A quotient by a radical
   ideal is reduced, so all stalks of this closed subscheme are reduced (Stacks 01J0).
3. The ideal sheaf has at every point the germ ideal computed in step 1. Apply the scheme
   clause of lem-sfb-stalk-nonzerodivisor-cartier-spreading (Stacks 0AG8) using local
   Noetherianity from `hY`. It is therefore an effective Cartier ideal. Unit generators
   outside the divisor, and the empty divisor, are allowed.
4. Apply lem-pc-cartier-divisor-nowhere-dense (Stacks 07ZU). The complement of the closed
   subscheme is the basic open of the product, so it is dense. If `r = 0`, the product is
   `1` and the complement is all of `Y`; if `Y` is empty the stalk assertions are vacuous. -/
theorem parameter_product_reduced_cartier
    (Y : Scheme.{u}) (hY : IsRegularScheme Y) (r : ℕ) (t : Fin r → Γ(Y, ⊤))
    (hparams : ∀ y : Y, ∃ (d : ℕ) (p : Fin d → Y.presheaf.stalk y),
      @IsLocalRing.IsRegularSystemOfParameters _ _ _
        (@IsRegular.isRegularLocalRing_stalk Y hY.2 y).toIsNoetherian (List.ofFn p) ∧
      ∃ e : {j : Fin r // ¬ IsUnit (Y.presheaf.germ ⊤ y trivial (t j))} ↪ Fin d,
        ∀ j, Y.presheaf.germ ⊤ y trivial (t j.val) = p (e j)) :
    IsReduced (Y.zeroLocusSubscheme {∏ i, t i}) ∧
      (Scheme.IdealSheafData.ofIdealTop (Ideal.span {∏ i, t i})).IsInvertible ∧
      Dense (Y.basicOpen (∏ i, t i) : Set Y) ∧
      ∀ y : Y, IsDomain (Y.presheaf.stalk y) ∧
        (∀ j : Fin r, ¬ IsUnit (Y.presheaf.germ ⊤ y trivial (t j)) →
          Prime (Y.presheaf.germ ⊤ y trivial (t j))) ∧
        (∀ i j : Fin r, i ≠ j →
          ¬ IsUnit (Y.presheaf.germ ⊤ y trivial (t i)) →
          ¬ IsUnit (Y.presheaf.germ ⊤ y trivial (t j)) →
          ¬ Y.presheaf.germ ⊤ y trivial (t i) ∣ Y.presheaf.germ ⊤ y trivial (t j)) ∧
        Ideal.span {Y.presheaf.germ ⊤ y trivial (∏ i, t i)} =
          Ideal.span {∏ j : {j : Fin r // ¬ IsUnit (Y.presheaf.germ ⊤ y trivial (t j))},
            Y.presheaf.germ ⊤ y trivial (t j.val)} ∧
        Ideal.span {Y.presheaf.germ ⊤ y trivial (∏ i, t i)} =
          ⨅ j : {j : Fin r // ¬ IsUnit (Y.presheaf.germ ⊤ y trivial (t j))},
            Ideal.span {Y.presheaf.germ ⊤ y trivial (t j.val)} ∧
        (Ideal.span {Y.presheaf.germ ⊤ y trivial (∏ i, t i)}).IsRadical ∧
        Y.presheaf.germ ⊤ y trivial (∏ i, t i) ∈ nonZeroDivisors (Y.presheaf.stalk y)  := by
  classical
  have hN : IsLocallyNoetherian Y := hY.1
  have hR : IsRegular Y := hY.2
  have hstalk (y : Y) :
      IsDomain (Y.presheaf.stalk y) ∧
      (∀ j : Fin r, ¬ IsUnit (Y.presheaf.germ ⊤ y trivial (t j)) →
        Prime (Y.presheaf.germ ⊤ y trivial (t j))) ∧
      (∀ i j : Fin r, i ≠ j →
        ¬ IsUnit (Y.presheaf.germ ⊤ y trivial (t i)) →
        ¬ IsUnit (Y.presheaf.germ ⊤ y trivial (t j)) →
        ¬ Y.presheaf.germ ⊤ y trivial (t i) ∣ Y.presheaf.germ ⊤ y trivial (t j)) ∧
      Ideal.span {Y.presheaf.germ ⊤ y trivial (∏ i, t i)} =
        Ideal.span {∏ j : {j : Fin r // ¬ IsUnit (Y.presheaf.germ ⊤ y trivial (t j))},
          Y.presheaf.germ ⊤ y trivial (t j.val)} ∧
      Ideal.span {Y.presheaf.germ ⊤ y trivial (∏ i, t i)} =
        ⨅ j : {j : Fin r // ¬ IsUnit (Y.presheaf.germ ⊤ y trivial (t j))},
          Ideal.span {Y.presheaf.germ ⊤ y trivial (t j.val)} ∧
      (Ideal.span {Y.presheaf.germ ⊤ y trivial (∏ i, t i)}).IsRadical ∧
      Y.presheaf.germ ⊤ y trivial (∏ i, t i) ∈ nonZeroDivisors (Y.presheaf.stalk y) := by
    have hdom : IsDomain (Y.presheaf.stalk y) := inferInstance
    obtain ⟨d, p, hp, e, he⟩ := hparams y
    have hd : ringKrullDim (Y.presheaf.stalk y) = (d : WithBot ℕ∞) := by
      simpa only [List.length_ofFn] using hp.2.symm
    have hall := RingTheory.parameter_product_ideal_properties
      (Y.presheaf.stalk y) d hd p hp d le_rfl
    simp only [Fin.castLE_refl] at hall
    have hpzero : ∀ i, p i ≠ 0 := by
      intro i
      exact Finset.prod_ne_zero_iff.mp (mem_nonZeroDivisors_iff_ne_zero.mp hall.1)
        i (Finset.mem_univ i)
    have hpprime (i : Fin d) : Prime (p i) :=
      (Ideal.span_singleton_prime (hpzero i)).mp (hall.2.1 i)
    let a : Fin r → Y.presheaf.stalk y := fun j ↦ Y.presheaf.germ ⊤ y trivial (t j)
    have hprime (j : Fin r) (hj : ¬ IsUnit (a j)) : Prime (a j) := by
      rw [show a j = p (e ⟨j, hj⟩) from he ⟨j, hj⟩]
      exact hpprime _
    have hdiv (i j : Fin r) (hij : i ≠ j)
        (hi : ¬ IsUnit (a i)) (hj : ¬ IsUnit (a j)) : ¬ a i ∣ a j := by
      change ¬ Y.presheaf.germ ⊤ y trivial (t i) ∣
        Y.presheaf.germ ⊤ y trivial (t j)
      rw [he ⟨i, hi⟩, he ⟨j, hj⟩]
      intro h
      apply hall.2.2.1 (show e ⟨j, hj⟩ ≠ e ⟨i, hi⟩ from
        fun hh ↦ hij (congrArg Subtype.val (e.injective hh)).symm)
      exact Ideal.span_singleton_le_span_singleton.mpr h
    let J := {j : Fin r // ¬ IsUnit (a j)}
    have hint : Ideal.span {∏ j : J, a j.val} = ⨅ j : J, Ideal.span {a j.val} :=
      prime_product_intersection (fun j : J ↦ a j.val) (fun j ↦ hprime j.val j.property)
        (fun i j hij ↦ hdiv i.val j.val (fun hh ↦ hij (Subtype.ext hh)) i.property j.property)
    have hunit : IsUnit (∏ j : {j : Fin r // ¬ ¬ IsUnit (a j)}, a j.val) := by
      exact IsUnit.prod_univ_iff.mpr fun j ↦ not_not.mp j.property
    have heq : Ideal.span {Y.presheaf.germ ⊤ y trivial (∏ i, t i)} =
        Ideal.span {∏ j : J, a j.val} := by
      rw [map_prod, ← Fintype.prod_subtype_mul_prod_subtype (fun j ↦ ¬ IsUnit (a j)) a,
        Ideal.span_singleton_mul_right_unit hunit]
    have hrad : (Ideal.span {Y.presheaf.germ ⊤ y trivial (∏ i, t i)}).IsRadical := by
      rw [heq, hint]
      exact Ideal.isRadical_iInf _ fun j ↦
        (Ideal.isPrime_span_singleton_of_prime (hprime j.val j.property)).isRadical
    have hnonzero : Y.presheaf.germ ⊤ y trivial (∏ i, t i) ≠ 0 := by
      rw [map_prod]
      apply Finset.prod_ne_zero_iff.mpr
      intro j _
      by_cases hj : IsUnit (a j)
      · exact hj.ne_zero
      · exact (hprime j hj).ne_zero
    exact ⟨hdom, hprime, hdiv, heq, heq.trans hint, hrad,
      mem_nonZeroDivisors_iff_ne_zero.mpr hnonzero⟩
  have hinv : (Scheme.IdealSheafData.ofIdealTop (Ideal.span {∏ i, t i})).IsInvertible := by
    let I := Scheme.IdealSheafData.ofIdealTop (Ideal.span {∏ i, t i})
    have hh : I.subschemeι.ker.IsInvertible := by
      apply isInvertible_ker_of_stalk_nonzerodivisor
      intro y
      obtain ⟨U, hU, hy, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp
        Y.isBasis_affineOpens (TopologicalSpace.Opens.mem_top y)
      refine ⟨⟨U, hU⟩, hy, Y.presheaf.germ ⊤ y trivial (∏ i, t i), ?_, ?_⟩
      · rw [I.ker_subschemeι]
        simp only [I, Scheme.IdealSheafData.ofIdealTop_ideal,
          Ideal.map_span, Set.image_singleton]
        congr 2
        exact Y.presheaf.germ_res_apply _ _ _ _
      · intro x z hxz
        apply sub_eq_zero.mp
        apply mem_nonZeroDivisors_iff_left.mp (hstalk y).2.2.2.2.2.2
        exact (mul_sub _ x z).trans (sub_eq_zero.mpr hxz)
    rwa [I.ker_subschemeι] at hh
  have hdense := hinv.compl_support_dense.2.2.1
  have hdense' : Dense (Y.basicOpen (∏ i, t i) : Set Y) := by
    simpa only [Scheme.IdealSheafData.coe_support_ofIdealTop,
      Y.zeroLocus_span, Y.zeroLocus_singleton, TopologicalSpace.Closeds.coe_compl,
      compl_compl] using hdense
  exact ⟨principal_subscheme_reduced Y _ (fun y ↦ (hstalk y).2.2.2.2.2.1),
    hinv, hdense', hstalk⟩

end AlgebraicGeometry
