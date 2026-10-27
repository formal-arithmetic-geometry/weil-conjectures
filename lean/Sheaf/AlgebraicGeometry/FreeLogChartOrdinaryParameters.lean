/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.LogEtaleRestrictionStalkComparison
public import Sheaf.AlgebraicGeometry.LogRegularPair
public import Sheaf.AlgebraicGeometry.IsRegularScheme
public import WeilConjectures.RingTheory.IsRegularSystemOfParameters
public import Mathlib.Data.List.OfFn

public import Sheaf.AlgebraicGeometry.FreeLogChartCoordinates

import Sheaf.AlgebraicGeometry.EtaleLogRegularRestriction
import Sheaf.AlgebraicGeometry.FreeLogChartStrictParameters
import Sheaf.AlgebraicGeometry.StrictLocalParameterDescent
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Ordinary parameters of a free logarithmic chart

Source: Illusie--Laszlo--Orgogozo, Exposé VI 1.2 and 1.6--1.7, pp. 69--70
(blueprint: lem-trf-free-log-chart-ordinary-parameters).

The inverse-image log structure is supplied with equality to the existing slice-site
restriction. The strict-local functions use the canonical affine-colimit comparison.
The ordered sublist retains the actual chart functions, without replacing them by associates.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry

private theorem regular_of_parameters {R : Type u} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] (l : List R)
    (hl : IsLocalRing.IsRegularSystemOfParameters l) : IsRegularLocalRing R := by
  classical
  apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
  rw [← hl.1, ← hl.2]
  have hs : (Ideal.span {x | x ∈ l}).spanFinrank ≤ l.toFinset.card := by
    have h := Submodule.spanFinrank_span_le_ncard_of_finite (R := R) l.finite_toSet
    have hc : {x | x ∈ l}.ncard = l.toFinset.card := by
      rw [← List.coe_toFinset, Set.ncard_coe_finset]
    rwa [hc] at h
  exact_mod_cast hs.trans l.toFinset_card_le

-- The existing statement names a proof binder inside its quantified conclusion.
-- Keep that signature verbatim while suppressing only its unused-variable style warning.
set_option linter.unusedVariables false in
/-- A free chart on an étale neighbourhood of a log regular fs log scheme gives
ordinary and strict-local regular parameters, with their original indexed values.
`N` is the inverse-image log structure: its underlying prelog structure equals the
canonical slice restriction. No independent fs or regularity hypothesis is made on N.
The characteristic isomorphism is normalized on every chart monomial, including
monomials in the coordinates which become units. The ideal is transported to the
recorded strict henselization by the canonical cofinality isomorphism.

Source: ILO VI 1.2, 1.6--1.7, printed pp. 69--70
(blueprint: lem-trf-free-log-chart-ordinary-parameters).

Proof:
1. Étale restriction identifies pointed-neighbourhood stalks and their structural
rings. The strict-local isomorphism of lem-trf-ind-etale-strict-local-invariance
preserves units, characteristic monoids, nonunit ideals and dimension. Therefore
the two log-regularity conditions on X hold for its inverse-image structure on W.
2. Ordinary stalks are Noetherian by affine localization and local Noetherianity.
The affine strict-local comparison identifies A with their strict henselization,
so A is Noetherian and local. The local map B -> A reflects units, hence the same
indices J select the nonunits in both rings.
3. Let K be the complementary indices. A monomial is a unit exactly when all
its positively occurring factors are units. The chart pushout is N^J times A^units:
[(a_J,a_K),v] maps to (a_J,t_K^a_K v), with inverse (a_J,v) -> [(a_J,0),v].
Quotienting units gives the displayed monomial-normalized characteristic isomorphism.
A nonunit has nonzero J-part, so its image lies in (t_j:j in J); each t_j is such
an image. This proves the ideal equality.
4. Log regularity says A/I is regular and dim A = dim(A/I) + |J|. Lift a regular
system of parameters of A/I. Together with the given ordered t_j these generate
the maximal ideal with dim A entries, so form a regular system of parameters.
5. Regularity descends from a strict henselization to B. Strict-henselization
cotangent base change sends [t_j] tensor 1 to [t_j]. Their classes are independent
in A by step 4 and the regular-local cotangent-dimension formula; faithful field
extension therefore gives independence of their original classes in B.
6. Extend those classes to a basis of the cotangent space of B, and lift the extra
vectors. Nakayama makes the resulting list generate the maximal ideal. Its length
is dim B by regularity, proving the ordinary parameter assertion for the actual
chart functions. Every ordinary stalk is regular, so W is a regular scheme.
7. The characteristic vanishes precisely when J is empty, equivalently when the
product f is a unit in B, equivalently w lies in D(f). This identifies the inverse
image of U with D(f). The empty product is 1; empty sublists extend by the whole
parameter list. Zero-dimensional local rings and the empty scheme are included.
-/
theorem freeLogChart_ordinary_parameters
    (X : FineSaturatedLogScheme.{u}) (hX : X.IsLogRegular)
    (W : X.scheme.Etale) [IsAffine W.left] [IsLocallyNoetherian W.left]
    (N : EtaleLogStructure W.left)
    (hN : N.toEtalePrelogStructure = X.logStructure.toEtalePrelogStructure.etaleRestrict W)
    (r : ℕ) (β : Multiplicative (ULift.{u} (Fin r) → ℕ) →*
      N.monoidSheaf.obj.obj (op (Scheme.Etale.mk (𝟙 W.left))))
    (hβ : N.IsChart (Scheme.Etale.mk (𝟙 W.left)) β) :
    (∃ hfs : N.IsFineSaturated,
      FineSaturatedLogScheme.IsLogRegular ⟨W.left, inferInstance, N, hfs⟩) ∧
    IsRegularScheme W.left ∧
    W.hom ⁻¹' X.logStructure.trivialityLocus =
      (W.left.basicOpen (∏ i : ULift.{u} (Fin r), FreeLogChart.coordinate N β i) : Set W.left) ∧
    (∀ (w : W.left) (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
      (t : Spec (.of Ω) ⟶ W.left) (ht : (Scheme.SpecToEquivOfField Ω W.left t).1 = w),
      (∃ E : N.characteristic t ≃*
          Multiplicative ({i : ULift.{u} (Fin r) //
            ¬ IsUnit (FreeLogChart.ordinaryCoordinate N β w i)} → ℕ),
        ∀ a : Multiplicative (ULift.{u} (Fin r) → ℕ),
          E (Associates.mk (N.toEtalePrelogStructure.germ t
            (Scheme.Etale.mk (𝟙 W.left)) (CategoryTheory.Over.homMk t (by simp)) (β a))) =
            Multiplicative.ofAdd (fun j ↦ a.toAdd j.val)) ∧
      (N.nonunitIdeal t).map (strictLocalRingStrictHenselizationIso W.left t).hom.hom =
        Ideal.span {a | ∃ i : ULift.{u} (Fin r),
          ¬ IsUnit (FreeLogChart.ordinaryCoordinate N β w i) ∧
            a = FreeLogChart.strictCoordinate N β t i} ∧
      (∃ (_ : IsLocalRing (Scheme.strictHenselizationRing t))
          (_ : IsNoetherianRing (Scheme.strictHenselizationRing t)),
        (∃ b : List (Scheme.strictHenselizationRing t),
          IsLocalRing.IsRegularSystemOfParameters
            (((FreeLogChart.nonunitIndices N β w).map
              (FreeLogChart.strictCoordinate N β t)) ++ b))) ∧
      (∃ b : List (W.left.presheaf.stalk w),
        IsLocalRing.IsRegularSystemOfParameters
          (((FreeLogChart.nonunitIndices N β w).map
            (FreeLogChart.ordinaryCoordinate N β w)) ++ b)) ∧
      ((∀ i : ULift.{u} (Fin r), IsUnit (FreeLogChart.ordinaryCoordinate N β w i)) →
        IsUnit (W.left.presheaf.germ ⊤ w (by trivial)
          (∏ i : ULift.{u} (Fin r), FreeLogChart.coordinate N β i)))) ∧
    (r = 0 → (∏ i : ULift.{u} (Fin r), FreeLogChart.coordinate N β i) = 1) := by
  classical
  obtain ⟨⟨hfs, hlog⟩, hrestriction⟩ := etale_logRegular_restriction X hX W N hN
  have hstrict := freeLogChart_strict_parameters W.left N hfs hlog r β hβ
  have hord (w : W.left) (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
      (t : Spec (.of Ω) ⟶ W.left)
      (ht : (Scheme.SpecToEquivOfField Ω W.left t).1 = w) :=
    strictLocal_parameters_descent W.left w Ω t ht
      ((FreeLogChart.nonunitIndices N β w).map (FreeLogChart.coordinate N β))
      (by
        obtain ⟨hl, hn, b, hb⟩ := (hstrict w Ω t ht).2.2
        let := hl
        let := hn
        refine ⟨hl, hn, b, ?_⟩
        have he :
            ((FreeLogChart.nonunitIndices N β w).map (FreeLogChart.coordinate N β)).map
              (fun f ↦ (strictLocalRingStrictHenselizationIso W.left t).hom
                (strictLocalGerm W.left t (Scheme.Etale.mk (𝟙 W.left))
                  (CategoryTheory.Over.homMk t (by simp)) f)) =
              (FreeLogChart.nonunitIndices N β w).map
                (FreeLogChart.strictCoordinate N β t) := by
          rw [List.map_map]
          rfl
        rw [he]
        exact hb)
  have hregular : IsRegularScheme W.left := by
    refine ⟨inferInstance, ⟨fun w ↦ ?_⟩⟩
    let Ω := AlgebraicClosure (W.left.residueField w)
    let z : Σ x : W.left, W.left.residueField x ⟶ CommRingCat.of Ω :=
      ⟨w, CommRingCat.ofHom (algebraMap (W.left.residueField w) Ω)⟩
    let t := (Scheme.SpecToEquivOfField Ω W.left).symm z
    have ht : (Scheme.SpecToEquivOfField Ω W.left t).1 = w :=
      congrArg Sigma.fst ((Scheme.SpecToEquivOfField Ω W.left).apply_symm_apply z)
    obtain ⟨b, hb⟩ := hord w Ω t ht
    exact regular_of_parameters _ hb
  have hunits (w : W.left) :
      w ∈ N.trivialityLocus ↔ ∀ i, IsUnit (FreeLogChart.ordinaryCoordinate N β w i) := by
    constructor
    · intro hw i
      by_contra hi
      let Ω := AlgebraicClosure (W.left.residueField w)
      let z : Σ x : W.left, W.left.residueField x ⟶ CommRingCat.of Ω :=
        ⟨w, CommRingCat.ofHom (algebraMap (W.left.residueField w) Ω)⟩
      let t := (Scheme.SpecToEquivOfField Ω W.left).symm z
      have ht : (Scheme.SpecToEquivOfField Ω W.left t).1 = w :=
        congrArg Sigma.fst ((Scheme.SpecToEquivOfField Ω W.left).apply_symm_apply z)
      obtain ⟨E, _⟩ := (hstrict w Ω t ht).1
      have : Subsingleton (N.characteristic t) := hw Ω t ht
      have he : Multiplicative.ofAdd (fun _ : {j //
            ¬ IsUnit (FreeLogChart.ordinaryCoordinate N β w j)} ↦ (0 : ℕ)) =
          Multiplicative.ofAdd (fun _ ↦ (1 : ℕ)) :=
        E.symm.injective (Subsingleton.elim _ _)
      exact Nat.zero_ne_one (congrArg (fun a ↦ a.toAdd ⟨i, hi⟩) he)
    · intro hw Ω _ _ t ht
      obtain ⟨E, _⟩ := (hstrict w Ω t ht).1
      refine ⟨fun a b ↦ E.injective ?_⟩
      change (E a).toAdd = (E b).toAdd
      funext j
      exact (j.2 (hw j.1)).elim
  have hproduct (w : W.left) :
      IsUnit (W.left.presheaf.germ ⊤ w (by trivial)
        (∏ i : ULift.{u} (Fin r), FreeLogChart.coordinate N β i)) ↔
        ∀ i, IsUnit (FreeLogChart.ordinaryCoordinate N β w i) := by
    rw [map_prod, IsUnit.prod_univ_iff]
    rfl
  refine ⟨⟨hfs, hlog⟩, hregular, ?_, ?_, ?_⟩
  · rw [hrestriction]
    ext w
    exact (hunits w).trans ((hproduct w).symm.trans (W.left.mem_basicOpen_top _ w).symm)
  · intro w Ω _ _ t ht
    have ho := hord w Ω t ht
    simp only [List.map_map, Function.comp_def] at ho
    exact ⟨(hstrict w Ω t ht).1, (hstrict w Ω t ht).2.1,
      (hstrict w Ω t ht).2.2, ho, (hproduct w).mpr⟩
  · intro hr
    subst r
    exact Finset.prod_of_isEmpty _

end AlgebraicGeometry
