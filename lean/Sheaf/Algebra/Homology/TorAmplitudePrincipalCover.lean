/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NW
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Flat.Localization
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction
import Mathlib.Algebra.Category.ModuleCat.Descent
import WeilConjectures.Algebra.Homology.KFlatModuleBaseChange
import WeilConjectures.RingTheory.HomologyVanishingLocalizationSpan

/-!
# Tor amplitude descends from a finite principal cover

Source: Stacks Project, More on Algebra, Tag 066N, lemma-glue-tor-amplitude
(blueprint: lem-weil-pbc-tor-amplitude-principal-cover-glue).
-/

@[expose] public section

universe w₁ w₂ u

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace DerivedCategory

private theorem kFlat_extendScalars
    {A B : Type u} [CommRing A] [CommRing B] (ρ : A →+* B)
    (P : CochainComplex (ModuleCat.{u} A) ℤ)
    (hP : (HomologicalComplex.quasiIso (ModuleCat.{u} A) (.up ℤ)).kFlat P) :
    (HomologicalComplex.quasiIso (ModuleCat.{u} B) (.up ℤ)).kFlat
      (((ModuleCat.extendScalars ρ).mapHomologicalComplex (.up ℤ)).obj P) := by
  have hacyclic (L : CochainComplex (ModuleCat.{u} A) ℤ) (hL : L.Acyclic) :
      (CochainComplex.mapBifunctor L P (curriedTensor _)).Acyclic := by
    have hk := (HomotopyCategory.kFlat_quotient_obj_iff P).2 hP
    have h := (HomotopyCategory.kFlat_iff_preserves_acyclic _).1 hk
      ((HomotopyCategory.quotient _ _).obj L)
      ((HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic L).2 hL)
    exact (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic _).1 h.2
  have hbase := CochainComplex.acyclic_mapBifunctor_extendScalars_of_kFlat ρ P hacyclic
  rw [← HomotopyCategory.kFlat_quotient_obj_iff,
    HomotopyCategory.kFlat_iff_preserves_acyclic]
  intro N hN
  obtain ⟨N, rfl⟩ := N.quotient_obj_surjective
  rw [HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic] at hN
  have hr := (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic _).2
    (hbase N hN)
  refine ⟨?_, hr⟩
  exact (HomotopyCategory.subcategoryAcyclic _).prop_of_iso (β_ _ _) hr

/-- Tor amplitude in a fixed interval descends from a finite principal localization cover.
Source: Stacks Project, More on Algebra, Tag 066N, lemma-glue-tor-amplitude.
(blueprint: lem-weil-pbc-tor-amplitude-principal-cover-glue).

The termwise `extendScalars` is ordinary localization of the complex. The derived tensor in
`torAmplitudeIn` is tested against every module in degree zero, without a flatness condition;
it is computed on K-flat models by `QObjTensorQObjIsoOfKFlatLeft`. This is the ordinary-module
specialization of change of rings on the singleton site with the trivial topology.

Proof: Fix a module M and a degree n outside [a,b]. Choose a K-flat resolution P of K
(lem-pc-kflat-resolution). The complex C = P tensor M computes K tensor-derived M by
lem-pc-source-kflat-module-tensor-model. Localization is flat
(lem-weil-pbc-localization-flat), so exactness of flat tensor
(lem-weil-pbc-flat-tensor-exact) identifies localized cycles, boundaries and cohomology;
in particular P localized remains a resolution of K localized. By
lem-pc-kflat-extension-of-scalars, P localized is K-flat over the localized ring. Applying
lem-pc-source-kflat-module-tensor-model over that ring identifies C localized with the tensor
of P localized and M localized: on pure tensors the comparison multiplies the two scalar
factors, with inverse putting the scalar in the first factor and 1 in the second. These
maps respect balancing and commute with the differential. The assumed local amplitude
therefore kills H^n(C localized). Finally lem-pc-homology-vanishing-localization-span kills
H^n(C), since the f i generate the unit ideal. Vary M and n. For an empty family the
unit-ideal condition forces the zero ring, so the same vanishing argument applies. -/
theorem torAmplitudeIn_of_principal_cover
    {R : Type u} [CommRing R] [HasDerivedCategory.{w₁} (ModuleCat.{u} R)]
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (a b : ℤ) (_hab : a ≤ b)
    (r : ℕ) (f : Fin r → R)
    [∀ i : Fin r, HasDerivedCategory.{w₂} (ModuleCat.{u} (Localization.Away (f i)))]
    (_hf : Ideal.span (Set.range f) = ⊤)
    (_hlocal : ∀ i : Fin r,
      torAmplitudeIn (ModuleCat.{u} (Localization.Away (f i))) a b
        (Q.obj ((Functor.mapHomologicalComplex
          (ModuleCat.extendScalars (algebraMap R (Localization.Away (f i))))
          (ComplexShape.up ℤ)).obj K))) :
    torAmplitudeIn (ModuleCat.{u} R) a b (Q.obj K) := by
  classical
  obtain ⟨P, π, hπ, _, hP⟩ := CochainComplex.exists_quasiIso_flat_kFlat K
  have : QuasiIso π := hπ
  have : IsIso (Q.map π) := (isIso_Q_map_iff_quasiIso _ π).2 hπ
  intro M
  let C := ((tensorRight M).mapHomologicalComplex (.up ℤ)).obj P
  let e : Q.obj K ⊗ (singleFunctor (ModuleCat.{u} R) 0).obj M ≅ Q.obj C :=
    whiskerRightIso (asIso (Q.map π)).symm _ ≪≫ QObjTensorSingleFunctorObjIso P hP M
  -- On each localization, the extended K-flat model computes the local derived tensor.
  have hlocal (i : Fin r) : homologyConcentratedIn a b
      (Q.obj ((Functor.mapHomologicalComplex
        (ModuleCat.extendScalars (algebraMap R (Localization.Away (f i)))) (.up ℤ)).obj C)) := by
    let S := Localization.Away (f i)
    let F : ModuleCat.{u} R ⥤ ModuleCat.{u} S :=
      ModuleCat.extendScalars (algebraMap R S)
    let FC := F.mapHomologicalComplex (.up ℤ)
    have : F.Additive := (ModuleCat.extendRestrictScalarsAdj _).left_adjoint_additive
    have : PreservesFiniteLimits F := ModuleCat.preservesFiniteLimits_extendScalars_of_flat
      (RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat S (Submonoid.powers (f i))))
    have : F.PreservesHomology := inferInstance
    have : QuasiIso (FC.map π) := inferInstance
    have : IsIso (Q.map (FC.map π)) := (isIso_Q_map_iff_quasiIso _ _).2 inferInstance
    let ep : Q.obj (FC.obj P) ≅ Q.obj (FC.obj K) := asIso (Q.map (FC.map π))
    let ec : FC.obj C ≅
        ((tensorRight (F.obj M)).mapHomologicalComplex (.up ℤ)).obj (FC.obj P) :=
      ((NatIso.mapHomologicalComplex (Functor.Monoidal.commTensorRight F M)
        (.up ℤ)).app P).symm
    let et : Q.obj (FC.obj C) ≅
        Q.obj (FC.obj K) ⊗ (singleFunctor (ModuleCat.{u} S) 0).obj (F.obj M) :=
      Q.mapIso ec ≪≫
        (QObjTensorSingleFunctorObjIso (FC.obj P)
          (kFlat_extendScalars (algebraMap R S) P hP) (F.obj M)).symm ≪≫
        whiskerRightIso ep _
    have ht := _hlocal i (F.obj M)
    have := ht.1
    have := ht.2
    exact ⟨TStructure.t.isGE_of_iso et.symm a,
      TStructure.t.isLE_of_iso et.symm b⟩
  -- Vanishing of the localized tensor complexes descends degree by degree.
  have hv (n : ℤ) (hn : n < a ∨ b < n) :
      IsZero ((homologyFunctor (ModuleCat.{u} R) n).obj (Q.obj C)) := by
    apply homology_vanishes_of_localization_span C r f _hf n
    intro i
    rcases hn with hn | hn
    · exact (isGE_iff _ a).1 (hlocal i).1 n hn
    · exact (isLE_iff _ b).1 (hlocal i).2 n hn
  have hc : homologyConcentratedIn a b (Q.obj C) :=
    ⟨(isGE_iff _ a).2 (fun n hn ↦ hv n (Or.inl hn)),
      (isLE_iff _ b).2 (fun n hn ↦ hv n (Or.inr hn))⟩
  have := hc.1
  have := hc.2
  exact ⟨TStructure.t.isGE_of_iso e.symm a,
    TStructure.t.isLE_of_iso e.symm b⟩

end DerivedCategory
