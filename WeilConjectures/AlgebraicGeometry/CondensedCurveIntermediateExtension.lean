/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedMiddleExtension
public import WeilConjectures.AlgebraicGeometry.CondensedCurvePerverseHeart
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
import WeilConjectures.AlgebraicGeometry.Curve.DenseOpenFiniteComplement
import Mathlib.CategoryTheory.Triangulated.Pretriangulated
import WeilConjectures.CategoryTheory.ExtOneExtensionClassification
import Mathlib.Algebra.CharP.CharAndCard
import WeilConjectures.AlgebraicGeometry.CoefficientHeartClosure
import WeilConjectures.AlgebraicGeometry.Regular
import WeilConjectures.AlgebraicGeometry.FieldBaseChangeDimension
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import WeilConjectures.AlgebraicGeometry.FrobeniusDetailed
import WeilConjectures.DeligneLaumon.CondensedCurveRestrictionCalculus

/-! # Condensed curve perverse intermediate extension

Source: literature/blueprint/latest/blueprint/sec-deligne-laumon-a1/
sk-lem-wft-curve-heart/rem-dl-a1-conventions.md, ordinary direct-image sentence.
(blueprint: lem-dl-a1-condensed-curve-intermediate-extension)
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Triangulated
open CategoryTheory.Pretriangulated
open scoped CategoryTheory.Obj
universe v u' v' w

section AdjunctionVanishing
variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
  {D : Type u'} [Category.{v'} D] [Abelian D]
  (L : C ⥤ D) (G : D ⥤ C) [L.Additive]
  [PreservesFiniteLimits L] [PreservesFiniteColimits L] (adj : L ⊣ G)
  (N : D) (B : C) (hB : IsZero (L.obj B))
include adj hB in
private theorem ext_zero_of_adjunction (δ : (DerivedCategory.singleFunctor C 0).obj B ⟶
    ((DerivedCategory.singleFunctor C 0).obj (G.obj N))⟦(1 : ℤ)⟧) : δ = 0 := by
  let : HasExt C := HasExt.standard C
  let ξ : Abelian.Ext B (G.obj N) 1 := Abelian.Ext.homEquiv.symm δ
  obtain ⟨M, a, b, z, hS, hξ⟩ :=
    (ext_one_extension_classification.{max u v, max u v, w, w, v, v, u, u}
      (G.obj N) B).1 ξ
  have hi : IsIso (L.map a) := ((hS.map_of_exact L).isIso_f_iff).2 hB
  let r : M ⟶ G.obj N := adj.homEquiv M N (inv (L.map a) ≫ adj.counit.app N)
  have har : a ≫ r = 𝟙 _ := by
    apply (adj.homEquiv _ _).symm.injective
    simp [r, adj.homEquiv_naturality_left_symm, adj.homEquiv_symm_id]
  have hδ : hS.singleδ = δ := by
    rw [← ShortComplex.ShortExact.extClass_hom, hξ]
    exact Abelian.Ext.homEquiv.apply_symm_apply δ
  have hz := comp_distTriang_mor_zero₃₁ _ hS.singleTriangle_distinguished
  dsimp only [ShortComplex.ShortExact.singleTriangle] at hz
  rw [hδ] at hz
  change δ ≫ ((DerivedCategory.singleFunctor C 0).map a)⟦(1 : ℤ)⟧' = 0 at hz
  calc
    δ = δ ≫ ((DerivedCategory.singleFunctor C 0).map a)⟦(1 : ℤ)⟧' ≫
        ((DerivedCategory.singleFunctor C 0).map r)⟦(1 : ℤ)⟧' := by
      rw [← (shiftFunctor (DerivedCategory C) (1 : ℤ)).map_comp,
        ← (DerivedCategory.singleFunctor C 0).map_comp, har]
      simp only [CategoryTheory.Functor.map_id, Category.comp_id]
    _ = 0 := by rw [← Category.assoc, hz, zero_comp]
end AdjunctionVanishing

section UniqueEquivariance
variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  (R : C ⥤ D) (G : C ⥤ C) (H : D ⥤ D) (r : R ⋙ H ≅ G ⋙ R)
  {P A : C} {F : D} (α : R.obj P ≅ F) (β : R.obj A ≅ F)
  (s : H.obj F ⟶ F) (e : P ≅ A)
  (he : R.map e.hom ≫ β.hom = α.hom)
  (hu : ∀ e' : P ≅ A, R.map e'.hom ≫ β.hom = α.hom → e' = e)
  (θP : G.obj P ≅ P) (θA : G.obj A ≅ A)
  (hP : r.hom.app P ≫ R.map θP.hom ≫ α.hom = H.map α.hom ≫ s)
  (hA : r.hom.app A ≫ R.map θA.hom ≫ β.hom = H.map β.hom ≫ s)

include r he hu hP hA in
private theorem equivariance_of_unique_iso : θP.hom ≫ e.hom = G.map e.hom ≫ θA.hom := by
  let d : P ≅ A := θP.symm ≪≫ G.mapIso e ≪≫ θA
  have hd : R.map d.hom ≫ β.hom = α.hom := by
    apply (cancel_epi (r.hom.app P ≫ R.map θP.hom)).1
    have hn := r.hom.naturality e.hom
    dsimp only [Functor.comp_map] at hn
    calc
      (r.hom.app P ≫ R.map θP.hom) ≫ R.map d.hom ≫ β.hom =
          r.hom.app P ≫ R.map (G.map e.hom) ≫ R.map θA.hom ≫ β.hom := by
        simp [d, Functor.map_comp, Category.assoc]
      _ = H.map (R.map e.hom) ≫ r.hom.app A ≫ R.map θA.hom ≫ β.hom := by
        simpa only [Category.assoc] using
          congrArg (fun z ↦ z ≫ R.map θA.hom ≫ β.hom) hn.symm
      _ = H.map (R.map e.hom) ≫ H.map β.hom ≫ s := by rw [hA]
      _ = H.map α.hom ≫ s := by
        rw [← Category.assoc, ← H.map_comp, he]
      _ = (r.hom.app P ≫ R.map θP.hom) ≫ α.hom := by
        simpa only [Category.assoc] using hP.symm
  have h := congrArg (fun x : P ≅ A ↦ θP.hom ≫ x.hom) (hu d hd)
  simpa [d, ← Category.assoc] using h.symm
end UniqueEquivariance

namespace AlgebraicGeometry.ProEtale.CondensedCurve

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ] {U C : Scheme.{u}} (j : U ⟶ C)

/-- Restriction of geometric complexes is exact module pullback localized termwise.
Source: latest blueprint, intermediate-extension open identification
(blueprint: lem-dl-a1-condensed-curve-intermediate-extension). -/
abbrev restriction := (CondensedRing.upperStar Λ j).mapDerivedCategory

/-- The restriction map on the shifted ordinary image is the shifted sheaf counit,
after the canonical single-complex and shift comparisons.
Source: latest blueprint, canonical open identification
(blueprint: lem-dl-a1-condensed-curve-intermediate-extension). -/
def openIdentificationMap (F : Modules Λ U) :
    (restriction Λ j).obj ((CondensedRing.shiftedOrdinaryImage Λ j).obj F) ⟶
      (CondensedRing.shiftedSheaf Λ U).obj F :=
  ((restriction Λ j).commShiftIso (1 : ℤ)).hom.app
      ((DerivedCategory.singleFunctor _ 0).obj ((CondensedRing.lowerStar Λ j).obj F)) ≫
    (shiftFunctor _ (1 : ℤ)).map
      (((CondensedRing.upperStar Λ j).mapDerivedCategorySingleFunctor 0).hom.app
        ((CondensedRing.lowerStar Λ j).obj F)) ≫
    (CondensedRing.shiftedSheaf Λ U).map
      ((CondensedRing.upperStarLowerStarAdjunction Λ j).counit.app F)

/-- Both geometric Hom vanishings against every boundary perverse object.
Source: latest blueprint, characterization by boundary Hom-vanishing
(blueprint: lem-dl-a1-condensed-curve-intermediate-extension). -/
def BoundaryMinimal (P : DerivedCategory (Modules Λ C)) : Prop :=
  ∀ Q : DerivedCategory (Modules Λ C), heart Λ C Q →
    IsZero ((restriction Λ j).obj Q) →
      (∀ f : Q ⟶ P, f = 0) ∧ (∀ f : P ⟶ Q, f = 0)

private theorem boundaryMinimal_of_iso {P P' : DerivedCategory (Modules Λ C)}
    (e : P ≅ P') (h : BoundaryMinimal Λ j P') : BoundaryMinimal Λ j P := by
  intro Q hQ hZ
  obtain ⟨h₁, h₂⟩ := h Q hQ hZ
  constructor
  · intro f
    apply (cancel_mono e.hom).1
    simpa only [zero_comp] using h₁ (f ≫ e.hom)
  · intro f
    apply (cancel_epi e.inv).1
    simpa only [comp_zero] using h₂ (e.inv ≫ f)

/-- The canonical restriction/Frobenius comparison, obtained by localizing the
module pullback composition comparison of the commutative Frobenius square.
Source: latest blueprint, Weil compatibility sentence
(blueprint: lem-dl-a1-condensed-curve-intermediate-extension). -/
def restrictionFrobeniusComparison (gU : U ≅ U) (gC : C ≅ C)
    (w : gU.hom ≫ j = j ≫ gC.hom) :
    restriction Λ j ⋙ CondensedRing.StrictWeil.action Λ gU ≅
      CondensedRing.StrictWeil.action Λ gC ⋙ restriction Λ j :=
  (Functor.mapDerivedCategoryCompIso (CondensedRing.upperStar Λ j)
      (CondensedRing.upperStar Λ gU.hom)).symm ≪≫
    Functor.mapDerivedCategoryNatIso
      (CondensedRing.upperStarSquareComparison Λ (CommSq.mk w)).symm ≪≫
    Functor.mapDerivedCategoryCompIso (CondensedRing.upperStar Λ gC.hom)
      (CondensedRing.upperStar Λ j)

/-- The induced Frobenius map on the lisse sheaf shifted by one, using the exact
pullback's canonical single-complex and shift comparisons.
Source: latest blueprint, Weil structure on F[1]
(blueprint: lem-dl-a1-condensed-curve-intermediate-extension). -/
def shiftedWeilMap (gU : U ≅ U) (F : CondensedRing.StrictWeil.WeilModule Λ gU) :
    (CondensedRing.StrictWeil.action Λ gU).obj
        ((CondensedRing.shiftedSheaf Λ U).obj F.carrier) ⟶
      (CondensedRing.shiftedSheaf Λ U).obj F.carrier :=
  ((CondensedRing.StrictWeil.action Λ gU).commShiftIso (1 : ℤ)).hom.app
      ((DerivedCategory.singleFunctor _ 0).obj F.carrier) ≫
    (shiftFunctor _ (1 : ℤ)).map
      (((CondensedRing.upperStar Λ gU.hom).mapDerivedCategorySingleFunctor 0).hom.app
        F.carrier) ≫
    (CondensedRing.shiftedSheaf Λ U).map F.str.hom

/-- Perverse membership, canonical open identification, both boundary Hom vanishings,
unique comparison over the open, and equivariance of that unique comparison.
The isomorphism on the ordinary image is pinned by its prescribed open restriction.
Source: latest blueprint, complete intermediate-extension sentence
(blueprint: lem-dl-a1-condensed-curve-intermediate-extension). -/
def IntermediateExtensionAssertion (gU : U ≅ U) (gC : C ≅ C)
    (w : gU.hom ≫ j = j ≫ gC.hom)
    (F : CondensedRing.StrictWeil.WeilModule Λ gU) : Prop :=
  heart Λ C ((CondensedRing.shiftedOrdinaryImage Λ j).obj F.carrier) ∧
    ∃ β : (restriction Λ j).obj
        ((CondensedRing.shiftedOrdinaryImage Λ j).obj F.carrier) ≅
        (CondensedRing.shiftedSheaf Λ U).obj F.carrier,
      β.hom = openIdentificationMap Λ j F.carrier ∧
      BoundaryMinimal Λ j ((CondensedRing.shiftedOrdinaryImage Λ j).obj F.carrier) ∧
      (∀ (P : DerivedCategory (Modules Λ C)), heart Λ C P →
        ∀ α : (restriction Λ j).obj P ≅ (CondensedRing.shiftedSheaf Λ U).obj F.carrier,
          BoundaryMinimal Λ j P ↔
            ∃! e : P ≅ (CondensedRing.shiftedOrdinaryImage Λ j).obj F.carrier,
              (restriction Λ j).map e.hom ≫ β.hom = α.hom) ∧
      ∃ θA : (CondensedRing.StrictWeil.action Λ gC).obj
          ((CondensedRing.shiftedOrdinaryImage Λ j).obj F.carrier) ≅
          (CondensedRing.shiftedOrdinaryImage Λ j).obj F.carrier,
        (restrictionFrobeniusComparison Λ j gU gC w).hom.app _ ≫
            (restriction Λ j).map θA.hom ≫ β.hom =
          (CondensedRing.StrictWeil.action Λ gU).map β.hom ≫ shiftedWeilMap Λ gU F ∧
        ∀ (P : DerivedCategory (Modules Λ C)), heart Λ C P →
          BoundaryMinimal Λ j P →
          ∀ (α : (restriction Λ j).obj P ≅ (CondensedRing.shiftedSheaf Λ U).obj F.carrier)
            (θP : (CondensedRing.StrictWeil.action Λ gC).obj P ≅ P)
            (e : P ≅ (CondensedRing.shiftedOrdinaryImage Λ j).obj F.carrier),
            (restriction Λ j).map e.hom ≫ β.hom = α.hom →
            (restrictionFrobeniusComparison Λ j gU gC w).hom.app P ≫
                (restriction Λ j).map θP.hom ≫ α.hom =
              (CondensedRing.StrictWeil.action Λ gU).map α.hom ≫ shiftedWeilMap Λ gU F →
            θP.hom ≫ e.hom = (CondensedRing.StrictWeil.action Λ gC).map e.hom ≫ θA.hom

section OpenImmersion
variable [IsOpenImmersion j]

private def openDirectImageFullyFaithful : (CondensedRing.lowerStar Λ j).FullyFaithful := by
  let a := (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} j).mapModAdjunction
    (condensedRingObj Λ C)
  have hf := (ProEtale.openImmersionRestrictionLowerStarAdjunction Ab.{u + 1} j
    ).fullyFaithfulROfIsIsoCounit
  have := hf.full
  have := hf.faithful
  have ha (M) : IsIso (a.counit.app M) := by
    have : IsIso ((Mod.forget _).map (a.counit.app M)) := by
      change IsIso (a.counit.app M).hom
      dsimp only [a]
      rw [Adjunction.mapModAdjunction_counit_app_hom]
      infer_instance
    exact isIso_of_reflects_iso _ (Mod.forget _)
  have : IsIso a.counit := NatIso.isIso_of_isIso_app _
  exact ((Mod.comapEquivalenceOfIsIso (condensedPullbackHom Λ j)).fullyFaithfulFunctor.comp
    a.fullyFaithfulROfIsIsoCounit).ofIso (CondensedRing.comapPullbackHomCompIso Λ j)

private theorem openIdentification_isIso (F : CondensedCurve.Modules Λ U) :
    IsIso (CondensedCurve.openIdentificationMap Λ j F) := by
  have hf := openDirectImageFullyFaithful Λ j
  have := hf.full
  have := hf.faithful
  have : IsIso (CondensedRing.upperStarLowerStarAdjunction Λ j).counit :=
    (CondensedRing.upperStarLowerStarAdjunction Λ j).counit_isIso_of_R_fully_faithful
  unfold CondensedCurve.openIdentificationMap
  infer_instance

private theorem punctual_of_zero_on_open (M : CondensedCurve.Modules Λ C)
    (hM : IsConstantModelConstructible Λ C M)
    (hf : ((j.opensRange : Set C)ᶜ).Finite)
    (hc : ∀ x ∈ (j.opensRange : Set C)ᶜ, IsClosed ({x} : Set C))
    (hZ : IsZero ((CondensedRing.upperStar Λ j).obj M)) :
    CondensedCurve.IsPunctual Λ C M := by
  refine ⟨hM, j.opensRange, hf, hc, ?_⟩
  exact ((CondensedRing.upperStar Λ j.isoOpensRange.inv).map_isZero hZ).of_iso
    (((CondensedRing.upperStarCongr Λ j.isoOpensRange_inv_comp).symm ≪≫
      CondensedRing.upperStarComp Λ j.isoOpensRange.inv j).app M)

private theorem boundary_as_single (hGeo : CondensedCurve.GeometricAssertions Λ C)
    (hf : ((j.opensRange : Set C)ᶜ).Finite)
    (hc : ∀ x ∈ (j.opensRange : Set C)ᶜ, IsClosed ({x} : Set C))
    (Q : DerivedCategory (CondensedCurve.Modules Λ C)) (hQ : CondensedCurve.heart Λ C Q)
    (hZ : IsZero ((CondensedCurve.restriction Λ j).obj Q)) :
    ∃ (B : CondensedCurve.Modules Λ C)
      (_e : Q ≅ (DerivedCategory.singleFunctor _ 0).obj B),
      IsZero ((CondensedRing.upperStar Λ j).obj B) := by
  have hQ' := (hGeo.2.2.1 ⟨Q, hQ.1⟩).mp hQ
  have hZm : IsZero ((CondensedRing.upperStar Λ j).obj
      ((DerivedCategory.homologyFunctor _ (-1)).obj Q)) :=
    ((DerivedCategory.homologyFunctor _ (-1)).map_isZero hZ).of_iso
      (((CondensedRing.upperStar Λ j).mapDerivedCategoryHomologyFunctorIso (-1)).app Q)
  have hP := punctual_of_zero_on_open Λ j _ (hQ.1.2 (-1)) hf hc hZm
  have hH : IsZero ((DerivedCategory.homologyFunctor _ (-1)).obj Q) :=
    hQ'.2.2 _ (𝟙 _) inferInstance hP
  have : Q.IsGE 0 := (DerivedCategory.isGE_iff Q 0).2 (by
    intro n hn
    by_cases he : n = -1
    · subst n; exact hH
    · exact hQ'.1 n he (by omega))
  have : Q.IsLE 0 := (DerivedCategory.isLE_iff Q 0).2 hQ.2.1.1
  obtain ⟨B, ⟨e⟩⟩ := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE Q 0
  refine ⟨B, e, ?_⟩
  let L := CondensedRing.upperStar Λ j
  let H := DerivedCategory.homologyFunctor (CondensedCurve.Modules Λ U) 0
  exact (H.map_isZero hZ).of_iso
    (((DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app (L.obj B)).symm ≪≫
      H.mapIso ((L.mapDerivedCategorySingleFunctor 0).app B).symm ≪≫
      H.mapIso (L.mapDerivedCategory.mapIso e.symm))

private theorem isIso_of_minimal_kernel_cokernel (hGeo : GeometricAssertions Λ C)
    (hf : ((j.opensRange : Set C)ᶜ).Finite)
    (hc : ∀ x ∈ (j.opensRange : Set C)ᶜ, IsClosed ({x} : Set C))
    {M A : Modules Λ C} (f : M ⟶ A)
    (hK : IsConstantModelConstructible Λ C (kernel f))
    (hT : IsConstantModelConstructible Λ C (cokernel f))
    (hM : HasNoPunctualSubsheaf Λ C M)
    (hA : HasNoPunctualSubsheaf Λ C A)
    (hmin : BoundaryMinimal Λ j ((CondensedRing.shiftedSheaf Λ C).obj M))
    [IsIso ((CondensedRing.upperStar Λ j).map f)] : IsIso f := by
  let L := CondensedRing.upperStar Λ j
  have hzK : IsZero (L.obj (kernel f)) :=
    (isZero_kernel_of_mono (L.map f)).of_iso (PreservesKernel.iso L f)
  have hpK := punctual_of_zero_on_open Λ j _ hK hf hc hzK
  have hzeroK := hM (kernel f) (kernel.ι f) inferInstance hpK
  have : Mono f := Preadditive.mono_of_isZero_kernel f hzeroK
  have hzT : IsZero (L.obj (cokernel f)) :=
    (isZero_cokernel_of_epi (L.map f)).of_iso (PreservesCokernel.iso L f)
  have hpT := punctual_of_zero_on_open Λ j _ hT hf hc hzT
  let S := DerivedCategory.singleFunctor (Modules Λ C) 0
  have ht : heart Λ C (S.obj (cokernel f)) := hGeo.2.2.2.1 _ hpT
  have hz : IsZero ((restriction Λ j).obj (S.obj (cokernel f))) :=
    ((DerivedCategory.singleFunctor (Modules Λ U) 0).map_isZero hzT).of_iso
      ((L.mapDerivedCategorySingleFunctor 0).app (cokernel f))
  have : Mono (ShortComplex.cokernelSequence f).f := inferInstanceAs (Mono f)
  have hS : (ShortComplex.cokernelSequence f).ShortExact :=
    { exact := ShortComplex.cokernelSequence_exact f }
  have hδ : hS.singleδ = 0 := (hmin _ ht hz).1 _
  obtain ⟨s₀, hs₀⟩ := CategoryTheory.Pretriangulated.Triangle.coyoneda_exact₃ _
    hS.singleTriangle_distinguished (𝟙 (S.obj (cokernel f))) (by
      change 𝟙 _ ≫ hS.singleδ = 0
      rw [hδ, comp_zero])
  let s : cokernel f ⟶ A := S.preimage s₀
  have hs : s ≫ cokernel.π f = 𝟙 _ := S.map_injective (by
    rw [S.map_comp, S.map_preimage, S.map_id]
    exact hs₀.symm)
  have : IsSplitMono s := IsSplitMono.mk' ⟨cokernel.π f, hs⟩
  have hzeroT : IsZero (cokernel f) := hA _ s inferInstance hpT
  have : Epi f := Preadditive.epi_of_isZero_cokernel f hzeroT
  exact isIso_of_mono_of_epi f

end OpenImmersion

private theorem minimal_isLE_neg_one (hGeo : CondensedCurve.GeometricAssertions Λ C)
    (P : DerivedCategory (CondensedCurve.Modules Λ C)) (hP : CondensedCurve.heart Λ C P)
    (hmin : CondensedCurve.BoundaryMinimal Λ j P)
    (hZ : IsZero ((CondensedRing.upperStar Λ j).obj
      ((DerivedCategory.homologyFunctor _ 0).obj P))) : P.IsLE (-1) := by
  let t := DerivedCategory.TStructure.t (C := CondensedCurve.Modules Λ C)
  let S := DerivedCategory.singleFunctor (CondensedCurve.Modules Λ C) 0
  let H := DerivedCategory.homologyFunctor (CondensedCurve.Modules Λ C) 0
  let T := (t.truncGE 0).obj P
  let π : P ⟶ T := (t.truncGEπ 0).app P
  have : P.IsLE 0 := (DerivedCategory.isLE_iff P 0).2 hP.2.1.1
  have : T.IsLE 0 := inferInstanceAs (t.IsLE ((t.truncGE 0).obj P) 0)
  have : T.IsGE 0 := inferInstanceAs (t.IsGE ((t.truncGE 0).obj P) 0)
  obtain ⟨B, ⟨e⟩⟩ := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE T 0
  have hπ : IsIso (H.map π) :=
    DerivedCategory.isIso_homologyFunctor_map_truncGEπ_app P 0 0 le_rfl
  let ε : T ≅ S.obj (H.obj P) := e ≪≫ S.mapIso
    (((DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app B).symm ≪≫
      H.mapIso e.symm ≪≫ (asIso (H.map π)).symm)
  have hB : CondensedCurve.heart Λ C (S.obj (H.obj P)) :=
    hGeo.2.2.2.1 _ hP.2.1.2
  have hzB : IsZero ((CondensedCurve.restriction Λ j).obj (S.obj (H.obj P))) :=
    ((DerivedCategory.singleFunctor (CondensedCurve.Modules Λ U) 0).map_isZero hZ).of_iso
      (((CondensedRing.upperStar Λ j).mapDerivedCategorySingleFunctor 0).app (H.obj P))
  have hf : π ≫ ε.hom = 0 := (hmin _ hB hzB).2 _
  have : IsIso (H.map (π ≫ ε.hom)) := by
    rw [H.map_comp]
    infer_instance
  have hH : IsZero (H.obj P) := IsZero.of_mono_eq_zero (H.map (π ≫ ε.hom)) (by
    rw [hf]
    exact H.map_zero _ _)
  exact (DerivedCategory.isLE_iff P (-1)).2 (by
    intro n hn
    by_cases he : n = 0
    · subst n; exact hH
    · exact hP.2.1.1 n (by omega))

private theorem ordinary_boundary_minimal [IsOpenImmersion j]
    (hGeo : GeometricAssertions Λ C)
    (hf : ((j.opensRange : Set C)ᶜ).Finite)
    (hc : ∀ x ∈ (j.opensRange : Set C)ᶜ, IsClosed ({x} : Set C))
    (F : Modules Λ U) : BoundaryMinimal Λ j ((CondensedRing.shiftedOrdinaryImage Λ j).obj F) := by
  intro Q hQ hZ
  obtain ⟨B, e, hB⟩ := boundary_as_single Λ j hGeo hf hc Q hQ hZ
  constructor
  · intro f
    apply (cancel_epi e.inv).1
    simpa only [comp_zero] using ext_zero_of_adjunction
      (CondensedRing.upperStar Λ j) (CondensedRing.lowerStar Λ j)
      (CondensedRing.upperStarLowerStarAdjunction Λ j) F B hB (e.inv ≫ f)
  · intro f
    apply (cancel_mono e.hom).1
    have : ((CondensedRing.shiftedOrdinaryImage Λ j).obj F).IsLE (-1) := by
      change ((DerivedCategory.singleFunctor _ 0).obj
        ((CondensedRing.lowerStar Λ j).obj F)⟦(1 : ℤ)⟧).IsLE (-1)
      exact DerivedCategory.TStructure.t.isLE_shift
        ((DerivedCategory.singleFunctor _ 0).obj ((CondensedRing.lowerStar Λ j).obj F))
        0 1 (-1) (by omega)
    simpa only [zero_comp] using
      (DerivedCategory.TStructure.t (C := Modules Λ C)).zero
        (f ≫ e.hom) (-1) 0 (by omega)

private def shiftedSheafCohomology (X : Scheme.{u}) :
    CondensedRing.shiftedSheaf Λ X ⋙ DerivedCategory.homologyFunctor _ (-1) ≅ 𝟭 _ :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (DerivedCategory.singleFunctor _ 0)
      ((DerivedCategory.homologyFunctor _ 0).shiftIso 1 (-1) 0 (by omega)) ≪≫
    DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0

private theorem noPunctual_of_iso {M N : Modules Λ C} (e : M ≅ N)
    (hN : HasNoPunctualSubsheaf Λ C N) : HasNoPunctualSubsheaf Λ C M := by
  intro B i hi hp
  have : Mono i := hi
  exact hN B (i ≫ e.hom) inferInstance hp

private theorem constructible_closedUnderIsomorphisms
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u}) :
    ObjectProperty.IsClosedUnderIsomorphisms (IsConstantModelConstructible Λ X) := by
  have hloc (Y : Scheme.{u})
      (M N : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))
      (e : M ≅ N) (h : HasFiniteConstantLocalModel Λ Y M) :
      HasFiniteConstantLocalModel Λ Y N := by
    obtain ⟨U, hU⟩ := h
    refine ⟨U, fun i ↦ ?_⟩
    obtain ⟨Q, hQ, ⟨eQ⟩⟩ := hU i
    exact ⟨Q, hQ, ⟨((CondensedRing.upperStar Λ (U.f i)).mapIso e).symm ≪≫ eQ⟩⟩
  have hstrat (Y : Scheme.{u})
      (M N : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))
      (e : M ≅ N) (h : IsFiniteConstantStratified Λ Y M) :
      IsFiniteConstantStratified Λ Y N := by
    obtain ⟨S, hS⟩ := h
    exact ⟨S, fun a ↦ hloc _ _ _
      ((CondensedRing.upperStar Λ (S.immersion a)).mapIso e) (hS a)⟩
  constructor
  intro M N e h
  unfold IsConstantModelConstructible at h ⊢
  split_ifs at h ⊢ with hX
  · exact hstrat _ _ _ e h
  · intro U hU
    exact hstrat _ _ _ ((CondensedRing.upperStar Λ U.ι).mapIso e) (h U hU)

private theorem geometric_setup (D : WeilConjectures.FiniteFieldDatum.{u})
    (ell : ℕ) [Fact ell.Prime]
    (hEll : ell ≠ D.p) (c : Scheme.MiddleExtensionCurve D)
    [GeometricallyConnected c.C.hom] :
    CondensedCurve.GeometricAssertions (Profinite.padicAlgClRingObj ell)
      (D.geometricFiber c.C).left ∧
    DenseRange (WeilConjectures.qbarCurveGeometricOpen D c) ∧
    ((Set.range (WeilConjectures.qbarCurveGeometricOpen D c))ᶜ).Finite ∧
    (∀ x ∈ (Set.range (WeilConjectures.qbarCurveGeometricOpen D c))ᶜ,
      IsClosed ({x} : Set (D.geometricFiber c.C).left)) := by
  have : ConnectedSpace c.C.left :=
    GeometricallyConnected.connectedSpace_of_subsingleton (f := c.C.hom)
  have : IsRegular c.C.left := IsRegular.of_smooth c.C.hom
  have : IrreducibleSpace c.C.left := IsRegular.irreducibleSpace c.C.left
  have hdim₀ : topologicalKrullDim c.C.left = (1 : WithBot ℕ∞) := by
    have h := c.pureDimension Set.univ (by simp only [irreducibleComponents_eq_singleton,
      Set.mem_singleton_iff])
    exact ((Homeomorph.Set.univ c.C.left).isHomeomorph.topologicalKrullDim_eq _).symm.trans h
  let C := D.geometricFiber c.C
  have hSmooth : Smooth C.hom := inferInstanceAs
    (Smooth (pullback.snd c.C.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))
  have hQC : QuasiCompact C.hom := inferInstanceAs
    (QuasiCompact (pullback.snd c.C.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))
  have hSep : IsSeparated C.hom := inferInstanceAs
    (IsSeparated (pullback.snd c.C.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))
  have hGC : GeometricallyConnected C.hom := inferInstanceAs
    (GeometricallyConnected (pullback.snd c.C.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))
  have : ConnectedSpace C.left :=
    GeometricallyConnected.connectedSpace_of_subsingleton (f := C.hom)
  have : IsLocallyNoetherian C.left := LocallyOfFiniteType.isLocallyNoetherian C.hom
  have : IsRegular C.left := IsRegular.of_smooth C.hom
  have : IrreducibleSpace C.left := IsRegular.irreducibleSpace C.left
  have hdim : topologicalKrullDim C.left = (1 : WithBot ℕ∞) :=
    (topologicalKrullDim_pullback_eq_of_field c.C.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).trans hdim₀
  have hPure : C.left.IsPureDimension 1 := by
    intro Z hZ
    have hZeq : Z = Set.univ := by
      simpa only [irreducibleComponents_eq_singleton, Set.mem_singleton_iff] using hZ
    subst Z
    exact (Homeomorph.Set.univ C.left).isHomeomorph.topologicalKrullDim_eq _ |>.trans hdim
  have : Nonempty c.U.left := c.dense.nonempty
  have : Nonempty (D.geometricFiber c.U).left := by
    obtain ⟨x⟩ := ‹Nonempty c.U.left›
    obtain ⟨y⟩ := (inferInstance : Nonempty (Spec (CommRingCat.of D.k)))
    obtain ⟨z, _, _⟩ := Scheme.Pullback.exists_preimage_pullback
      (f := c.U.hom) (g := Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))
      x y (Subsingleton.elim _ _)
    exact ⟨z⟩
  have hj : IsOpenImmersion (WeilConjectures.qbarCurveGeometricOpen D c) := by
    exact MorphismProperty.overPullbackMap (P := @IsOpenImmersion)
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) c.j inferInstance
  have hd : DenseRange (WeilConjectures.qbarCurveGeometricOpen D c) :=
    IsOpenMap.denseRange_of_isPreirreducibleSpace
      (U := (D.geometricFiber c.U).left) (X := C.left) _
      (WeilConjectures.qbarCurveGeometricOpen D c).isOpenMap
  have : IsCurve C.hom := { krullDim_le_one := hdim.le }
  obtain ⟨hf, hc, _⟩ := IsCurve.dense_open_finite_complement C.hom
    (WeilConjectures.qbarCurveGeometricOpen D c).opensRange hd
  let : Fintype D.k₀ := Fintype.ofFinite D.k₀
  let : Fact D.p.Prime := ⟨D.prime⟩
  have hcard : Fintype.card D.k₀ = D.p ^ D.a := by
    simpa only [Nat.card_eq_fintype_card] using D.card_base.trans D.cardinality_eq
  let : CharP D.k₀ D.p := charP_of_card_eq_prime_pow hcard
  let : CharP D.k D.p := charP_of_injective_algebraMap' D.k₀ D.p
  have hunit : IsUnit (ell : D.k) :=
    isUnit_iff_ne_zero.mpr (CharP.cast_ne_zero_of_ne_of_prime D.k (Fact.out) hEll.symm)
  exact ⟨curve_perverse_heart ell D.k hunit C hPure, hd, hf, hc⟩

private theorem modelFrobenius_naturality (D : WeilConjectures.FiniteFieldDatum.{u})
    (c : Scheme.MiddleExtensionCurve D) :
    (CondensedRing.StrictWeil.modelFrobenius D c.U).hom ≫
        WeilConjectures.qbarCurveGeometricOpen D c =
      WeilConjectures.qbarCurveGeometricOpen D c ≫
        (CondensedRing.StrictWeil.modelFrobenius D c.C).hom := by
  apply pullback.hom_ext
  · simp [WeilConjectures.qbarCurveGeometricOpen, CondensedRing.StrictWeil.modelFrobenius,
      WeilConjectures.FiniteFieldDatum.galoisMap, Over.pullback_map_left,
      AlgebraicGeometry.baseChangeMap,
      Category.assoc]
  · simp [WeilConjectures.qbarCurveGeometricOpen, CondensedRing.StrictWeil.modelFrobenius,
      WeilConjectures.FiniteFieldDatum.galoisMap, Over.pullback_map_left,
      AlgebraicGeometry.baseChangeMap,
      Category.assoc]

private def restrictionShiftedSingle :
    CondensedRing.shiftedSheaf Λ C ⋙ restriction Λ j ≅
      CondensedRing.upperStar Λ j ⋙ CondensedRing.shiftedSheaf Λ U :=
  NatIso.ofComponents
    (fun M ↦ ((restriction Λ j).commShiftIso (1 : ℤ)).app
        ((DerivedCategory.singleFunctor _ 0).obj M) ≪≫
      (shiftFunctor _ (1 : ℤ)).mapIso
        (((CondensedRing.upperStar Λ j).mapDerivedCategorySingleFunctor 0).app M))
    (by
      intro M N f
      have h₁ := ((restriction Λ j).commShiftIso (1 : ℤ)).hom.naturality
        ((DerivedCategory.singleFunctor _ 0).map f)
      have h₂ := ((CondensedRing.upperStar Λ j).mapDerivedCategorySingleFunctor 0).hom.naturality f
      dsimp only [Functor.comp_map] at h₁ h₂
      change (restriction Λ j).map
          ((shiftFunctor _ (1 : ℤ)).map ((DerivedCategory.singleFunctor _ 0).map f)) ≫
          ((restriction Λ j).commShiftIso (1 : ℤ)).hom.app
            ((DerivedCategory.singleFunctor _ 0).obj N) ≫
          (shiftFunctor _ (1 : ℤ)).map
            (((CondensedRing.upperStar Λ j).mapDerivedCategorySingleFunctor 0).hom.app N) =
        (((restriction Λ j).commShiftIso (1 : ℤ)).hom.app
            ((DerivedCategory.singleFunctor _ 0).obj M) ≫
          (shiftFunctor _ (1 : ℤ)).map
            (((CondensedRing.upperStar Λ j).mapDerivedCategorySingleFunctor 0).hom.app M)) ≫
          (shiftFunctor _ (1 : ℤ)).map
            ((DerivedCategory.singleFunctor _ 0).map ((CondensedRing.upperStar Λ j).map f))
      rw [← Category.assoc, h₁, Category.assoc, ← Functor.map_comp, h₂, Functor.map_comp]
      simp only [Category.assoc])

private theorem shifted_hom_ext (M : Modules Λ C) (F : Modules Λ U)
    (f g : (CondensedRing.shiftedSheaf Λ C).obj M ⟶
      (CondensedRing.shiftedOrdinaryImage Λ j).obj F)
    (h : (restriction Λ j).map f ≫
        openIdentificationMap Λ j F =
      (restriction Λ j).map g ≫ openIdentificationMap Λ j F) :
    f = g := by
  let S := CondensedRing.shiftedSheaf Λ C
  let T := CondensedRing.shiftedSheaf Λ U
  let L := CondensedRing.upperStar Λ j
  let G := CondensedRing.lowerStar Λ j
  let R := restriction Λ j
  let ρ := restrictionShiftedSingle Λ j
  let a := CondensedRing.upperStarLowerStarAdjunction Λ j
  have : S.Full := inferInstanceAs
    (DerivedCategory.singleFunctor _ 0 ⋙ shiftFunctor _ (1 : ℤ)).Full
  have : S.Faithful := inferInstanceAs
    (DerivedCategory.singleFunctor _ 0 ⋙ shiftFunctor _ (1 : ℤ)).Faithful
  have : T.Faithful := inferInstanceAs
    (DerivedCategory.singleFunctor _ 0 ⋙ shiftFunctor _ (1 : ℤ)).Faithful
  obtain ⟨f', rfl⟩ := S.map_surjective f
  obtain ⟨g', rfl⟩ := S.map_surjective g
  have hρ : openIdentificationMap Λ j F =
      ρ.hom.app (G.obj F) ≫ T.map (a.counit.app F) := by
    dsimp only [ρ, G, T, a, restrictionShiftedSingle, NatIso.ofComponents]
    simp only [openIdentificationMap, Iso.trans_hom,
      Functor.mapIso_hom, Iso.app_hom, Category.assoc]
  rw [hρ] at h
  have hf := ρ.hom.naturality f'
  have hg := ρ.hom.naturality g'
  dsimp only [Functor.comp_map] at hf hg
  have h' : ρ.hom.app M ≫ T.map (L.map f' ≫ a.counit.app F) =
      ρ.hom.app M ≫ T.map (L.map g' ≫ a.counit.app F) := by
    change R.map (S.map f') ≫ _ = R.map (S.map g') ≫ _ at h
    calc
      _ = R.map (S.map f') ≫ ρ.hom.app (G.obj F) ≫ T.map (a.counit.app F) := by
        simpa only [T.map_comp, Category.assoc] using
          (congrArg (fun z ↦ z ≫ T.map (a.counit.app F)) hf).symm
      _ = R.map (S.map g') ≫ ρ.hom.app (G.obj F) ≫ T.map (a.counit.app F) := h
      _ = _ := by
        simpa only [T.map_comp, Category.assoc] using
          congrArg (fun z ↦ z ≫ T.map (a.counit.app F)) hg
  have ha : L.map f' ≫ a.counit.app F = L.map g' ≫ a.counit.app F :=
    T.map_injective ((cancel_epi (ρ.hom.app M)).1 h')
  have he : f' = g' := (a.homEquiv _ _).symm.injective (by
    simpa only [Adjunction.homEquiv_counit] using ha)
  exact congrArg S.map he

private theorem shifted_hom_surjective (M : Modules Λ C)
    (F : Modules Λ U)
    (a₀ : (restriction Λ j).obj ((CondensedRing.shiftedSheaf Λ C).obj M) ⟶
      (CondensedRing.shiftedSheaf Λ U).obj F) :
    ∃ f : (CondensedRing.shiftedSheaf Λ C).obj M ⟶
      (CondensedRing.shiftedOrdinaryImage Λ j).obj F,
      (restriction Λ j).map f ≫
        openIdentificationMap Λ j F = a₀ := by
  let S := CondensedRing.shiftedSheaf Λ C
  let T := CondensedRing.shiftedSheaf Λ U
  let L := CondensedRing.upperStar Λ j
  let G := CondensedRing.lowerStar Λ j
  let R := restriction Λ j
  let ρ := restrictionShiftedSingle Λ j
  let a := CondensedRing.upperStarLowerStarAdjunction Λ j
  have : T.Full := inferInstanceAs
    (DerivedCategory.singleFunctor _ 0 ⋙ shiftFunctor _ (1 : ℤ)).Full
  obtain ⟨b, hb⟩ := T.map_surjective (ρ.inv.app M ≫ a₀)
  let f := a.homEquiv M F b
  refine ⟨S.map f, ?_⟩
  have hρ : openIdentificationMap Λ j F =
      ρ.hom.app (G.obj F) ≫ T.map (a.counit.app F) := by
    dsimp only [ρ, G, T, a, restrictionShiftedSingle, NatIso.ofComponents]
    simp only [openIdentificationMap, Iso.trans_hom,
      Functor.mapIso_hom, Iso.app_hom, Category.assoc]
  rw [hρ]
  have hn := ρ.hom.naturality f
  dsimp only [Functor.comp_map] at hn
  calc
    R.map (S.map f) ≫ ρ.hom.app (G.obj F) ≫ T.map (a.counit.app F) =
        ρ.hom.app M ≫ T.map (L.map f ≫ a.counit.app F) := by
      simpa only [T.map_comp, Category.assoc] using
        congrArg (fun z ↦ z ≫ T.map (a.counit.app F)) hn
    _ = ρ.hom.app M ≫ T.map b := by
      congr 2
      exact (a.homEquiv_counit M F f).symm.trans ((a.homEquiv _ _).symm_apply_apply b)
    _ = a₀ := by rw [hb]; simp only [Iso.hom_inv_id_app_assoc]

private theorem normalized_iso_of_nonempty_iso (F : Modules Λ U)
    [IsIso (openIdentificationMap Λ j F)]
    (P : DerivedCategory (Modules Λ C))
    (e₀ : P ≅ (CondensedRing.shiftedOrdinaryImage Λ j).obj F)
    (α : (restriction Λ j).obj P ≅ (CondensedRing.shiftedSheaf Λ U).obj F) :
    ∃! e : P ≅ (CondensedRing.shiftedOrdinaryImage Λ j).obj F,
      (restriction Λ j).map e.hom ≫
        openIdentificationMap Λ j F = α.hom := by
  let R := restriction Λ j
  let A := (CondensedRing.shiftedOrdinaryImage Λ j).obj F
  let β := asIso (openIdentificationMap Λ j F)
  have hinj {f g : A ⟶ A} (h : R.map f = R.map g) : f = g :=
    shifted_hom_ext Λ j _ F f g (by rw [h])
  have hsurj (g : R.obj A ⟶ R.obj A) : ∃ f : A ⟶ A, R.map f = g := by
    obtain ⟨f, hf⟩ := shifted_hom_surjective Λ j _ F (g ≫ β.hom)
    exact ⟨f, (cancel_mono β.hom).1 hf⟩
  let γ : R.obj A ≅ R.obj A := R.mapIso e₀.symm ≪≫ α ≪≫ β.symm
  obtain ⟨f, hf⟩ := hsurj γ.hom
  obtain ⟨g, hg⟩ := hsurj γ.inv
  have hfg : f ≫ g = 𝟙 A := hinj (by simp only [R.map_comp, hf, hg,
    Iso.hom_inv_id, R.map_id])
  have hgf : g ≫ f = 𝟙 A := hinj (by simp only [R.map_comp, hf, hg,
    Iso.inv_hom_id, R.map_id])
  have : IsIso f := ⟨⟨g, hfg, hgf⟩⟩
  let e : P ≅ A := e₀ ≪≫ asIso f
  have he : R.map e.hom ≫ β.hom = α.hom := by
    simp [e, R.map_comp, hf, γ, Category.assoc]
  refine ⟨e, he, ?_⟩
  intro e' he'
  apply Iso.ext
  apply (cancel_epi e₀.inv).1
  apply shifted_hom_ext Λ j _ F
  change R.map (e₀.inv ≫ e'.hom) ≫ β.hom = R.map (e₀.inv ≫ e.hom) ≫ β.hom
  change R.map e'.hom ≫ β.hom = α.hom at he'
  simpa only [R.map_comp, Category.assoc] using
    congrArg (fun z ↦ R.map e₀.inv ≫ z) (he'.trans he.symm)

private theorem minimal_has_iso [IsOpenImmersion j]
    (hGeo : GeometricAssertions Λ C)
    (hf : ((j.opensRange : Set C)ᶜ).Finite)
    (hc : ∀ x ∈ (j.opensRange : Set C)ᶜ, IsClosed ({x} : Set C))
    [ObjectProperty.IsClosedUnderIsomorphisms (IsConstantModelConstructible Λ C)]
    [ObjectProperty.IsClosedUnderKernels (IsConstantModelConstructible Λ C)]
    [ObjectProperty.IsClosedUnderCokernels (IsConstantModelConstructible Λ C)]
    (F : Modules Λ U)
    (hA : heart Λ C ((CondensedRing.shiftedOrdinaryImage Λ j).obj F))
    (P : DerivedCategory (Modules Λ C)) (hP : heart Λ C P)
    (hMin : BoundaryMinimal Λ j P)
    (α : (restriction Λ j).obj P ≅ (CondensedRing.shiftedSheaf Λ U).obj F) :
    Nonempty (P ≅ (CondensedRing.shiftedOrdinaryImage Λ j).obj F) := by
  let L := CondensedRing.upperStar Λ j
  let G := CondensedRing.lowerStar Λ j
  let S := CondensedRing.shiftedSheaf Λ C
  let T := CondensedRing.shiftedSheaf Λ U
  let R := restriction Λ j
  let H := DerivedCategory.homologyFunctor (Modules Λ C) (-1)
  let H₀ := DerivedCategory.homologyFunctor (Modules Λ U) 0
  have hTF : (T.obj F).IsLE (-1) := by
    change ((DerivedCategory.singleFunctor _ 0).obj F⟦(1 : ℤ)⟧).IsLE (-1)
    exact DerivedCategory.TStructure.t.isLE_shift
      ((DerivedCategory.singleFunctor _ 0).obj F) 0 1 (-1) (by omega)
  have hZ : IsZero (L.obj ((DerivedCategory.homologyFunctor _ 0).obj P)) :=
    (DerivedCategory.isZero_of_isLE (T.obj F) (-1) 0 (by omega)).of_iso
      ((L.mapDerivedCategoryHomologyFunctorIso 0).app P ≪≫ H₀.mapIso α)
  have : P.IsLE (-1) := minimal_isLE_neg_one Λ j hGeo P hP hMin hZ
  have : P.IsGE (-1) := (DerivedCategory.isGE_iff P (-1)).2 hP.2.2.1
  obtain ⟨M, ⟨e₀⟩⟩ := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE P (-1)
  let e : P ≅ S.obj M := e₀ ≪≫
    ((DerivedCategory.singleFunctors (Modules Λ C)).shiftIso 1 (-1) 0 (by omega)).symm.app M
  let χP : H.obj P ≅ M := H.mapIso e ≪≫ (shiftedSheafCohomology Λ C).app M
  let χA : H.obj (S.obj (G.obj F)) ≅ G.obj F :=
    (shiftedSheafCohomology Λ C).app (G.obj F)
  have hM : IsConstantModelConstructible Λ C M :=
    ObjectProperty.prop_of_iso (IsConstantModelConstructible Λ C) χP (hP.1.2 (-1))
  have hGF : IsConstantModelConstructible Λ C (G.obj F) :=
    ObjectProperty.prop_of_iso (IsConstantModelConstructible Λ C) χA (hA.1.2 (-1))
  have hnM : HasNoPunctualSubsheaf Λ C M := noPunctual_of_iso Λ χP.symm hP.2.2.2
  have hnA : HasNoPunctualSubsheaf Λ C (G.obj F) := noPunctual_of_iso Λ χA.symm hA.2.2.2
  let ρ := restrictionShiftedSingle Λ j
  let αM : R.obj (S.obj M) ≅ T.obj F := R.mapIso e.symm ≪≫ α
  have : T.Full := inferInstanceAs
    (DerivedCategory.singleFunctor _ 0 ⋙ shiftFunctor _ (1 : ℤ)).Full
  have : T.Faithful := inferInstanceAs
    (DerivedCategory.singleFunctor _ 0 ⋙ shiftFunctor _ (1 : ℤ)).Faithful
  let b : L.obj M ⟶ F := T.preimage (ρ.inv.app M ≫ αM.hom)
  have hb : T.map b = ρ.inv.app M ≫ αM.hom := T.map_preimage _
  have : IsIso (T.map b) := by rw [hb]; infer_instance
  have : IsIso b := isIso_of_reflects_iso b T
  let adj := CondensedRing.upperStarLowerStarAdjunction Λ j
  let f : M ⟶ G.obj F := adj.homEquiv M F b
  have hfb : L.map f ≫ adj.counit.app F = b := by
    exact (adj.homEquiv_counit M F f).symm.trans ((adj.homEquiv _ _).symm_apply_apply b)
  have ff := openDirectImageFullyFaithful Λ j
  have := ff.full
  have := ff.faithful
  have : IsIso (adj.counit.app F) := inferInstance
  have : IsIso (L.map f) := by
    have : IsIso (L.map f ≫ adj.counit.app F) := by rw [hfb]; infer_instance
    exact IsIso.of_isIso_comp_right _ (adj.counit.app F)
  have hminM : BoundaryMinimal Λ j (S.obj M) := boundaryMinimal_of_iso Λ j e.symm hMin
  have : IsIso f := isIso_of_minimal_kernel_cokernel Λ j hGeo hf hc f
    (ObjectProperty.prop_kernel (IsConstantModelConstructible Λ C) f hM hGF)
    (ObjectProperty.prop_cokernel (IsConstantModelConstructible Λ C) f hM hGF) hnM hnA hminM
  exact ⟨e ≪≫ S.mapIso (asIso f)⟩

private theorem assertion_of_geometric [IsOpenImmersion j]
    [ObjectProperty.IsClosedUnderKernels (IsConstantModelConstructible Λ C)]
    [ObjectProperty.IsClosedUnderCokernels (IsConstantModelConstructible Λ C)]
    (hGeo : GeometricAssertions Λ C)
    (hf : ((j.opensRange : Set C)ᶜ).Finite)
    (hc : ∀ x ∈ (j.opensRange : Set C)ᶜ, IsClosed ({x} : Set C))
    (gU : U ≅ U) (gC : C ≅ C) (w : gU.hom ≫ j = j ≫ gC.hom)
    (F : CondensedRing.StrictWeil.WeilModule Λ gU)
    (hA : heart Λ C ((CondensedRing.shiftedOrdinaryImage Λ j).obj F.carrier))
    (θ₀ : (CondensedRing.StrictWeil.action Λ gC).obj
      ((CondensedRing.shiftedOrdinaryImage Λ j).obj F.carrier) ≅
        (CondensedRing.shiftedOrdinaryImage Λ j).obj F.carrier) :
    IntermediateExtensionAssertion Λ j gU gC w F := by
  let A := (CondensedRing.shiftedOrdinaryImage Λ j).obj F.carrier
  let R := restriction Λ j
  let HC := CondensedRing.StrictWeil.action Λ gC
  let HU := CondensedRing.StrictWeil.action Λ gU
  let r := restrictionFrobeniusComparison Λ j gU gC w
  have : ObjectProperty.IsClosedUnderIsomorphisms (IsConstantModelConstructible Λ C) :=
    constructible_closedUnderIsomorphisms Λ C
  have : IsIso (openIdentificationMap Λ j F.carrier) := openIdentification_isIso Λ j F.carrier
  let β := asIso (openIdentificationMap Λ j F.carrier)
  have hMin : BoundaryMinimal Λ j A := ordinary_boundary_minimal Λ j hGeo hf hc F.carrier
  have hUnique (P : DerivedCategory (Modules Λ C)) (hP : heart Λ C P)
      (hmin : BoundaryMinimal Λ j P)
      (α : R.obj P ≅ (CondensedRing.shiftedSheaf Λ U).obj F.carrier) :
      ∃! e : P ≅ A, R.map e.hom ≫ β.hom = α.hom := by
    obtain ⟨e₀⟩ := minimal_has_iso Λ j hGeo hf hc F.carrier hA P hP hmin α
    exact normalized_iso_of_nonempty_iso Λ j F.carrier P e₀ α
  have : IsIso (shiftedWeilMap Λ gU F) := by unfold shiftedWeilMap; infer_instance
  let αA : R.obj (HC.obj A) ≅ (CondensedRing.shiftedSheaf Λ U).obj F.carrier :=
    (r.app A).symm ≪≫ HU.mapIso β ≪≫ asIso (shiftedWeilMap Λ gU F)
  obtain ⟨θA, hθA, _⟩ := normalized_iso_of_nonempty_iso Λ j F.carrier (HC.obj A) θ₀ αA
  have hθ : r.hom.app A ≫ R.map θA.hom ≫ β.hom =
      HU.map β.hom ≫ shiftedWeilMap Λ gU F := by
    change R.map θA.hom ≫ β.hom = αA.hom at hθA
    rw [hθA]
    simp only [αA, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, asIso_hom,
      Iso.app_inv, Iso.hom_inv_id_app_assoc]
  refine ⟨hA, β, rfl, hMin, ?_, θA, hθ, ?_⟩
  · intro P hP α
    constructor
    · exact fun hmin ↦ hUnique P hP hmin α
    · rintro ⟨e, _, _⟩
      exact boundaryMinimal_of_iso Λ j e hMin
  · intro P hP hmin α θP e he hθP
    have hu : ∀ e' : P ≅ A, R.map e'.hom ≫ β.hom = α.hom → e' = e := by
      obtain ⟨e₁, h₁, huniq⟩ := hUnique P hP hmin α
      intro e' he'
      exact (huniq e' he').trans (huniq e he).symm
    exact equivariance_of_unique_iso R HC HU r α β (shiftedWeilMap Λ gU F)
      e he hu θP θA hθP hθ

private theorem shifted_iso_of_sheaf_iso (gC : C ≅ C) (M N : Modules Λ C)
    (ψ : (CondensedRing.upperStar Λ gC.hom).obj M ≅ N) :
    Nonempty ((CondensedRing.StrictWeil.action Λ gC).obj
      ((CondensedRing.shiftedSheaf Λ C).obj M) ≅ (CondensedRing.shiftedSheaf Λ C).obj N) :=
  ⟨(restrictionShiftedSingle Λ gC.hom).app M ≪≫
    (CondensedRing.shiftedSheaf Λ C).mapIso ψ⟩

private theorem ordinary_weil_iso_from_comparison (gU : U ≅ U) (gC : C ≅ C)
    (F : CondensedRing.StrictWeil.WeilModule Λ gU)
    (e : CondensedRing.lowerStar Λ j ⋙ CondensedRing.upperStar Λ gC.hom ≅
      CondensedRing.upperStar Λ gU.hom ⋙ CondensedRing.lowerStar Λ j) :
    Nonempty ((CondensedRing.StrictWeil.action Λ gC).obj
      ((CondensedRing.shiftedOrdinaryImage Λ j).obj F.carrier) ≅
        (CondensedRing.shiftedOrdinaryImage Λ j).obj F.carrier) := by
  let ψ := e.app F.carrier ≪≫ (CondensedRing.lowerStar Λ j).mapIso F.str
  exact shifted_iso_of_sheaf_iso Λ gC _ _ ψ

private theorem ordinary_weil_iso (ell : ℕ) [Fact ell.Prime]
    {U C : Scheme.{u}} (j : U ⟶ C) (gU : U ≅ U) (gC : C ≅ C)
    (w : gU.hom ≫ j = j ≫ gC.hom)
    (F : CondensedRing.StrictWeil.WeilModule (Profinite.padicAlgClRingObj ell) gU) :
    Nonempty ((CondensedRing.StrictWeil.action (Profinite.padicAlgClRingObj ell) gC).obj
      ((CondensedRing.shiftedOrdinaryImage (Profinite.padicAlgClRingObj ell) j).obj F.carrier) ≅
        (CondensedRing.shiftedOrdinaryImage (Profinite.padicAlgClRingObj ell) j).obj
          F.carrier) := by
  have : IsIso (CurveRestriction.pushSquare ell j gU gC w) :=
    (CurveRestriction.automorphism_calculus ell j gU gC w).1
  exact ordinary_weil_iso_from_comparison (Profinite.padicAlgClRingObj ell) j gU gC F
    (asIso (CurveRestriction.pushSquare ell j gU gC w))

private theorem padic_constructible_closure (ell : ℕ) [Fact ell.Prime]
    (X : Scheme.{u}) [IsNoetherian X] :
    ObjectProperty.IsClosedUnderKernels
      (IsConstantModelConstructible (Profinite.padicAlgClRingObj ell) X) ∧
    ObjectProperty.IsClosedUnderCokernels
      (IsConstantModelConstructible (Profinite.padicAlgClRingObj ell) X) := by
  have h := (coefficientHeart_closure ell (Profinite.padicAlgClCondensedRing ell)
    (Or.inr rfl)).2 X
  exact ⟨h.1, h.2.1⟩

/-- The ordinary condensed direct image shifted by one is the perverse intermediate
extension of the lisse Weil sheaf, uniquely over the open and with its induced Weil structure.
Source: literature/blueprint/latest/blueprint/sec-deligne-laumon-a1/
sk-lem-wft-curve-heart/rem-dl-a1-conventions.md, ordinary direct-image sentence
(blueprint: lem-dl-a1-condensed-curve-intermediate-extension).

Proof, following the eight DAG steps:
1. Smoothness, geometric connectedness and field-extension dimension invariance give
   a pure geometric curve. The geometric open is dense with finite closed complement.
   The curve-heart theorem gives perversity, and the open sheaf counit gives restriction.
2. For a boundary perverse Q, H^-1(Q) is punctual and has no punctual subsheaf, so is zero.
   The standard amplitude characterization identifies Q with a sheaf B in degree zero.
3. Represent B → (j_*F)[1] by a short exact extension using degree-one Ext classification.
   Ordinary sheaf adjunction retracts its first arrow, so its connecting map is zero.
4. The reverse boundary Hom vanishes by standard t-structure orthogonality.
5. Minimality kills the truncation projection of another extension P onto H^0(P)[0].
   Its H^0 is invertible, so H^0(P) vanishes and P is a sheaf M shifted by one.
6. The adjoint M → j_*F has punctual kernel and cokernel. The kernel vanishes by the
   lower heart condition. Minimality kills the cokernel's connecting map, so the
   extension splits. The cokernel is then a punctual subsheaf of j_*F, hence zero.
7. Shifted single complexes are fully faithful. The sheaf adjunction therefore gives
   the precise open Hom bijection; it normalizes the isomorphism uniquely over the open.
8. The ordinary automorphism comparison gives an initial Frobenius isomorphism. Normalize
   its restriction by the same Hom bijection. Conjugation by the two Weil structures
   preserves a comparison's normalization, so uniqueness proves equivariance.
No triangulated structure on strict Weil pairs or exactness of ordinary j_* is used. -/
theorem condensed_curve_intermediate_extension
    (D : WeilConjectures.FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime]
    (_hEll : ell ≠ D.p) (c : Scheme.MiddleExtensionCurve D)
    [GeometricallyConnected c.C.hom]
    (F : CondensedRing.StrictWeil.WeilModule (Profinite.padicAlgClRingObj ell)
      (CondensedRing.StrictWeil.modelFrobenius D c.U))
    (_hCons : IsConstantModelConstructible (Profinite.padicAlgClRingObj ell)
      (D.geometricFiber c.U).left F.carrier)
    (_hLisse : IsLisseCoefficientModule (Profinite.padicAlgClRingObj ell) F.carrier) :
    ∃ w : (CondensedRing.StrictWeil.modelFrobenius D c.U).hom ≫
          WeilConjectures.qbarCurveGeometricOpen D c =
        WeilConjectures.qbarCurveGeometricOpen D c ≫
          (CondensedRing.StrictWeil.modelFrobenius D c.C).hom,
      IntermediateExtensionAssertion (Profinite.padicAlgClRingObj ell)
        (WeilConjectures.qbarCurveGeometricOpen D c)
        (CondensedRing.StrictWeil.modelFrobenius D c.U)
        (CondensedRing.StrictWeil.modelFrobenius D c.C) w F := by
  let Λ := Profinite.padicAlgClRingObj ell
  let C := D.geometricFiber c.C
  let j := WeilConjectures.qbarCurveGeometricOpen D c
  have : IsOpenImmersion j := MorphismProperty.overPullbackMap (P := @IsOpenImmersion)
    (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) c.j inferInstance
  have : Smooth C.hom := inferInstanceAs
    (Smooth (pullback.snd c.C.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))
  have : QuasiCompact C.hom := inferInstanceAs
    (QuasiCompact (pullback.snd c.C.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))
  have : IsLocallyNoetherian C.left := LocallyOfFiniteType.isLocallyNoetherian C.hom
  have : CompactSpace C.left := QuasiCompact.compactSpace_of_compactSpace C.hom
  have hN : IsNoetherian C.left := {}
  have : IsNoetherian (D.geometricFiber c.C).left := hN
  obtain ⟨hGeo, hd, hf, hc⟩ := geometric_setup D ell _hEll c
  let w := modelFrobenius_naturality D c
  have hcl := padic_constructible_closure ell C.left
  obtain ⟨θ₀⟩ := ordinary_weil_iso ell j
    (CondensedRing.StrictWeil.modelFrobenius D c.U)
    (CondensedRing.StrictWeil.modelFrobenius D c.C) w F
  exact ⟨w, @assertion_of_geometric Λ _ _ _ _ j _ hcl.1 hcl.2 hGeo hf hc
    (CondensedRing.StrictWeil.modelFrobenius D c.U)
    (CondensedRing.StrictWeil.modelFrobenius D c.C) w F
    (hGeo.2.2.2.2 _ j inferInstance hd F.carrier _hLisse) θ₀⟩

end AlgebraicGeometry.ProEtale.CondensedCurve
