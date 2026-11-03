/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CoefficientScalarRepresentatives.CoefficientScalarRepresentatives
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.RestrictScalars
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarRestrictScalars
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.OpenCover
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Stalk
public import WeilConjectures.AlgebraicGeometry.ProEtale.Extension.ProEtaleExtensionZeroComparison
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.CategoryTheory.Derived.DerivedExactSquareComposition
import WeilConjectures.AlgebraicGeometry.Etale.Open.EtaleOpenTensor
import WeilConjectures.SixFunctors.ProEtale.Comparison.Flat
import WeilConjectures.AlgebraicGeometry.Etale.Constant.EtaleConstantModuleFlat
import all WeilConjectures.AlgebraicGeometry.ProEtale.Extension.ProEtaleExtensionZeroComparison
import all WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedEtaleCompactSupportComparisonsSupplement
import all WeilConjectures.AlgebraicGeometry.Comparison.ComparisonOpenTensorCoherence

/-! # Open extension/scalar/site coherence (current ordinary model)

Source: Stacks Project, `sites-cohomology.tex`, Tags 06YQ, 0GL1 and 09AF;
blueprint `lem-sp-open-scalar-site-coherence`.

The scalar functors and their normalization are those of the current ordinary
coefficient interfaces, fixed by the actual exact restriction adjunctions.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor CategoryTheory.TwoSquare

namespace AlgebraicGeometry.ProEtale.OpenScalarSiteCoherence

private lemma pro_derived_comp_conjugate
    (A : Type (u + 1)) [CommRing A]
    {X Y Z : Scheme.{u}}
    (j₁ : X ⟶ Y) (j₂ : Y ⟶ Z) [IsOpenImmersion j₁] [IsOpenImmersion j₂] :
    let B := ModuleCat.{u + 1} A
    conjugateEquiv
      ((openImmersionLowerShriekUpperStarAdjunction B j₁
        ).mapDerivedCategoryAdjunction.comp
        (openImmersionLowerShriekUpperStarAdjunction B j₂
          ).mapDerivedCategoryAdjunction)
      (openImmersionLowerShriekUpperStarAdjunction B (j₁ ≫ j₂)
        ).mapDerivedCategoryAdjunction
      (Functor.mapDerivedCategoryTriangleIso
        (proEtaleOpenExtensionComp A j₁ j₂)).hom =
      (Functor.mapDerivedCategoryTriangleIso
        (upperStarComp B j₁ j₂)).inv := by
  let B := ModuleCat.{u + 1} A
  let a := openImmersionLowerShriekUpperStarAdjunction B j₁
  let b := openImmersionLowerShriekUpperStarAdjunction B j₂
  let c := openImmersionLowerShriekUpperStarAdjunction B (j₁ ≫ j₂)
  let e := proEtaleOpenExtensionComp A j₁ j₂
  let r := upperStarComp B j₁ j₂
  have hu (K : Sheaf (Scheme.ProEt.topology X) B) :
      c.unit.app K ≫ (upperStar B (j₁ ≫ j₂)).map (e.hom.app K) =
        (a.comp b).unit.app K ≫ r.inv.app
          (((openImmersionLowerShriek B j₁) ⋙ (openImmersionLowerShriek B j₂)).obj K) := by
    exact Adjunction.unit_leftAdjointUniq_hom_app c ((a.comp b).ofNatIsoRight r.symm) K
  have hd := Etale.exact_adj_conjugate
    (C := Sheaf (Scheme.ProEt.topology X) B) (D := Sheaf (Scheme.ProEt.topology Z) B)
    c (a.comp b) e r.symm hu
  rw [Etale.exact_adj_comp (C := Sheaf (Scheme.ProEt.topology X) B)
    (D := Sheaf (Scheme.ProEt.topology Y) B) (E := Sheaf (Scheme.ProEt.topology Z) B) a b] at hd
  apply conjugateEquiv_eq_of_unit
  intro K
  have hK := congrArg (fun t ↦ t.app K) hd
  simp only [Adjunction.ofNatIsoRight_unit, Adjunction.ofNatIsoLeft_unit,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Iso.symm_hom, Adjunction.comp_unit_app,
    Functor.mapDerivedCategoryNatIso_symm] at hK
  let L₁ := openImmersionLowerShriek B j₁
  let L₂ := openImmersionLowerShriek B j₂
  let R := upperStar B (j₁ ≫ j₂)
  let R₁ := upperStar B j₁
  let R₂ := upperStar B j₂
  have hk := congrArg (fun t ↦ t ≫ R.mapDerivedCategory.map
    ((Functor.mapDerivedCategoryCompIso L₁ L₂).hom.app K)) hK
  simp only [Category.assoc] at hk
  have hn := (Functor.mapDerivedCategoryTriangleIso r).inv.naturality
    ((Functor.mapDerivedCategoryCompIso L₁ L₂).hom.app K)
  simp only [Functor.comp_map] at hn
  simp only [Functor.mapDerivedCategoryTriangleIso, Iso.trans_inv,
    NatTrans.comp_app, Category.assoc] at hn
  erw [← hn] at hk
  erw [← (R₂.mapDerivedCategory ⋙ R₁.mapDerivedCategory).map_comp_assoc,
    Iso.inv_hom_id_app, CategoryTheory.Functor.map_id, Category.id_comp] at hk
  simpa only [Functor.mapDerivedCategoryTriangleIso, Iso.trans_hom, Iso.trans_inv,
    NatTrans.comp_app, Functor.map_comp, Adjunction.comp_unit_app,
    a, b, c, e, r, L₁, L₂, R, R₁, R₂, Category.assoc] using hk.symm


private abbrev proRestrictionSquare
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {U X : Scheme.{u}} (j : U ⟶ X) :=
  (upperStarRestrictScalarsIso φ j).symm

private abbrev etRestrictionSquare
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {U X : Scheme.{u}} (j : U ⟶ X) :=
  (Etale.upperStarRestrictScalarsIso φ j).symm

private theorem pro_restrict_comp {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {V U X : Scheme.{u}} (k : V ⟶ U) (j : U ⟶ X)
    [IsOpenImmersion k] [IsOpenImmersion j]
    (M : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} B)) :
    (Sheaf.restrictScalars (Scheme.ProEt.topology V) φ).map
        ((upperStarComp (ModuleCat.{u + 1} B) k j).hom.app M) ≫
      (proRestrictionSquare φ k).hom.app ((upperStar (ModuleCat.{u + 1} B) j).obj M) ≫
      (upperStar (ModuleCat.{u + 1} A) k).map ((proRestrictionSquare φ j).hom.app M) =
    (proRestrictionSquare φ (k ≫ j)).hom.app M ≫
      (upperStarComp (ModuleCat.{u + 1} A) k j).hom.app
        ((Sheaf.restrictScalars (Scheme.ProEt.topology X) φ).obj M) := by
  have h := congr_app (upperStarRestrictScalarsIso_comp_hom φ k j) M
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id] at h
  apply (cancel_epi ((upperStarRestrictScalarsIso φ (k ≫ j)).hom.app M)).mp
  simp only [proRestrictionSquare, Iso.symm_hom]
  rw [← Category.assoc, ← Category.assoc, h]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc, Iso.hom_inv_id_app]
  erw [Category.id_comp]
  rw [← Functor.map_comp, Iso.hom_inv_id_app]
  simp only [CategoryTheory.Functor.map_id]
  erw [Category.comp_id]

private theorem pro_derived_restrict_comp {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {V U X : Scheme.{u}} (k : V ⟶ U) (j : U ⟶ X)
    [IsOpenImmersion k] [IsOpenImmersion j]
    (hq : ∀ M : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} B),
      (Sheaf.restrictScalars (Scheme.ProEt.topology V) φ).map
          ((upperStarComp (ModuleCat.{u + 1} B) k j).hom.app M) ≫
        (proRestrictionSquare φ k).hom.app ((upperStar (ModuleCat.{u + 1} B) j).obj M) ≫
        (upperStar (ModuleCat.{u + 1} A) k).map ((proRestrictionSquare φ j).hom.app M) =
      (proRestrictionSquare φ (k ≫ j)).hom.app M ≫
        (upperStarComp (ModuleCat.{u + 1} A) k j).hom.app
          ((Sheaf.restrictScalars (Scheme.ProEt.topology X) φ).obj M)) :
    let RA (T : Scheme.{u}) := Sheaf.derivedRestrictScalars (Scheme.ProEt.topology T) φ
    let UB {S T : Scheme.{u}} (f : S ⟶ T) := (upperStar (ModuleCat.{u + 1} B) f).mapDerivedCategory
    let UA {S T : Scheme.{u}} (f : S ⟶ T) := (upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory
    let β := Functor.mapDerivedCategoryNatIso (upperStarComp (ModuleCat.{u + 1} A) k j) ≪≫
      Functor.mapDerivedCategoryCompIso _ _
    let γ := Functor.mapDerivedCategoryNatIso (upperStarComp (ModuleCat.{u + 1} B) k j) ≪≫
      Functor.mapDerivedCategoryCompIso _ _
    Functor.mapDerivedCategorySquareIso (proRestrictionSquare φ (k ≫ j)) =
      Functor.isoWhiskerRight γ (RA V) ≪≫
      Functor.associator (UB j) (UB k) (RA V) ≪≫
      Functor.isoWhiskerLeft (UB j)
        (Functor.mapDerivedCategorySquareIso (proRestrictionSquare φ k)) ≪≫
      (Functor.associator (UB j) (RA U) (UA k)).symm ≪≫
      Functor.isoWhiskerRight
        (Functor.mapDerivedCategorySquareIso (proRestrictionSquare φ j)) (UA k) ≪≫
      Functor.associator (RA X) (UA j) (UA k) ≪≫
      Functor.isoWhiskerLeft (RA X) β.symm := by
  dsimp only
  apply Iso.ext
  ext K
  have hc :
      (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology V) φ).map
          ((Functor.mapDerivedCategoryNatIso (upperStarComp (ModuleCat.{u + 1} B) k j) ≪≫
            Functor.mapDerivedCategoryCompIso _ _).hom.app K) ≫
        (Functor.mapDerivedCategorySquareIso (proRestrictionSquare φ k)).hom.app
          ((upperStar (ModuleCat.{u + 1} B) j).mapDerivedCategory.obj K) ≫
        (upperStar (ModuleCat.{u + 1} A) k).mapDerivedCategory.map
          ((Functor.mapDerivedCategorySquareIso (proRestrictionSquare φ j)).hom.app K) =
      (Functor.mapDerivedCategorySquareIso (proRestrictionSquare φ (k ≫ j))).hom.app K ≫
        (Functor.mapDerivedCategoryNatIso (upperStarComp (ModuleCat.{u + 1} A) k j) ≪≫
          Functor.mapDerivedCategoryCompIso _ _).hom.app
            ((Sheaf.derivedRestrictScalars (Scheme.ProEt.topology X) φ).obj K) := by
    simpa only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
      Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Functor.associator_hom_app, Functor.associator_inv_app,
      Category.id_comp, Category.comp_id] using congrArg (fun e ↦ e.hom.app K)
      (Functor.mapDerivedCategorySquareIso_comp
        (C₀ := Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} B))
        (C₁ := Sheaf (Scheme.ProEt.topology U) (ModuleCat.{u + 1} B))
        (C₂ := Sheaf (Scheme.ProEt.topology V) (ModuleCat.{u + 1} B))
        (D₀ := Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))
        (D₁ := Sheaf (Scheme.ProEt.topology U) (ModuleCat.{u + 1} A))
        (D₂ := Sheaf (Scheme.ProEt.topology V) (ModuleCat.{u + 1} A))
        (upperStar (ModuleCat.{u + 1} B) j) (upperStar (ModuleCat.{u + 1} B) k)
        (upperStar (ModuleCat.{u + 1} B) (k ≫ j))
        (upperStar (ModuleCat.{u + 1} A) j) (upperStar (ModuleCat.{u + 1} A) k)
        (upperStar (ModuleCat.{u + 1} A) (k ≫ j))
        (Sheaf.restrictScalars (Scheme.ProEt.topology X) φ)
        (Sheaf.restrictScalars (Scheme.ProEt.topology U) φ)
        (Sheaf.restrictScalars (Scheme.ProEt.topology V) φ)
        (proRestrictionSquare φ j) (proRestrictionSquare φ k)
        (proRestrictionSquare φ (k ≫ j))
        (upperStarComp (ModuleCat.{u + 1} B) k j)
        (upperStarComp (ModuleCat.{u + 1} A) k j) hq)
  have he := congrArg (fun t ↦ t ≫
    (Functor.mapDerivedCategoryNatIso (upperStarComp (ModuleCat.{u + 1} A) k j) ≪≫
      Functor.mapDerivedCategoryCompIso _ _).inv.app
        ((Sheaf.derivedRestrictScalars (Scheme.ProEt.topology X) φ).obj K)) hc
  simp only [Category.assoc, Iso.hom_inv_id_app] at he
  erw [Category.comp_id] at he
  simpa only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id] using he.symm

private theorem pro_restrict_id {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (X : Scheme.{u})
    (M : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} B)) :
    (proRestrictionSquare φ (𝟙 X)).hom.app M ≫
      (upperStarId (ModuleCat.{u + 1} A) X).hom.app
        ((Sheaf.restrictScalars (Scheme.ProEt.topology X) φ).obj M) =
      (Sheaf.restrictScalars (Scheme.ProEt.topology X) φ).map
        ((upperStarId (ModuleCat.{u + 1} B) X).hom.app M) := by
  apply (cancel_epi ((upperStarRestrictScalarsIso φ (𝟙 X)).hom.app M)).mp
  simp only [proRestrictionSquare, Iso.symm_hom, Iso.hom_inv_id_app_assoc]
  have h := congr_app (upperStarRestrictScalarsIso_id_hom φ X) M
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.leftUnitor_inv_app, Functor.rightUnitor_hom_app] at h
  erw [Category.comp_id] at h
  exact h.symm


private theorem et_restrict_comp {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {V U X : Scheme.{u}} (k : V ⟶ U) (j : U ⟶ X)
    [IsOpenImmersion k] [IsOpenImmersion j]
    (M : Sheaf (X.smallEtaleTopology) (ModuleCat.{u + 1} B)) :
    (Sheaf.restrictScalars (V.smallEtaleTopology) φ).map
        ((Etale.upperStarComp (ModuleCat.{u + 1} B) k j).hom.app M) ≫
      (etRestrictionSquare φ k).hom.app ((Etale.upperStar (ModuleCat.{u + 1} B) j).obj M) ≫
      (Etale.upperStar (ModuleCat.{u + 1} A) k).map ((etRestrictionSquare φ j).hom.app M) =
    (etRestrictionSquare φ (k ≫ j)).hom.app M ≫
      (Etale.upperStarComp (ModuleCat.{u + 1} A) k j).hom.app
        ((Sheaf.restrictScalars (X.smallEtaleTopology) φ).obj M) := by
  have h := congr_app (Etale.upperStarRestrictScalarsIso_comp_hom φ k j) M
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id] at h
  apply (cancel_epi ((Etale.upperStarRestrictScalarsIso φ (k ≫ j)).hom.app M)).mp
  simp only [etRestrictionSquare, Iso.symm_hom]
  rw [← Category.assoc, ← Category.assoc, h]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc, Iso.hom_inv_id_app]
  erw [Category.id_comp]
  rw [← Functor.map_comp, Iso.hom_inv_id_app]
  simp only [CategoryTheory.Functor.map_id]
  erw [Category.comp_id]

private theorem et_derived_restrict_comp {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {V U X : Scheme.{u}} (k : V ⟶ U) (j : U ⟶ X)
    [IsOpenImmersion k] [IsOpenImmersion j]
    (hq : ∀ M : Sheaf (X.smallEtaleTopology) (ModuleCat.{u + 1} B),
      (Sheaf.restrictScalars (V.smallEtaleTopology) φ).map
          ((Etale.upperStarComp (ModuleCat.{u + 1} B) k j).hom.app M) ≫
        (etRestrictionSquare φ k).hom.app
          ((Etale.upperStar (ModuleCat.{u + 1} B) j).obj M) ≫
        (Etale.upperStar (ModuleCat.{u + 1} A) k).map
          ((etRestrictionSquare φ j).hom.app M) =
      (etRestrictionSquare φ (k ≫ j)).hom.app M ≫
        (Etale.upperStarComp (ModuleCat.{u + 1} A) k j).hom.app
          ((Sheaf.restrictScalars (X.smallEtaleTopology) φ).obj M)) :
    let RA (T : Scheme.{u}) := Sheaf.derivedRestrictScalars (T.smallEtaleTopology) φ
    let UB {S T : Scheme.{u}} (f : S ⟶ T) :=
      (Etale.upperStar (ModuleCat.{u + 1} B) f).mapDerivedCategory
    let UA {S T : Scheme.{u}} (f : S ⟶ T) :=
      (Etale.upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory
    let β := Functor.mapDerivedCategoryNatIso (Etale.upperStarComp (ModuleCat.{u + 1} A) k j) ≪≫
      Functor.mapDerivedCategoryCompIso _ _
    let γ := Functor.mapDerivedCategoryNatIso (Etale.upperStarComp (ModuleCat.{u + 1} B) k j) ≪≫
      Functor.mapDerivedCategoryCompIso _ _
    Functor.mapDerivedCategorySquareIso (etRestrictionSquare φ (k ≫ j)) =
      Functor.isoWhiskerRight γ (RA V) ≪≫
      Functor.associator (UB j) (UB k) (RA V) ≪≫
      Functor.isoWhiskerLeft (UB j)
        (Functor.mapDerivedCategorySquareIso (etRestrictionSquare φ k)) ≪≫
      (Functor.associator (UB j) (RA U) (UA k)).symm ≪≫
      Functor.isoWhiskerRight
        (Functor.mapDerivedCategorySquareIso (etRestrictionSquare φ j)) (UA k) ≪≫
      Functor.associator (RA X) (UA j) (UA k) ≪≫
      Functor.isoWhiskerLeft (RA X) β.symm := by
  dsimp only
  apply Iso.ext
  ext K
  have hc :
      (Sheaf.derivedRestrictScalars (V.smallEtaleTopology) φ).map
          ((Functor.mapDerivedCategoryNatIso (Etale.upperStarComp (ModuleCat.{u + 1} B) k j) ≪≫
            Functor.mapDerivedCategoryCompIso _ _).hom.app K) ≫
        (Functor.mapDerivedCategorySquareIso (etRestrictionSquare φ k)).hom.app
          ((Etale.upperStar (ModuleCat.{u + 1} B) j).mapDerivedCategory.obj K) ≫
        (Etale.upperStar (ModuleCat.{u + 1} A) k).mapDerivedCategory.map
          ((Functor.mapDerivedCategorySquareIso (etRestrictionSquare φ j)).hom.app K) =
      (Functor.mapDerivedCategorySquareIso (etRestrictionSquare φ (k ≫ j))).hom.app K ≫
        (Functor.mapDerivedCategoryNatIso (Etale.upperStarComp (ModuleCat.{u + 1} A) k j) ≪≫
          Functor.mapDerivedCategoryCompIso _ _).hom.app
            ((Sheaf.derivedRestrictScalars (X.smallEtaleTopology) φ).obj K) := by
    simpa only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
      Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Functor.associator_hom_app, Functor.associator_inv_app,
      Category.id_comp, Category.comp_id] using congrArg (fun e ↦ e.hom.app K)
      (Functor.mapDerivedCategorySquareIso_comp
        (C₀ := Sheaf (X.smallEtaleTopology) (ModuleCat.{u + 1} B))
        (C₁ := Sheaf (U.smallEtaleTopology) (ModuleCat.{u + 1} B))
        (C₂ := Sheaf (V.smallEtaleTopology) (ModuleCat.{u + 1} B))
        (D₀ := Sheaf (X.smallEtaleTopology) (ModuleCat.{u + 1} A))
        (D₁ := Sheaf (U.smallEtaleTopology) (ModuleCat.{u + 1} A))
        (D₂ := Sheaf (V.smallEtaleTopology) (ModuleCat.{u + 1} A))
        (Etale.upperStar (ModuleCat.{u + 1} B) j) (Etale.upperStar (ModuleCat.{u + 1} B) k)
        (Etale.upperStar (ModuleCat.{u + 1} B) (k ≫ j))
        (Etale.upperStar (ModuleCat.{u + 1} A) j) (Etale.upperStar (ModuleCat.{u + 1} A) k)
        (Etale.upperStar (ModuleCat.{u + 1} A) (k ≫ j))
        (Sheaf.restrictScalars (X.smallEtaleTopology) φ)
        (Sheaf.restrictScalars (U.smallEtaleTopology) φ)
        (Sheaf.restrictScalars (V.smallEtaleTopology) φ)
        (etRestrictionSquare φ j) (etRestrictionSquare φ k)
        (etRestrictionSquare φ (k ≫ j))
        (Etale.upperStarComp (ModuleCat.{u + 1} B) k j)
        (Etale.upperStarComp (ModuleCat.{u + 1} A) k j) hq)
  have he := congrArg (fun t ↦ t ≫
    (Functor.mapDerivedCategoryNatIso (Etale.upperStarComp (ModuleCat.{u + 1} A) k j) ≪≫
      Functor.mapDerivedCategoryCompIso _ _).inv.app
        ((Sheaf.derivedRestrictScalars (X.smallEtaleTopology) φ).obj K)) hc
  simp only [Category.assoc, Iso.hom_inv_id_app] at he
  erw [Category.comp_id] at he
  simpa only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id] using he.symm

private theorem et_restrict_id {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (X : Scheme.{u})
    (M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)) :
    (etRestrictionSquare φ (𝟙 X)).hom.app M ≫
      (Etale.upperStarId (ModuleCat.{u + 1} A) X).hom.app
        ((Sheaf.restrictScalars X.smallEtaleTopology φ).obj M) =
      (Sheaf.restrictScalars X.smallEtaleTopology φ).map
        ((Etale.upperStarId (ModuleCat.{u + 1} B) X).hom.app M) := by
  apply (cancel_epi ((Etale.upperStarRestrictScalarsIso φ (𝟙 X)).hom.app M)).mp
  simp only [etRestrictionSquare, Iso.symm_hom, Iso.hom_inv_id_app_assoc]
  have h := congr_app (Etale.upperStarRestrictScalarsIso_id_hom φ X) M
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.leftUnitor_inv_app, Functor.rightUnitor_hom_app] at h
  erw [Category.comp_id] at h
  exact h.symm


private theorem inverse_mate_cube
    {A B C D A' B' C' D' : Type*}
    [Category A] [Category B] [Category C] [Category D]
    [Category A'] [Category B'] [Category C'] [Category D']
    {L : A ⥤ A'} {U : A' ⥤ A} {l : B ⥤ B'} {u : B' ⥤ B}
    {M : C ⥤ C'} {V : C' ⥤ C} {m : D ⥤ D'} {v : D' ⥤ D}
    (a : L ⊣ U) (al : l ⊣ u) (am : M ⊣ V) (ad : m ⊣ v)
    {r : A ⥤ B} {r' : A' ⥤ B'} {H : A ⥤ C} {H' : A' ⥤ C'}
    {K : B ⥤ D} {K' : B' ⥤ D'} {s : C ⥤ D} {s' : C' ⥤ D'}
    (t : TwoSquare U r' r u) (k : TwoSquare u K' K v)
    (c : TwoSquare U H' H V) (q : TwoSquare V s' s v)
    (b : r ⋙ K ≅ H ⋙ s) (b' : r' ⋙ K' ≅ H' ⋙ s')
    (h : t ≫ᵥ k = TwoSquare.mk U (r' ⋙ K') (r ⋙ K) v
      (Functor.whiskerLeft U b.hom ≫ (c ≫ᵥ q).natTrans ≫
        Functor.whiskerRight b'.inv v)) (x : A) :
    m.map (b.hom.app x) ≫
        ((mateEquiv am ad).symm q).app (H.obj x) ≫
        s'.map (((mateEquiv a am).symm c).app x) =
      ((mateEquiv al ad).symm k).app (r.obj x) ≫
        K'.map (((mateEquiv a al).symm t).app x) ≫ b'.hom.app (L.obj x) := by
  have ht := inverse_mate_paste a al ad t k
  have hq := inverse_mate_paste a am ad c q
  rw [h] at ht
  have hn := inverse_mate_transport a ad (c ≫ᵥ q) b.symm b'.symm
  have hp := congrArg (fun w ↦ w.natTrans.app x) ht
  dsimp only [Iso.symm_hom, Iso.symm_inv] at hn
  rw [NatTrans.congr_app hn] at hp
  rw [hq] at hp
  simp only [TwoSquare.hComp, TwoSquare.natTrans, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Category.comp_id, Category.id_comp, Category.assoc] at hp
  have hh := congrArg (fun f ↦ f ≫ b'.hom.app (L.obj x)) hp
  simp only [Category.assoc, Iso.inv_hom_id_app] at hh
  erw [Category.comp_id] at hh
  exact hh

private theorem derived_cube
    {A B C D A' B' C' D' : Type*}
    [Category A] [Category B] [Category C] [Category D]
    [Category A'] [Category B'] [Category C'] [Category D']
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [Abelian A'] [Abelian B'] [Abelian C'] [Abelian D']
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
    [HasDerivedCategory D] [HasDerivedCategory A'] [HasDerivedCategory B']
    [HasDerivedCategory C'] [HasDerivedCategory D']
    (U : A' ⥤ A) (V : B' ⥤ B) (W : C' ⥤ C) (Z : D' ⥤ D)
    (r : A ⥤ B) (r' : A' ⥤ B') (s : C ⥤ D) (s' : C' ⥤ D')
    (H : A ⥤ C) (H' : A' ⥤ C') (K : B ⥤ D) (K' : B' ⥤ D')
    [U.Additive] [V.Additive] [W.Additive] [Z.Additive]
    [r.Additive] [r'.Additive] [s.Additive] [s'.Additive]
    [H.Additive] [H'.Additive] [K.Additive] [K'.Additive]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    [PreservesFiniteLimits W] [PreservesFiniteColimits W]
    [PreservesFiniteLimits Z] [PreservesFiniteColimits Z]
    [PreservesFiniteLimits r] [PreservesFiniteColimits r]
    [PreservesFiniteLimits r'] [PreservesFiniteColimits r']
    [PreservesFiniteLimits s] [PreservesFiniteColimits s]
    [PreservesFiniteLimits s'] [PreservesFiniteColimits s']
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    [PreservesFiniteLimits H'] [PreservesFiniteColimits H']
    [PreservesFiniteLimits K] [PreservesFiniteColimits K]
    [PreservesFiniteLimits K'] [PreservesFiniteColimits K']
    (t : U ⋙ r ≅ r' ⋙ V) (k : V ⋙ K ≅ K' ⋙ Z)
    (c : U ⋙ H ≅ H' ⋙ W) (q : W ⋙ s ≅ s' ⋙ Z)
    (b : r ⋙ K ≅ H ⋙ s) (b' : r' ⋙ K' ≅ H' ⋙ s')
    (h : ∀ x, K.map (t.hom.app x) ≫ k.hom.app (r'.obj x) ≫ Z.map (b'.hom.app x) =
      b.hom.app (U.obj x) ≫ s.map (c.hom.app x) ≫ q.hom.app (H'.obj x))
    (x : DerivedCategory A') :
    K.mapDerivedCategory.map ((Functor.mapDerivedCategorySquareIso t).hom.app x) ≫
        (Functor.mapDerivedCategorySquareIso k).hom.app (r'.mapDerivedCategory.obj x) ≫
        Z.mapDerivedCategory.map ((Functor.mapDerivedCategorySquareIso b').hom.app x) =
      (Functor.mapDerivedCategorySquareIso b).hom.app (U.mapDerivedCategory.obj x) ≫
        s.mapDerivedCategory.map ((Functor.mapDerivedCategorySquareIso c).hom.app x) ≫
        (Functor.mapDerivedCategorySquareIso q).hom.app (H'.mapDerivedCategory.obj x) := by
  let a : U ⋙ (r ⋙ K) ≅ (r' ⋙ K') ⋙ Z :=
    Functor.isoWhiskerRight t K ≪≫ Functor.isoWhiskerLeft r' k
  have h₁ := Functor.mapDerivedCategorySquareIso_hom_app_comp t k a
    (Iso.refl (r ⋙ K)) (Iso.refl (r' ⋙ K')) (fun y ↦ by simp [a]) x
  have h₂ := Functor.mapDerivedCategorySquareIso_hom_app_comp c q a b b'
    (fun y ↦ by simpa [a] using h y) x
  simp only [Functor.mapDerivedCategoryTriangleIso, Functor.mapDerivedCategoryNatIso_refl,
    Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, CategoryTheory.Functor.map_comp,
    Category.assoc, Category.id_comp] at h₁ h₂
  rw [← cancel_epi ((Functor.mapDerivedCategoryCompIso r K).hom.app
    (U.mapDerivedCategory.obj x))]
  rw [← cancel_mono (Z.mapDerivedCategory.map
    ((Functor.mapDerivedCategoryCompIso H' s').inv.app x))]
  simp only [Functor.mapDerivedCategorySquareIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, CategoryTheory.Functor.map_comp, Category.assoc]
  simp only [Iso.hom_inv_id_app_assoc]
  rw [← reassoc_of% h₁, ← reassoc_of% h₂]
  simp only [← Z.mapDerivedCategory.map_comp_assoc]
  simp only [Iso.hom_inv_id_app_assoc]

private theorem open_mate_cube
    {C D E F Cb Db Eb Fb : Type*}
    [Category C] [Category D] [Category E] [Category F]
    [Category Cb] [Category Db] [Category Eb] [Category Fb]
    {LA : C ⥤ D} {JA : D ⥤ C} {LA' : E ⥤ F} {JA' : F ⥤ E}
    {LB : Cb ⥤ Db} {JB : Db ⥤ Cb} {LB' : Eb ⥤ Fb} {JB' : Fb ⥤ Eb}
    (a : LA ⊣ JA) (a' : LA' ⊣ JA') (b : LB ⊣ JB) (b' : LB' ⊣ JB')
    {HA : C ⥤ E} {GA : D ⥤ F} {HB : Cb ⥤ Eb} {GB : Db ⥤ Fb}
    {S : C ⥤ Cb} {Q : D ⥤ Db} {S' : E ⥤ Eb} {Q' : F ⥤ Fb}
    (β : LA ⋙ Q ≅ S ⋙ LB) (β' : LA' ⋙ Q' ≅ S' ⋙ LB')
    (dA : HA ⋙ LA' ≅ LA ⋙ GA) (dB : HB ⋙ LB' ≅ LB ⋙ GB)
    (lj : JA ⋙ S ⟶ Q ⋙ JB) (lj' : JA' ⋙ S' ⟶ Q' ⋙ JB')
    (lh : S ⋙ HB ≅ HA ⋙ S') (lg : Q ⋙ GB ≅ GA ⋙ Q')
    (cA : JA ⋙ HA ≅ GA ⋙ JA') (cB : JB ⋙ HB ≅ GB ⋙ JB')
    (hi : ∀ M, b.unit.app (S.obj M) ≫ JB.map (β.inv.app M) =
      S.map (a.unit.app M) ≫ lj.app (LA.obj M))
    (hi' : ∀ M, b'.unit.app (S'.obj M) ≫ JB'.map (β'.inv.app M) =
      S'.map (a'.unit.app M) ≫ lj'.app (LA'.obj M))
    (hdA : ∀ M, a'.unit.app (HA.obj M) ≫ JA'.map (dA.hom.app M) =
      HA.map (a.unit.app M) ≫ cA.hom.app (LA.obj M))
    (hdB : ∀ M, b'.unit.app (HB.obj M) ≫ JB'.map (dB.hom.app M) =
      HB.map (b.unit.app M) ≫ cB.hom.app (LB.obj M))
    (hc : ∀ N, S'.map (cA.hom.app N) ≫ lj'.app (GA.obj N) ≫
        JB'.map (lg.inv.app N) =
      lh.inv.app (JA.obj N) ≫ HB.map (lj.app N) ≫ cB.hom.app (Q.obj N))
    (M : C) :
    LB'.map (lh.inv.app M) ≫ dB.hom.app (S.obj M) ≫ GB.map (β.inv.app M) =
      β'.inv.app (HA.obj M) ≫ Q'.map (dA.hom.app M) ≫ lg.inv.app (LA.obj M) := by
  apply (b'.homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit, Functor.map_comp, Functor.comp_obj]
  have hn := b'.unit.naturality (lh.inv.app M)
  dsimp only [Functor.id_map, Functor.comp_map, Functor.comp_obj] at hn
  rw [← reassoc_of% hn, reassoc_of% hdB]
  have hn := cB.hom.naturality (β.inv.app M)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hn
  rw [← hn, ← HB.map_comp_assoc, hi, HB.map_comp, Category.assoc]
  have hn := lh.inv.naturality (a.unit.app M)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hn
  rw [← reassoc_of% hn]
  rw [reassoc_of% hi']
  have hn := lj'.naturality (dA.hom.app M)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hn
  rw [← reassoc_of% hn, ← S'.map_comp_assoc, hdA, S'.map_comp, Category.assoc]
  rw [hc]


private theorem et_coefficient_conjugate
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {U X : Scheme.{u}} (j : U ⟶ X) :
    conjugateIsoEquiv
      ((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} B) j).comp
        (Sheaf.restrictCoextendScalarsAdj U.smallEtaleTopology φ))
      ((Sheaf.restrictCoextendScalarsAdj X.smallEtaleTopology φ).comp
        (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) j))
      (Etale.upperStarRestrictScalarsIso φ j) = Iso.refl _ := by
  apply Iso.ext
  exact Etale.conjugateEquiv_upperStarRestrictScalarsIso_hom φ j

private theorem ordinary_restriction_cube
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (a : A →+* B) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (N : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} B)) :
    (upperStar (ModuleCat.{u + 1} A) f).map
        ((CoefficientScalarRepresentatives.comparisonRestriction Y a).inv.app N) ≫
      (upperStarRestrictScalarsIso a f).hom.app
        ((comparisonUpperStar (ModuleCat.{u + 1} B) Y).obj N) ≫
      (Sheaf.restrictScalars (Scheme.ProEt.topology X) a).map
        ((comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} B) f).hom.app N) =
    (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} A) f).hom.app
        ((Sheaf.restrictScalars Y.smallEtaleTopology a).obj N) ≫
      (comparisonUpperStar (ModuleCat.{u + 1} A) X).map
        ((Etale.upperStarRestrictScalarsIso a f).hom.app N) ≫
      (CoefficientScalarRepresentatives.comparisonRestriction X a).inv.app
        ((Etale.upperStar (ModuleCat.{u + 1} B) f).obj N) := by
  let cyA := comparisonAdjunction (ModuleCat.{u + 1} A) Y
  let cxA := comparisonAdjunction (ModuleCat.{u + 1} A) X
  let cyB := comparisonAdjunction (ModuleCat.{u + 1} B) Y
  let cxB := comparisonAdjunction (ModuleCat.{u + 1} B) X
  let pA := upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f
  let pB := upperStarLowerStarAdjunction (ModuleCat.{u + 1} B) f
  let lA := Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f
  let lB := Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} B) f
  let ey := Sheaf.restrictCoextendScalarsAdj Y.smallEtaleTopology a
  let ex := Sheaf.restrictCoextendScalarsAdj X.smallEtaleTopology a
  let py := Sheaf.restrictCoextendScalarsAdj (Scheme.ProEt.topology Y) a
  let px := Sheaf.restrictCoextendScalarsAdj (Scheme.ProEt.topology X) a
  let e₁ := Functor.isoWhiskerRight
    (CoefficientScalarRepresentatives.comparisonRestriction Y a).symm (adjLeft pA)
  let e₂ := Functor.associator (adjLeft cyB) (adjLeft py) (adjLeft pA)
  let e₃ := Functor.isoWhiskerLeft (adjLeft cyB) (upperStarRestrictScalarsIso a f)
  let e₄ := (Functor.associator (adjLeft cyB) (adjLeft pB) (adjLeft px)).symm
  let e₅ := Functor.isoWhiskerRight
    (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} B) f) (adjLeft px)
  let e₁' := Functor.associator (adjLeft ey) (adjLeft cyA) (adjLeft pA)
  let e₂' := Functor.isoWhiskerLeft (adjLeft ey)
    (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} A) f)
  let e₃' := (Functor.associator (adjLeft ey) (adjLeft lA) (adjLeft cxA)).symm
  let e₄' := Functor.isoWhiskerRight (Etale.upperStarRestrictScalarsIso a f) (adjLeft cxA)
  let e₅' := Functor.associator (adjLeft lB) (adjLeft ex) (adjLeft cxA)
  let e₆' := Functor.isoWhiskerLeft (adjLeft lB)
    (CoefficientScalarRepresentatives.comparisonRestriction X a).symm
  let e₇' := (Functor.associator (adjLeft lB) (adjLeft cxB) (adjLeft px)).symm
  have h : (((e₁ ≪≫ e₂) ≪≫ e₃) ≪≫ e₄) ≪≫ e₅ =
      (((((e₁' ≪≫ e₂') ≪≫ e₃') ≪≫ e₄') ≪≫ e₅') ≪≫ e₆') ≪≫ e₇' := by
    apply (conjugateIsoEquiv ((lB.comp cxB).comp px) ((ey.comp cyA).comp pA)).injective
    rw [conjugateIsoEquiv_trans _ ((cyB.comp pB).comp px),
      conjugateIsoEquiv_trans _ (cyB.comp (pB.comp px)),
      conjugateIsoEquiv_trans _ (cyB.comp (py.comp pA)),
      conjugateIsoEquiv_trans _ ((cyB.comp py).comp pA)]
    rw [conjugateIsoEquiv_trans _ (lB.comp (cxB.comp px)),
      conjugateIsoEquiv_trans _ (lB.comp (ex.comp cxA)),
      conjugateIsoEquiv_trans _ ((lB.comp ex).comp cxA),
      conjugateIsoEquiv_trans _ ((ey.comp lA).comp cxA),
      conjugateIsoEquiv_trans _ (ey.comp (lA.comp cxA)),
      conjugateIsoEquiv_trans _ (ey.comp (cyA.comp pA))]
    dsimp only [e₁, e₂, e₃, e₄, e₅, e₁', e₂', e₃', e₄', e₅', e₆', e₇']
    simp only [conjugateIsoEquiv_isoWhiskerRight, conjugateIsoEquiv_isoWhiskerLeft]
    simp only [cyA, cxA, cyB, cxB, pA, pB, lA, lB, ey, ex, py, px,
      CoefficientScalarRepresentatives.comparisonRestriction, comparisonUpperStarCompUpperStarIso,
      upperStarRestrictScalarsIso, et_coefficient_conjugate,
      conjugateIsoEquiv_iso_symm,
      Equiv.apply_symm_apply, conjugateIsoEquiv_associator]
    ext F V x
    simp only [lowerStarCompComparisonLowerStarIso, toProEtCompOverPullbackIso,
      Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app]
    simp
    rfl
  simpa only [e₁, e₂, e₃, e₄, e₅, e₁', e₂', e₃', e₄', e₅', e₆', e₇',
    Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp,
    Category.comp_id, Category.assoc, pA, px, cyB, ey, cxA, lB] using
    congrArg (fun e ↦ e.hom.app N) h

private theorem site_pullback_eq (A : Type (u + 1)) [CommRing A]
    {U X : Scheme.{u}} (j : U ⟶ X) :
    site_pullback A j = (comparisonUpperStarCompUpperStarIso
      (ModuleCat.{u + 1} A) j).symm := by
  rfl

private def etScalarRestrictionMap
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {U X : Scheme.{u}} (j : U ⟶ X) :=
  ((mateEquiv (CoefficientScalarRepresentatives.adjunction X.smallEtaleTopology φ)
    (CoefficientScalarRepresentatives.adjunction U.smallEtaleTopology φ)).symm
    (TwoSquare.mk _ _ _ _
      (Functor.mapDerivedCategorySquareIso (etRestrictionSquare φ j)).inv)).natTrans

private theorem upper_coefficient_cube {A B : Type (u + 1)} [CommRing A] [CommRing B]
    [Finite A] [Finite B] (φ : A →+* B) {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j]
    (M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)) :
    (comparisonUpperStar (ModuleCat.{u + 1} A) U).map
        ((etRestrictionSquare φ j).inv.app M) ≫
      (CoefficientScalarRepresentatives.comparisonRestriction U φ).inv.app
        ((Etale.upperStar (ModuleCat.{u + 1} B) j).obj M) ≫
      (Sheaf.restrictScalars (Scheme.ProEt.topology U) φ).map
        ((site_pullback B j).hom.app M) =
    (site_pullback A j).hom.app
        ((Sheaf.restrictScalars X.smallEtaleTopology φ).obj M) ≫
      (upperStar (ModuleCat.{u + 1} A) j).map
        ((CoefficientScalarRepresentatives.comparisonRestriction X φ).inv.app M) ≫
      (proRestrictionSquare φ j).inv.app
        ((comparisonUpperStar (ModuleCat.{u + 1} B) X).obj M) := by
  have h := ordinary_restriction_cube φ j M
  have h' := congrArg (fun f ↦ (site_pullback A j).hom.app
      ((Sheaf.restrictScalars X.smallEtaleTopology φ).obj M) ≫ f ≫
      (Sheaf.restrictScalars (Scheme.ProEt.topology U) φ).map
        ((site_pullback B j).hom.app M)) h
  simp only [site_pullback_eq, Iso.symm_hom, Category.assoc,
    ← Functor.map_comp, Iso.inv_hom_id_app_assoc, Iso.hom_inv_id_app] at h'
  erw [CategoryTheory.Functor.map_id, Category.comp_id] at h'
  simpa only [site_pullback_eq, Iso.symm_hom, etRestrictionSquare,
    proRestrictionSquare, Iso.symm_inv] using h'.symm

private theorem derived_coefficient_cube {A B : Type (u + 1)} [CommRing A] [CommRing B]
    [Finite A] [Finite B] (φ : A →+* B) {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j]
    (M : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B))) :
    (comparisonUpperStar (ModuleCat.{u + 1} A) U).mapDerivedCategory.map
        ((Functor.mapDerivedCategorySquareIso (etRestrictionSquare φ j)).inv.app M) ≫
      (CoefficientScalarRepresentatives.derivedComparisonRestriction U φ).inv.app
        ((Etale.upperStar (ModuleCat.{u + 1} B) j).mapDerivedCategory.obj M) ≫
      (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology U) φ).map
        ((Functor.mapDerivedCategorySquareIso
          (site_pullback B j)).hom.app M) =
    (Functor.mapDerivedCategorySquareIso
        (site_pullback A j)).hom.app
        ((Sheaf.derivedRestrictScalars X.smallEtaleTopology φ).obj M) ≫
      (upperStar (ModuleCat.{u + 1} A) j).mapDerivedCategory.map
        ((CoefficientScalarRepresentatives.derivedComparisonRestriction X φ).inv.app M) ≫
      (Functor.mapDerivedCategorySquareIso (proRestrictionSquare φ j)).inv.app
        ((comparisonUpperStar (ModuleCat.{u + 1} B) X).mapDerivedCategory.obj M) := by
  have h := derived_cube
    (Sheaf.restrictScalars X.smallEtaleTopology φ)
    (Sheaf.restrictScalars U.smallEtaleTopology φ)
    (Sheaf.restrictScalars (Scheme.ProEt.topology X) φ)
    (Sheaf.restrictScalars (Scheme.ProEt.topology U) φ)
    (Etale.upperStar (ModuleCat.{u + 1} A) j)
    (Etale.upperStar (ModuleCat.{u + 1} B) j)
    (upperStar (ModuleCat.{u + 1} A) j)
    (upperStar (ModuleCat.{u + 1} B) j)
    (comparisonUpperStar (ModuleCat.{u + 1} A) X)
    (comparisonUpperStar (ModuleCat.{u + 1} B) X)
    (comparisonUpperStar (ModuleCat.{u + 1} A) U)
    (comparisonUpperStar (ModuleCat.{u + 1} B) U)
    (etRestrictionSquare φ j).symm (CoefficientScalarRepresentatives.comparisonRestriction U φ).symm
    (CoefficientScalarRepresentatives.comparisonRestriction X φ).symm
    (proRestrictionSquare φ j).symm
    (site_pullback A j)
    (site_pullback B j)
    (upper_coefficient_cube φ j) M
  simpa only [CoefficientScalarRepresentatives.derivedComparisonRestriction,
    Functor.mapDerivedCategorySquareIso,
    Functor.mapDerivedCategoryNatIso_symm, Iso.trans_hom, Iso.trans_inv,
    Iso.symm_hom, Iso.symm_inv, NatTrans.comp_app, Functor.map_comp, Category.assoc] using h

private theorem scalar_pullback_cube {A B : Type (u + 1)} [CommRing A] [CommRing B]
    [Finite A] [Finite B] (φ : A →+* B) {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j]
    (M : Etale.DerivedCategoryModule A X) :
    (CoefficientScalarRepresentatives.extension (Scheme.ProEt.topology U) φ).map
        ((Functor.mapDerivedCategorySquareIso
          (site_pullback A j)).hom.app M) ≫
      ((mateEquiv
        (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology X) φ))
        (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology U)
      φ))).symm
          (TwoSquare.mk _ _ _ _
            (Functor.mapDerivedCategorySquareIso (proRestrictionSquare φ j)).inv)).natTrans.app
              ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj M) ≫
      (upperStar (ModuleCat.{u + 1} B) j).mapDerivedCategory.map
        ((CoefficientScalarRepresentatives.comparisonIso X φ).hom.app M) =
    (CoefficientScalarRepresentatives.comparisonIso U φ).hom.app
        ((Etale.upperStar (ModuleCat.{u + 1} A) j).mapDerivedCategory.obj M) ≫
      (comparisonUpperStar (ModuleCat.{u + 1} B) U).mapDerivedCategory.map
        ((etScalarRestrictionMap φ j).app M) ≫
      (Functor.mapDerivedCategorySquareIso
        (site_pullback B j)).hom.app
          ((CoefficientScalarRepresentatives.extension X.smallEtaleTopology φ).obj M) := by
  let a := Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars X.smallEtaleTopology φ)
  let al := Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars U.smallEtaleTopology φ)
  let am := Adjunction.ofIsRightAdjoint
    (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology X) φ)
  let ad := Adjunction.ofIsRightAdjoint
    (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology U) φ)
  let t := TwoSquare.mk _ _ _ _
    (Functor.mapDerivedCategorySquareIso (etRestrictionSquare φ j)).inv
  let k := TwoSquare.mk _ _ _ _
    (CoefficientScalarRepresentatives.derivedComparisonRestriction U φ).inv
  let c := TwoSquare.mk _ _ _ _
    (CoefficientScalarRepresentatives.derivedComparisonRestriction X φ).inv
  let q := TwoSquare.mk _ _ _ _
    (Functor.mapDerivedCategorySquareIso (proRestrictionSquare φ j)).inv
  let b := Functor.mapDerivedCategorySquareIso
    (site_pullback A j)
  let b' := Functor.mapDerivedCategorySquareIso
    (site_pullback B j)
  have hp : TwoSquare.vComp t k = TwoSquare.mk _ _ _ _
      (Functor.whiskerLeft (Sheaf.derivedRestrictScalars X.smallEtaleTopology φ) b.hom ≫
        (TwoSquare.vComp c q).natTrans ≫ Functor.whiskerRight b'.inv
          (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology U) φ)) := by
    ext N
    simp only [TwoSquare.vComp, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, Functor.associator_hom_app, Functor.associator_inv_app,
      Category.id_comp, Category.comp_id, Category.assoc]
    dsimp only [t, k, c, q, b, b']
    apply (cancel_mono ((Sheaf.derivedRestrictScalars
      (Scheme.ProEt.topology U) φ).map
        ((Functor.mapDerivedCategorySquareIso
          (site_pullback B j)).hom.app N))).mp
    simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app,
      CategoryTheory.Functor.map_id]
    erw [Category.comp_id]
    exact derived_coefficient_cube φ j N
  have h := inverse_mate_cube a al am ad t k c q b b' hp M
  simpa only [a, al, am, ad, t, k, c, q, b, b',
    CoefficientScalarRepresentatives.comparisonIso, asIso_hom,
    CoefficientScalarRepresentatives.comparisonMap, etScalarRestrictionMap,
    CoefficientScalarRepresentatives.extension, CoefficientScalarRepresentatives.adjunction,
    Category.assoc,
    TwoSquare, TwoSquare.mk, TwoSquare.natTrans] using h

/-- Derived site comparisons compose with the same open compositors.
Source: Stacks 09AF (blueprint: lem-sp-open-scalar-site-coherence).
Proof: Use the recorded sheaf site-comparison composition identity, whose two
maps have the same transpose under the open adjunctions. Apply the degreewise
complex functor and localization. The derived functor composition isomorphisms
identify the resulting equation with this displayed equation. -/
theorem site_comp (R : Type (u + 1)) [CommRing R] [Finite R]
    {V U X : Scheme.{u}} (k : V ⟶ U) (j : U ⟶ X)
    [IsOpenImmersion k] [IsOpenImmersion j] (L : Etale.DerivedCategoryModule R V) :
    (comparisonUpperStar (ModuleCat.{u + 1} R) X).mapDerivedCategory.map
        ((Etale.mapDerivedCategoryOpenImmersionLowerShriekComp
          (ModuleCat.{u + 1} R) k j).hom.app L) ≫
      (mapDerivedCategoryOpenImmersionLowerShriekComparisonUpperStarIso
        (ModuleCat.{u + 1} R) j).hom.app
          ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} R) k).mapDerivedCategory.obj L) ≫
      (openImmersionLowerShriek (ModuleCat.{u + 1} R) j).mapDerivedCategory.map
        ((mapDerivedCategoryOpenImmersionLowerShriekComparisonUpperStarIso
          (ModuleCat.{u + 1} R) k).hom.app L) ≫
      (extensionComp R k j).inv.app
        ((comparisonUpperStar (ModuleCat.{u + 1} R) V).mapDerivedCategory.obj L) =
    (mapDerivedCategoryOpenImmersionLowerShriekComparisonUpperStarIso
      (ModuleCat.{u + 1} R) (k ≫ j)).hom.app L := by
  let E (T : Scheme.{u}) := comparisonUpperStar (ModuleCat.{u + 1} R) T
  let f := Etale.openImmersionLowerShriek (ModuleCat.{u + 1} R) k
  let g := Etale.openImmersionLowerShriek (ModuleCat.{u + 1} R) j
  let fg := Etale.openImmersionLowerShriek (ModuleCat.{u + 1} R) (k ≫ j)
  let f' := openImmersionLowerShriek (ModuleCat.{u + 1} R) k
  let g' := openImmersionLowerShriek (ModuleCat.{u + 1} R) j
  let fg' := openImmersionLowerShriek (ModuleCat.{u + 1} R) (k ≫ j)
  have hq (F : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} R)) :
      (E X).map ((Etale.openImmersionLowerShriekComp
        (ModuleCat.{u + 1} R) k j).hom.app F) ≫
      (openImmersionLowerShriekComparisonUpperStarIso (ModuleCat.{u + 1} R) j).hom.app
        (f.obj F) ≫ g'.map
        ((openImmersionLowerShriekComparisonUpperStarIso (ModuleCat.{u + 1} R) k).hom.app F) =
      (openImmersionLowerShriekComparisonUpperStarIso
        (ModuleCat.{u + 1} R) (k ≫ j)).hom.app F ≫
      (proEtaleOpenExtensionComp R k j).hom.app ((E V).obj F) := by
    have hc := (openImmersionLowerShriekComparison_coherence R).2.1 k j F
    have he := congrArg (fun t ↦ t ≫
      (proEtaleOpenExtensionComp R k j).hom.app ((E V).obj F)) hc
    simpa [Category.assoc, E, f, g'] using he
  have hc :
      (E X).mapDerivedCategory.map
          ((Etale.mapDerivedCategoryOpenImmersionLowerShriekComp
            (ModuleCat.{u + 1} R) k j).hom.app L) ≫
        (mapDerivedCategoryOpenImmersionLowerShriekComparisonUpperStarIso
          (ModuleCat.{u + 1} R) j).hom.app (f.mapDerivedCategory.obj L) ≫
        g'.mapDerivedCategory.map
          ((mapDerivedCategoryOpenImmersionLowerShriekComparisonUpperStarIso
            (ModuleCat.{u + 1} R) k).hom.app L) =
      (mapDerivedCategoryOpenImmersionLowerShriekComparisonUpperStarIso
        (ModuleCat.{u + 1} R) (k ≫ j)).hom.app L ≫
        (extensionComp R k j).hom.app ((E V).mapDerivedCategory.obj L) := by
    simpa only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
      Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Functor.associator_hom_app, Iso.symm_hom, Functor.associator_inv_app,
      Category.id_comp, Category.comp_id,
      mapDerivedCategoryOpenImmersionLowerShriekComparisonUpperStarIso,
      Etale.mapDerivedCategoryOpenImmersionLowerShriekComp, extensionComp, E, f, g, fg,
      f', g', fg'] using (congrArg (fun e ↦ e.hom.app L)
      (Functor.mapDerivedCategorySquareIso_comp
      (C₀ := Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} R))
      (C₁ := Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} R))
      (C₂ := Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R))
      (D₀ := Sheaf (Scheme.ProEt.topology V) (ModuleCat.{u + 1} R))
      (D₁ := Sheaf (Scheme.ProEt.topology U) (ModuleCat.{u + 1} R))
      (D₂ := Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} R))
      f g fg f' g' fg' (E V) (E U) (E X)
      (openImmersionLowerShriekComparisonUpperStarIso (ModuleCat.{u + 1} R) k)
      (openImmersionLowerShriekComparisonUpperStarIso (ModuleCat.{u + 1} R) j)
      (openImmersionLowerShriekComparisonUpperStarIso (ModuleCat.{u + 1} R) (k ≫ j))
      (Etale.openImmersionLowerShriekComp (ModuleCat.{u + 1} R) k j)
      (proEtaleOpenExtensionComp R k j) hq))
  have he := congrArg (fun t ↦ t ≫ (extensionComp R k j).inv.app
    ((E V).mapDerivedCategory.obj L)) hc
  simp only [Category.assoc, Iso.hom_inv_id_app] at he
  erw [Category.comp_id] at he
  simpa only [Category.assoc, Iso.hom_inv_id_app, Category.comp_id,
    mapDerivedCategoryOpenImmersionLowerShriekComparisonUpperStarIso,
    Etale.mapDerivedCategoryOpenImmersionLowerShriekComp, extensionComp, E, f, g, fg,
    f', g', fg'] using he


private lemma identity_comparison {C : Type*} [Category C]
    {F G : C ⥤ C} (a : F ⊣ G) (e : G ≅ 𝟭 C) :
    a.leftAdjointUniq (Adjunction.id.ofNatIsoRight e.symm) = a.leftAdjointIdIso e := by
  apply Iso.ext
  ext M : 2
  simp [Adjunction.leftAdjointUniq, Adjunction.leftAdjointIdIso,
    conjugateIsoEquiv, conjugateEquiv, Adjunction.ofNatIsoRight]

/-- Bounded flat complexes remain termwise flat and independent-coefficient K-flat
under open extension, on both sites. The pro-etale input is the actual comparison
pullback. The predicates are the recorded fixed-coefficient flat and K-flat predicates.
Source: Stacks 0GL1, 06YQ, 09AF (blueprint: lem-sp-open-scalar-site-coherence).
Proof (node step 1): use the flatness and K-flat preservation clauses of the
canonical etale open tensor comparison (lem-coef-etale-open-tensor). For pro-etale
flatness, identify the open extension of comparison pullback with comparison pullback
of etale extension by its canonical isomorphism (lem-cbc-proetale-extension-zero-comparison).
Constant-scalar realization reflects etale flatness (lem-pur-etale-constant-module-flat)
and comparison inverse image preserves ordinary flat sheaves
(lem-exc-constant-inverse-image-flat); the finite-coefficient realization lemma
(lem-sp-finite-coefficient-realization-flat) identifies the resulting flat sheaf with
its constant-ring coordinates. Exact additive functors preserve the upper degree bound,
and the bounded-above flat criterion (lem-weil-pbc-independent-bounded-flat-kflat)
gives K-flatness before etale extension and after pro-etale extension. -/
theorem extension_flat_kflat (A : Type (u + 1)) [CommRing A] [Finite A]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (P : CochainComplex (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
    (_hbounded : ∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (P.X n))
    (_hflat : ∀ n : ℤ, ObjectProperty.flat (P.X n)) :
    (∀ n : ℤ, ObjectProperty.flat
      ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) j).obj (P.X n))) ∧
    (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat
      (((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapHomologicalComplex
        (.up ℤ)).obj P) ∧
    (∀ n : ℤ, ObjectProperty.flat
      ((openImmersionLowerShriek (ModuleCat.{u + 1} A) j).obj
        ((comparisonUpperStar (ModuleCat.{u + 1} A) U).obj (P.X n)))) ∧
    (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat
      (((comparisonUpperStar (ModuleCat.{u + 1} A) U ⋙
        openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapHomologicalComplex
          (.up ℤ)).obj P) := by
  have hf : ∀ n : ℤ, ObjectProperty.flat
      ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) j).obj (P.X n)) :=
    fun n ↦ (Scheme.etaleConstantModule_flat_iff X A _).mpr
      ((Etale.etaleOpenTensorComparisons (RingHom.id A) j).flat_preserved _
        ((Scheme.etaleConstantModule_flat_iff U A _).mp (_hflat n)))
  have hg : ∀ n : ℤ, ObjectProperty.flat
      ((openImmersionLowerShriek (ModuleCat.{u + 1} A) j).obj
        ((comparisonUpperStar (ModuleCat.{u + 1} A) U).obj (P.X n))) := by
    intro n
    exact ObjectProperty.prop_of_iso ObjectProperty.flat
      ((openImmersionLowerShriekComparisonUpperStarIso
        (ModuleCat.{u + 1} A) j).app (P.X n))
      (flat_comparisonUpperStar_obj (hf n))
  obtain ⟨a, b, hb⟩ := _hbounded
  have hP : P.IsStrictlyLE b := (P.isStrictlyLE_iff b).2 (fun n hn ↦ hb n (Or.inr hn))
  refine ⟨hf, ?_, hg, ?_⟩
  · exact CochainComplex.kFlat_of_isStrictlyLE_of_flat _ b hf
  · exact CochainComplex.kFlat_of_isStrictlyLE_of_flat _ b hg

end AlgebraicGeometry.ProEtale.OpenScalarSiteCoherence
