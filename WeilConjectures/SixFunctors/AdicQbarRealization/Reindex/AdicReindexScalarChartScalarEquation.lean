/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.AdicQbarRealization.Reindex.AdicReindexScalarChartVertices
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import all Mathlib.CategoryTheory.Limits.HasLimits
import all WeilConjectures.AlgebraicGeometry.Pbc.PbcRationalAutomorphismScalarCoherence

/-! # Representative equations for scalar reindexing computation charts

Source: Stacks 06YY and 07A4; Bhatt--Scholze, Proposition 6.8.14.
(blueprint: lem-sf-adic-reindex-scalar-chart-scalar-equation).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
attribute [local irreducible] HasDerivedCategory.standard
  WeilConjectures.podCompletedRingMap
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale
namespace WeilConjectures.AdicQbarRealization
open AlgebraicallyClosedCoefficients (Index Coefficient coefficientInclusion)

section ScalarModel

private theorem exact_square {A B C D : Type*}
    [Category A] [Category B] [Category C] [Category D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory A] [HasDerivedCategory B]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F₁ : A ⥤ B) (F₂ : B ⥤ D) (G₁ : A ⥤ C) (G₂ : C ⥤ D)
    [F₁.Additive] [F₂.Additive] [G₁.Additive] [G₂.Additive]
    [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
    [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂]
    [PreservesFiniteLimits G₁] [PreservesFiniteColimits G₁]
    [PreservesFiniteLimits G₂] [PreservesFiniteColimits G₂]
    (e : F₁ ⋙ F₂ ≅ G₁ ⋙ G₂) (P : CochainComplex A ℤ) :
    (Functor.mapDerivedCategorySquareIso e).hom.app (DerivedCategory.Q.obj P) ≫
      G₂.mapDerivedCategory.map (G₁.mapDerivedCategoryFactors.hom.app P) ≫
      G₂.mapDerivedCategoryFactors.hom.app ((G₁.mapHomologicalComplex (.up ℤ)).obj P) =
    F₂.mapDerivedCategory.map (F₁.mapDerivedCategoryFactors.hom.app P) ≫
      F₂.mapDerivedCategoryFactors.hom.app ((F₁.mapHomologicalComplex (.up ℤ)).obj P) ≫
      DerivedCategory.Q.map ((NatIso.mapHomologicalComplex e (.up ℤ)).hom.app P) := by
  simp only [Functor.mapDerivedCategorySquareIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Category.assoc]
  rw [Functor.mapDerivedCategoryCompIso_hom_app_factors]
  erw [Functor.mapDerivedCategoryNatIso_fac]
  rw [← Functor.mapDerivedCategoryCompIso_hom_app_factors F₁ F₂ P]
  erw [Category.assoc, Iso.inv_hom_id_app_assoc, Category.assoc]
  rfl

private theorem inverse_transport {C D : Type*} [Category C] [Category D]
    {F G : C ⥤ D} (β : F ≅ G) {U V : C} (a : U ⟶ V)
    {W Z : D} (f : F.obj V ⟶ W) (g : G.obj V ⟶ Z) (b : W ≅ Z)
    (h : β.hom.app V ≫ g = f ≫ b.hom) :
    β.inv.app U ≫ F.map a ≫ f = G.map a ≫ g ≫ b.inv := by
  have hn := β.inv.naturality a
  have hr : β.inv.app V ≫ f = g ≫ b.inv := by
    have hh := congrArg (fun z ↦ β.inv.app V ≫ z ≫ b.inv) h
    simpa only [Category.assoc, Iso.inv_hom_id_app_assoc,
      Iso.hom_inv_id, Category.comp_id] using hh.symm
  calc
    _ = (β.inv.app U ≫ F.map a) ≫ f := by simp only [Category.assoc]
    _ = (G.map a ≫ β.inv.app V) ≫ f := by rw [← hn]
    _ = G.map a ≫ g ≫ b.inv := by rw [Category.assoc, hr]

private theorem paste_five {D : Type*} [Category D]
    {X₀ X₁ X₂ X₃ X₄ X₅ Y₀ Y₁ Y₂ Y₃ Y₄ Y₅ : D}
    (f₀ : X₀ ⟶ X₁) (f₁ : X₁ ⟶ X₂) (f₂ : X₂ ⟶ X₃)
    (f₃ : X₃ ⟶ X₄) (f₄ : X₄ ⟶ X₅)
    (q₀ : X₀ ⟶ Y₀) (q₁ : X₁ ⟶ Y₁) (q₂ : X₂ ⟶ Y₂)
    (q₃ : X₃ ⟶ Y₃) (q₄ : X₄ ⟶ Y₄) (q₅ : X₅ ⟶ Y₅)
    (c₀ : Y₀ ⟶ Y₁) (c₁ : Y₁ ⟶ Y₂) (c₂ : Y₂ ⟶ Y₃)
    (c₃ : Y₃ ⟶ Y₄) (c₄ : Y₄ ⟶ Y₅)
    (h₀ : f₀ ≫ q₁ = q₀ ≫ c₀) (h₁ : f₁ ≫ q₂ = q₁ ≫ c₁)
    (h₂ : f₂ ≫ q₃ = q₂ ≫ c₂) (h₃ : f₃ ≫ q₄ = q₃ ≫ c₃)
    (h₄ : f₄ ≫ q₅ = q₄ ≫ c₄) :
    f₀ ≫ f₁ ≫ f₂ ≫ f₃ ≫ f₄ ≫ q₅ = q₀ ≫ c₀ ≫ c₁ ≫ c₂ ≫ c₃ ≫ c₄ := by
  rw [h₄, ← Category.assoc f₃ q₄ c₄, h₃]
  simp only [Category.assoc]
  rw [← Category.assoc f₂ q₃ (c₃ ≫ c₄), h₂]
  simp only [Category.assoc]
  rw [← Category.assoc f₁ q₂ (c₂ ≫ c₃ ≫ c₄), h₁]
  simp only [Category.assoc]
  rw [← Category.assoc f₀ q₁ (c₁ ≫ c₂ ≫ c₃ ≫ c₄), h₀]
  simp only [Category.assoc]

private theorem assoc_five {D : Type*} [Category D] {A B C E F G : D}
    (f : A ⟶ B) (g : B ⟶ C) (h : C ⟶ E) (i : E ⟶ F) (j : F ⟶ G) :
    f ≫ g ≫ h ≫ i ≫ j = (f ≫ g ≫ h ≫ i) ≫ j := by simp only [Category.assoc]

private theorem naturality_square {C D : Type*} [Category C] [Category D]
    {F G : C ⥤ D} (β : F ≅ G) {U V : C} (a : U ⟶ V)
    {W : D} (q : G.obj V ⟶ W) (r : F.obj V ⟶ W)
    (h : β.hom.app V ≫ q = r) :
    β.hom.app U ≫ G.map a ≫ q = F.map a ≫ r := by
  rw [← Category.assoc, ← β.hom.naturality a, Category.assoc, h]

private theorem map_square {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {X A B C₁ Y A' B' C' : C} {U V : D}
    (f₀ : X ⟶ A) (f₁ : A ⟶ B) (f₂ : B ⟶ C₁) (f₃ : C₁ ⟶ Y)
    (g₀ : X ⟶ A') (g₁ : A' ⟶ B') (g₂ : B' ⟶ C') (g₃ : C' ⟶ Y)
    (ε : F.obj Y ⟶ V) (ε' : F.obj C' ⟶ U) (c : U ⟶ V)
    (h : f₀ ≫ f₁ ≫ f₂ ≫ f₃ = g₀ ≫ g₁ ≫ g₂ ≫ g₃)
    (hc : F.map g₃ ≫ ε = ε' ≫ c) :
    F.map f₀ ≫ F.map f₁ ≫ F.map f₂ ≫ F.map f₃ ≫ ε =
      F.map g₀ ≫ F.map g₁ ≫ F.map g₂ ≫ ε' ≫ c := by
  have hh := congrArg (fun z ↦ F.map z ≫ ε) h
  simpa only [Functor.map_comp, Category.assoc, hc] using hh

variable (l : ℕ) [Fact l.Prime]
    (E L : Type u) [Field E] [Field L]
    [Algebra (Padic l) E] [Algebra (Padic l) L]
    [FiniteDimensional (Padic l) E] [FiniteDimensional (Padic l) L]
    (i : E →ₐ[Padic l] L)

private theorem scalar_model (W : Scheme.{u})
    (P : CochainComplex (integralTowerModules l E W) ℤ) :
    (scalarExactModel l E L i W).hom.app (DerivedCategory.Q.obj P) ≫
      completedScalarCounit l E L i W P =
    (integralOrdinaryScalar l E L i W).mapDerivedCategoryFactors.hom.app P ≫
      DerivedCategory.Q.map ((NatIso.mapHomologicalComplex
        (isomorphismScalarSheafModel l E L i W) (.up ℤ)).hom.app P) :=
  (isomorphismScalarModel_existsUnique l E L i W).exists.choose_spec.1 P

private instance inverseImage_additive {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g] :
    (inverseImageIntegralModules l E g).Additive :=
  Functor.additive_of_iso (completedReindexSheafModel l E g)

private instance inverseImage_limits {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g] :
    PreservesFiniteLimits (inverseImageIntegralModules l E g) :=
  preservesFiniteLimits_of_natIso (completedReindexSheafModel l E g)

private instance inverseImage_colimits {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g] :
    PreservesFiniteColimits (inverseImageIntegralModules l E g) :=
  preservesFiniteColimits_of_natIso (completedReindexSheafModel l E g)

private theorem reindex_model {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g] :
    completedReindexModel l E g =
      Functor.mapDerivedCategoryNatIso (completedReindexSheafModel l E g) := by
  unfold completedReindexModel completedReindexSheafModel
  rfl

set_option maxHeartbeats 800000 in
-- Paste the five exact-derived and scalar-model factorization equations.
private theorem scalar_inner {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    (P : CochainComplex (integralTowerModules l E Y) ℤ) :
    (completedScalarReindex l E L i g).hom.app (DerivedCategory.Q.obj P) ≫
      (podCompletedDerivedInverseImage l L g).map (completedScalarCounit l E L i Y P) ≫
      (podCompletedModuleInverseImage l L g).mapDerivedCategoryFactors.hom.app
        ((completedOrdinaryScalarComplex l E L i Y).obj P) =
    (completedDerivedScalarExtension l E L i X).map
        ((podCompletedModuleInverseImage l E g).mapDerivedCategoryFactors.hom.app P) ≫
      completedScalarCounit l E L i X
        (((podCompletedModuleInverseImage l E g).mapHomologicalComplex (.up ℤ)).obj P) ≫
      DerivedCategory.Q.map ((NatIso.mapHomologicalComplex
        (completedScalarSheafReindex l E L i g) (.up ℤ)).hom.app P) := by
  dsimp only [podCompletedDerivedInverseImage, Functor.comp_obj]
  let HE := podCompletedModuleInverseImage l E g
  let HL := podCompletedModuleInverseImage l L g
  let GE := inverseImageIntegralModules l E g
  let Glarge := inverseImageIntegralModules l L g
  let FX := integralOrdinaryScalar l E L i X
  let FY := integralOrdinaryScalar l E L i Y
  let TX := completedDerivedScalarExtension l E L i X
  let TY := completedDerivedScalarExtension l E L i Y
  let esX := isomorphismScalarSheafModel l E L i X
  let esY := isomorphismScalarSheafModel l E L i Y
  let erE := completedReindexSheafModel l E g
  let erL := completedReindexSheafModel l L g
  let sX := scalarExactModel l E L i X
  let sY := scalarExactModel l E L i Y
  let rE := completedReindexModel l E g
  let rL := completedReindexModel l L g
  let QHE := (HE.mapHomologicalComplex (.up ℤ)).obj P
  let QGE := (GE.mapHomologicalComplex (.up ℤ)).obj P
  let QFY := (FY.mapHomologicalComplex (.up ℤ)).obj P
  let QTY := (completedOrdinaryScalarComplex l E L i Y).obj P
  let q₀ := TX.map (HE.mapDerivedCategoryFactors.hom.app P) ≫
    completedScalarCounit l E L i X QHE
  let q₁ := FX.mapDerivedCategory.map (HE.mapDerivedCategoryFactors.hom.app P) ≫
    FX.mapDerivedCategoryFactors.hom.app QHE
  let q₂ := FX.mapDerivedCategory.map (GE.mapDerivedCategoryFactors.hom.app P) ≫
    FX.mapDerivedCategoryFactors.hom.app QGE
  let q₃ := Glarge.mapDerivedCategory.map (FY.mapDerivedCategoryFactors.hom.app P) ≫
    Glarge.mapDerivedCategoryFactors.hom.app QFY
  let q₄ := HL.mapDerivedCategory.map (FY.mapDerivedCategoryFactors.hom.app P) ≫
    HL.mapDerivedCategoryFactors.hom.app QFY
  let q₅ := HL.mapDerivedCategory.map (completedScalarCounit l E L i Y P) ≫
    HL.mapDerivedCategoryFactors.hom.app QTY
  let c₀ := DerivedCategory.Q.map ((NatIso.mapHomologicalComplex esX (.up ℤ)).inv.app QHE)
  let c₁ := DerivedCategory.Q.map ((FX.mapHomologicalComplex (.up ℤ)).map
    ((NatIso.mapHomologicalComplex erE (.up ℤ)).hom.app P))
  let c₂ := DerivedCategory.Q.map ((NatIso.mapHomologicalComplex
    (isomorphismScalarTensor l E L i g) (.up ℤ)).hom.app P)
  let c₃ := DerivedCategory.Q.map ((NatIso.mapHomologicalComplex erL (.up ℤ)).inv.app QFY)
  let c₄ := DerivedCategory.Q.map ((HL.mapHomologicalComplex (.up ℤ)).map
    ((NatIso.mapHomologicalComplex esY (.up ℤ)).hom.app P))
  have h₀ : sX.inv.app ((podCompletedDerivedInverseImage l E g).obj
      (DerivedCategory.Q.obj P)) ≫ q₁ = q₀ ≫ c₀ := by
    have hh := inverse_transport sX (HE.mapDerivedCategoryFactors.hom.app P)
      (FX.mapDerivedCategoryFactors.hom.app QHE)
      (completedScalarCounit l E L i X QHE)
      (DerivedCategory.Q.mapIso ((NatIso.mapHomologicalComplex esX (.up ℤ)).app QHE))
      (scalar_model l E L i X QHE)
    dsimp only [Functor.mapIso, Iso.app] at hh
    dsimp only [q₀, q₁, c₀, HE, FX, TX, podCompletedDerivedInverseImage,
      integralOrdinaryDerivedScalar, Functor.comp_obj, Functor.mapIso_inv, Iso.app_inv,
      Functor.comp_obj] at hh ⊢
    erw [Category.assoc]
    exact hh
  have h₁ : FX.mapDerivedCategory.map (rE.hom.app (DerivedCategory.Q.obj P)) ≫ q₂ =
      q₁ ≫ c₁ := by
    have he := Functor.mapDerivedCategoryNatIso_fac erE P
    have hn := FX.mapDerivedCategoryFactors.hom.naturality
      ((NatIso.mapHomologicalComplex erE (.up ℤ)).hom.app P)
    dsimp only [Functor.comp_map] at hn
    rw [show rE = Functor.mapDerivedCategoryNatIso erE from reindex_model l E g]
    dsimp only [q₁, q₂, c₁]
    rw [← FX.mapDerivedCategory.map_comp_assoc]
    change FX.mapDerivedCategory.map
      ((Functor.mapDerivedCategoryNatIso erE).hom.app (DerivedCategory.Q.obj P) ≫
        GE.mapDerivedCategoryFactors.hom.app P) ≫ _ = _
    rw [he, FX.mapDerivedCategory.map_comp]
    simpa only [HE, GE, QHE, QGE, Functor.comp_obj,
      NatIso.mapHomologicalComplex, Category.assoc] using
      congrArg (fun z ↦ FX.mapDerivedCategory.map
        (HE.mapDerivedCategoryFactors.hom.app P) ≫ z) hn
  have h₂ : (isomorphismScalarTensorDerived l E L i g).hom.app
      (DerivedCategory.Q.obj P) ≫ q₃ = q₂ ≫ c₂ := by
    have hh := exact_square GE FX FY Glarge (isomorphismScalarTensor l E L i g) P
    dsimp only [q₂, q₃, c₂, QFY, QGE]
    have hassoc := Category.assoc
      (FX.mapDerivedCategory.map (GE.mapDerivedCategoryFactors.hom.app P))
      (FX.mapDerivedCategoryFactors.hom.app QGE) c₂
    exact hh.trans hassoc.symm
  have h₃ : rL.inv.app (FY.mapDerivedCategory.obj (DerivedCategory.Q.obj P)) ≫ q₄ =
      q₃ ≫ c₃ := by
    have he := Functor.mapDerivedCategoryNatIso_fac erL.symm QFY
    rw [Functor.mapDerivedCategoryNatIso_symm] at he
    have hn := rL.inv.naturality (FY.mapDerivedCategoryFactors.hom.app P)
    dsimp only [podCompletedDerivedInverseImage, inverseImageIntegralDerived,
      Functor.comp_obj] at hn
    dsimp only [q₃, q₄, c₃]
    erw [← Category.assoc, ← hn, Category.assoc]
    rw [show rL = Functor.mapDerivedCategoryNatIso erL from reindex_model l L g]
    change Glarge.mapDerivedCategory.map (FY.mapDerivedCategoryFactors.hom.app P) ≫
      (Functor.mapDerivedCategoryNatIso erL).inv.app (DerivedCategory.Q.obj QFY) ≫
      HL.mapDerivedCategoryFactors.hom.app QFY = _
    rw [he]
    simp only [Category.assoc]
    rfl
  have h₄ : HL.mapDerivedCategory.map (sY.hom.app (DerivedCategory.Q.obj P)) ≫ q₅ =
      q₄ ≫ c₄ := by
    have he := congrArg HL.mapDerivedCategory.map (scalar_model l E L i Y P)
    have hn := HL.mapDerivedCategoryFactors.hom.naturality
      ((NatIso.mapHomologicalComplex esY (.up ℤ)).hom.app P)
    dsimp only [Functor.comp_map] at hn
    dsimp only [q₄, q₅, c₄]
    rw [← HL.mapDerivedCategory.map_comp_assoc]
    change HL.mapDerivedCategory.map
      ((scalarExactModel l E L i Y).hom.app (DerivedCategory.Q.obj P) ≫
        completedScalarCounit l E L i Y P) ≫ _ = _
    rw [he]
    erw [HL.mapDerivedCategory.map_comp]
    simp only [Category.assoc]
    dsimp only [QTY, completedOrdinaryScalarComplex, FY, esY, QFY] at hn ⊢
    rw [hn]
  have hpaste :
      sX.inv.app ((podCompletedDerivedInverseImage l E g).obj (DerivedCategory.Q.obj P)) ≫
      FX.mapDerivedCategory.map (rE.hom.app (DerivedCategory.Q.obj P)) ≫
      (isomorphismScalarTensorDerived l E L i g).hom.app (DerivedCategory.Q.obj P) ≫
      rL.inv.app (FY.mapDerivedCategory.obj (DerivedCategory.Q.obj P)) ≫
      HL.mapDerivedCategory.map (sY.hom.app (DerivedCategory.Q.obj P)) ≫ q₅ =
      q₀ ≫ c₀ ≫ c₁ ≫ c₂ ≫ c₃ ≫ c₄ := by
    exact paste_five _ _ _ _ _ q₀ q₁ q₂ q₃ q₄ q₅ c₀ c₁ c₂ c₃ c₄ h₀ h₁ h₂ h₃ h₄
  have hc : DerivedCategory.Q.map ((NatIso.mapHomologicalComplex
      (completedScalarSheafReindex l E L i g) (.up ℤ)).hom.app P) =
      c₀ ≫ c₁ ≫ c₂ ≫ c₃ ≫ c₄ := by
    dsimp only [c₀, c₁, c₂, c₃, c₄]
    erw [← DerivedCategory.Q.map_comp, ← DerivedCategory.Q.map_comp,
      ← DerivedCategory.Q.map_comp, ← DerivedCategory.Q.map_comp]
    apply congrArg DerivedCategory.Q.map
    apply HomologicalComplex.hom_ext
    intro n
    rfl
  erw [hc]
  simp only [q₀, q₅, FX, FY, HL, sX, sY, rE, rL, QHE, QTY,
    podCompletedDerivedInverseImage, integralOrdinaryDerivedScalar,
    completedScalarReindex, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.comp_obj, TX, HE, Iso.symm_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Category.assoc,
    Functor.isoWhiskerRight_hom] at hpaste ⊢
  with_unfolding_all exact hpaste

end ScalarModel

set_option maxHeartbeats 800000 in
-- Elaborate the two nested scalar/inverse-image chart comparisons.
/-- The scalar-reindexing edge for the specified counit maps.
Source: Stacks 06YY; BS 6.8.14--6.8.15.
(blueprint: lem-sf-adic-reindex-scalar-chart-scalar-equation).

Proof in words: expand the five factors defining completedScalarReindex. Use the
scalarExactModel counit normalization for the scalar factors and the exact-derived
factorization equations for the inverse-image factors. The central exact-derived
square is the localization of isomorphismScalarTensor. Paste the five squares,
apply naturality of the native scalar counit, and transport along e.inv. These
are exactly the specified comparison maps, with no arbitrary vertex choices.
-/
theorem adic_scalar_chart_scalar_equation (l : ℕ) [Fact l.Prime]
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    (R : LocallyFiniteAdicRealization.Realization l X)
    (S : LocallyFiniteAdicRealization.Realization l Y)
    (B : RingReindex l X g R S)
    (E L : Index l (PadicAlgCl l)) (h : E ≤ L)
    (be : pbcExtend (coefficientMap l Y S E) ⋙ modulePull l X g B ≅
      podCompletedModuleInverseImage l (Coefficient.{u} l (PadicAlgCl l) E) g ⋙
        pbcExtend (coefficientMap l X R E))
    (bl : pbcExtend (coefficientMap l Y S L) ⋙ modulePull l X g B ≅
      podCompletedModuleInverseImage l (Coefficient.{u} l (PadicAlgCl l) L) g ⋙
        pbcExtend (coefficientMap l X R L))
    (de : pbcDerivedExtend (coefficientMap l Y S E) ⋙ derivedPull l X g B ≅
      podCompletedDerivedInverseImage l (Coefficient.{u} l (PadicAlgCl l) E) g ⋙
        pbcDerivedExtend (coefficientMap l X R E))
    (dl : pbcDerivedExtend (coefficientMap l Y S L) ⋙ derivedPull l X g B ≅
      podCompletedDerivedInverseImage l (Coefficient.{u} l (PadicAlgCl l) L) g ⋙
        pbcDerivedExtend (coefficientMap l X R L))
    (K : DerivedCategory (integralTowerModules l (Coefficient.{u} l (PadicAlgCl l) E) Y))
    (P : CochainComplex (integralTowerModules l (Coefficient.{u} l (PadicAlgCl l) E) Y) ℤ)
    (e : DerivedCategory.Q.obj P ≅ K)
    (hp : CochainComplex.IsKFlatIndependentCoefficients
      (R := completedIntegralCommRingSheafUnrestricted l
        (Coefficient.{u} l (PadicAlgCl l) E) Y) P)
    (hf : ∀ n : ℤ, SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
      (R := completedIntegralCommRingSheafUnrestricted l
        (Coefficient.{u} l (PadicAlgCl l) E) Y) (P.X n)) :
    (adicScalarChartVertices l g R S B E L h be bl de dl K P e hp hf).scalarEquation := by
  let A := Coefficient.{u} l (PadicAlgCl l) E
  let C := Coefficient.{u} l (PadicAlgCl l) L
  let i := coefficientInclusion l (PadicAlgCl l) E L h
  let HE := podCompletedModuleInverseImage l A g
  let HL := podCompletedModuleInverseImage l C g
  let TX := completedDerivedScalarExtension l A C i X
  let TY := completedDerivedScalarExtension l A C i Y
  let rL := pbcDerivedExtend (coefficientMap l X R L)
  let δ := completedScalarReindex l A C i g
  let QHE := (HE.mapHomologicalComplex (.up ℤ)).obj P
  let QTY := (completedOrdinaryScalarComplex l A C i Y).obj P
  let a := (NatIso.mapHomologicalComplex
    (completedScalarSheafReindex l A C i g) (.up ℤ)).hom.app P
  have hinner := scalar_inner l A C i g P
  have hn := δ.hom.naturality e.inv
  dsimp only [Functor.comp_map] at hn
  have ht := naturality_square δ e.inv
    ((podCompletedDerivedInverseImage l C g).map (completedScalarCounit l A C i Y P) ≫
      HL.mapDerivedCategoryFactors.hom.app QTY)
    (TX.map (HE.mapDerivedCategoryFactors.hom.app P) ≫
      completedScalarCounit l A C i X QHE ≫ DerivedCategory.Q.map a) hinner
  dsimp only [Functor.comp_map] at ht
  have hc := (AlgebraicGeometry.Scheme.tensorComplexCounit
    (coefficientMap l X R L)).naturality a
  dsimp only [Functor.comp_map, AlgebraicGeometry.Scheme.tensorComplexCounit] at hc
  have hh := map_square rL (δ.hom.app K)
    ((podCompletedDerivedInverseImage l C g).map (TY.map e.inv))
    ((podCompletedDerivedInverseImage l C g).map (completedScalarCounit l A C i Y P))
    (HL.mapDerivedCategoryFactors.hom.app QTY)
    (TX.map ((podCompletedDerivedInverseImage l A g).map e.inv))
    (TX.map (HE.mapDerivedCategoryFactors.hom.app P))
    (completedScalarCounit l A C i X QHE) (DerivedCategory.Q.map a)
    (pbcComplexCounit (coefficientMap l X R L)
      ((HL.mapHomologicalComplex (.up ℤ)).obj QTY))
    (pbcComplexCounit (coefficientMap l X R L)
      ((completedOrdinaryScalarComplex l A C i X).obj QHE))
    (DerivedCategory.Q.map (((pbcExtend (coefficientMap l X R L)).mapHomologicalComplex
      (.up ℤ)).map a)) (by
        simpa only [Functor.comp_map, Category.assoc] using ht)
      (by with_unfolding_all exact hc)
  simp only [ScalarComputationChartVertices.scalarEquation, adicScalarChartVertices,
    adicScalarChartMap₁, adicScalarChartMap₂] at ⊢
  dsimp only [asIso]
  dsimp only [rL, δ, HE, HL, TX, TY, QHE, QTY, a, A, C, i] at hh
  refine hh.trans ?_
  exact assoc_five _ _ _ _ _

end WeilConjectures.AdicQbarRealization
