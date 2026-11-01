/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.System.SystemEvaluationNormalizationData
import WeilConjectures.Algebra.Homology.SmoothPurity.ExtensionEvaluationComparison

/-! # The singleton comparison as an evaluation mate

Source: Stacks Project, Tags 03D2, 0D6E and 07A6; Zheng, Construction 4.1.
(blueprint: lem-route-system-singleton-evaluation-mate).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
universe u v u' v' w
open CategoryTheory CategoryTheory.Limits Opposite
attribute [local irreducible] Functor.mapDerivedCategory Functor.rightDerivedFunctor
  Functor.mapDerivedCategoryCompIso Functor.mapDerivedCategoryNatIso
  Adjunction.mapDerivedCategoryRightDerivedAdjunction
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem cachedRingCompose {T : Type*} [Category T]
    [EssentiallySmall.{w} T] (τ : GrothendieckTopology T) :
    τ.HasSheafCompose (CategoryTheory.forget RingCat.{w}) := inferInstance

private theorem cachedAddCompose {T : Type*} [Category T]
    [EssentiallySmall.{w} T] (τ : GrothendieckTopology T) :
    τ.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{w}) := inferInstance

attribute [local instance 20000] cachedRingCompose cachedAddCompose cachedCommCompose
attribute [local instance 20000] comp_preservesFiniteLimits comp_preservesFiniteColimits

private theorem cachedCommCompose {T : Type*} [Category T]
    [EssentiallySmall.{w} T] (τ : GrothendieckTopology T) :
    τ.HasSheafCompose (CategoryTheory.forget CommRingCat.{w}) := inferInstance

private theorem exactSquare_fac
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory A] [HasDerivedCategory B]
    [HasDerivedCategory C] [HasDerivedCategory D]
    {R : A ⥤ B} {G : B ⥤ D} {H : A ⥤ C} {S : C ⥤ D}
    [R.Additive] [G.Additive] [H.Additive] [S.Additive]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    [PreservesFiniteLimits S] [PreservesFiniteColimits S]
    (δ : R ⋙ G ≅ H ⋙ S) (K : CochainComplex A ℤ) :
    (Functor.mapDerivedCategorySquareIso δ).hom.app (DerivedCategory.Q.obj K) ≫
        S.mapDerivedCategory.map (H.mapDerivedCategoryFactors.hom.app K) ≫
        S.mapDerivedCategoryFactors.hom.app ((H.mapHomologicalComplex (.up ℤ)).obj K) =
      G.mapDerivedCategory.map (R.mapDerivedCategoryFactors.hom.app K) ≫
        G.mapDerivedCategoryFactors.hom.app ((R.mapHomologicalComplex (.up ℤ)).obj K) ≫
        DerivedCategory.Q.map ((δ.hom.mapHomologicalComplex (.up ℤ)).app K) := by
  have hc := Functor.mapDerivedCategoryCompIso_hom_app_factors R G K
  have hi : (Functor.mapDerivedCategoryCompIso R G).inv.app (DerivedCategory.Q.obj K) ≫
      (R ⋙ G).mapDerivedCategoryFactors.hom.app K =
    G.mapDerivedCategory.map (R.mapDerivedCategoryFactors.hom.app K) ≫
      G.mapDerivedCategoryFactors.hom.app ((R.mapHomologicalComplex (.up ℤ)).obj K) := by
    apply (cancel_epi
      ((Functor.mapDerivedCategoryCompIso R G).hom.app (DerivedCategory.Q.obj K))).mp
    rw [Iso.hom_inv_id_app_assoc]
    exact hc.symm
  simp only [Functor.mapDerivedCategorySquareIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Category.assoc]
  rw [Functor.mapDerivedCategoryCompIso_hom_app_factors,
    Functor.mapDerivedCategoryNatIso_fac]
  rw [← Category.assoc, hi, Category.assoc]


private theorem inverseSquare_eq {E : Type*} [Category E] {W X Y Z : E}
    (a : W ≅ X) (b : X ≅ Y) (c : W ≅ Z) (d : Z ≅ Y)
    (h : a.hom ≫ b.hom = c.hom ≫ d.hom) : b.inv ≫ a.inv = d.inv ≫ c.inv := by
  have h' : a ≪≫ b = c ≪≫ d := Iso.ext h
  exact congrArg Iso.inv h'

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [EssentiallySmall.{w} C]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]

variable {D : Type u'} [Category.{v'} D] {K : GrothendieckTopology D}
  [EssentiallySmall.{w} D]
  [K.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [K.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify K AddCommGrpCat.{w}]
  {BY : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}} {BX : ℕᵒᵖ ⥤ Sheaf K CommRingCat.{w}}
  {uTop : GeometricMorphism (Sheaf K (Type w)) (Sheaf J (Type w))}
  {I : ∀ n : ℕ, AlgebraicInverseImage uTop.inverse (BY.obj (op n)) (BX.obj (op n))}
  (SY : SystemScalarAssignment (J := J)) (TY : SystemTensorCoherence SY)
  (SX : SystemScalarAssignment (J := K)) (TX : SystemTensorCoherence SX)
  (F : SystemGeometricInverseImageData BY BX uTop I)

variable (H : StrictRingSystem BX ⥤ StrictRingSystem BY) [H.Additive]
  [Abelian.HasKInjectiveResolutions (StrictRingSystem BX)]
  (adj : F.functor ⊣ H)
  (Hn : ∀ n : ℕ, systemLevel BX n ⥤ systemLevel BY n)
  [∀ n : ℕ, (Hn n).Additive]
  [∀ n : ℕ, Abelian.HasKInjectiveResolutions (systemLevel BX n)]
  (adjn : ∀ n : ℕ, F.levelFunctor n ⊣ Hn n)

set_option maxHeartbeats 2000000 in
-- Comparing the normalized singleton packages exceeds the default elaboration budget.
end SheafOfModules
