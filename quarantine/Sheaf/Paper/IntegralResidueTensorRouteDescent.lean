/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.IntegralResidueTensorModel

/-! Descent of the tensor-route computation from resolving representatives.
Source: Bhatt--Scholze, Lemma 6.5.9(3), Remark 6.8.15.
(blueprint: new-integral-residue-tensor-route-descent)

The statement isolates the naturality and essential-surjectivity step. -/

@[expose] public section

universe v u u₁ u₂

open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor

private theorem descend_natTrans_app {K C D : Type*}
    [Category* K] [Category* C] [Category* D]
    (Q : K ⥤ C) (G : C ⥤ D) (T : K ⥤ D) (α β : Q ⋙ G ⟶ T)
    {P R : K} (w : R ⟶ P) (hw : IsIso (Q.map w)) (h : α.app R = β.app R) :
    α.app P = β.app P := by
  let := hw
  have : IsIso ((Q ⋙ G).map w) := Functor.map_isIso G (Q.map w)
  apply (cancel_epi ((Q ⋙ G).map w)).mp
  rw [α.naturality, β.naturality, h]

noncomputable section TensorModelNaturality
variable {C : Type u₁} [Category.{v + 1} C] [Abelian C] [IsGrothendieckAbelian.{v + 1} C]
  [MonoidalCategory C] [MonoidalClosed C] [MonoidalPreadditive C] [BraidedCategory C]
  [Abelian.HasFunctorialFlatResolution C]
  {D : Type u₂} [Category.{v + 1} D] [Abelian D] [IsGrothendieckAbelian.{v + 1} D]
  [MonoidalCategory D] [MonoidalClosed D] [MonoidalPreadditive D] [BraidedCategory D]
  [Abelian.HasFunctorialFlatResolution D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
local instance : BraidedCategory (DerivedCategory D) :=
  CategoryTheory.derivedTensorPresentationBraiding
variable (G : DerivedCategory C ⥤ DerivedCategory D)
  (γ : DerivedCategory.Qh ⋙ G ⟶ F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
private def targetNat (B : C) :
    DerivedCategory.Qh ⋙ G ⋙
        tensorRight (G.obj ((DerivedCategory.singleFunctor C 0).obj B)) ⟶
      F.mapHomotopyCategory (.up ℤ) ⋙
        tensorLeft ((F.mapHomotopyCategory (.up ℤ)).obj (Functor.tensorModelCoefficient B)) ⋙
          DerivedCategory.Qh :=
  Functor.whiskerLeft (DerivedCategory.Qh ⋙ G)
      (BraidedCategory.tensorLeftIsoTensorRight
        (G.obj ((DerivedCategory.singleFunctor C 0).obj B))).inv ≫
    Functor.whiskerLeft (DerivedCategory.Qh ⋙ G)
      ((curriedTensor (DerivedCategory D)).map
        (G.map (Functor.tensorModelCoefficientIso B).hom ≫
          γ.app (Functor.tensorModelCoefficient B))) ≫
    Functor.whiskerRight γ
      (tensorLeft (DerivedCategory.Qh.obj
        ((F.mapHomotopyCategory (.up ℤ)).obj (Functor.tensorModelCoefficient B)))) ≫
    Functor.whiskerLeft (F.mapHomotopyCategory (.up ℤ))
      ((Functor.LaxMonoidal.μNatTrans DerivedCategory.Qh).app
        ((F.mapHomotopyCategory (.up ℤ)).obj (Functor.tensorModelCoefficient B)))
omit [MonoidalCategory C] [MonoidalClosed C] [MonoidalPreadditive C] [BraidedCategory C]
  [Abelian.HasFunctorialFlatResolution C] [PreservesFiniteLimits F]
  [PreservesFiniteColimits F] in
private theorem targetNat_app (B : C) (P : HomotopyCategory C (.up ℤ)) :
    (targetNat F G γ B).app P = Functor.tensorModelTargetWith F G γ B P := by
  unfold targetNat Functor.tensorModelTargetWith
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    BraidedCategory.tensorLeftIsoTensorRight, curriedTensor_map_app, curriedTensor_obj_map,
    Category.assoc, MonoidalCategory.tensorHom_def]
  rfl
variable [F.IsLeftAdjoint] [F.Monoidal]
private def mapNat (B : C) (H : DerivedCategory C ⥤ DerivedCategory C)
    (ε : DerivedCategory.Qh ⋙ H ⟶
      (tensorLeft B).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh) :
    DerivedCategory.Qh ⋙ H ⋙ G ⟶
      F.mapHomotopyCategory (.up ℤ) ⋙
        tensorLeft ((F.mapHomotopyCategory (.up ℤ)).obj (Functor.tensorModelCoefficient B)) ⋙
          DerivedCategory.Qh :=
  Functor.whiskerRight ε G ≫
    Functor.whiskerLeft ((tensorLeft B).mapHomotopyCategory (.up ℤ))
      γ ≫
    Functor.whiskerRight
      (Functor.whiskerRight (homotopyTensorSingleIso B).inv
          (F.mapHomotopyCategory (.up ℤ)) ≫
        (Functor.OplaxMonoidal.mapHomotopyCategoryδNatTrans (.up ℤ) F).app
          (Functor.tensorModelCoefficient B)) DerivedCategory.Qh
omit [Abelian.HasFunctorialFlatResolution C] [Abelian.HasFunctorialFlatResolution D]
  [PreservesFiniteLimits F]
  [PreservesFiniteColimits F] in
private theorem mapNat_app (B : C) (H : DerivedCategory C ⥤ DerivedCategory C)
    (ε : DerivedCategory.Qh ⋙ H ⟶
      (tensorLeft B).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (P : HomotopyCategory C (.up ℤ)) :
    (mapNat F G γ B H ε).app P = Functor.tensorModelMapWith F G γ B H ε P := by
  simp only [mapNat, Functor.tensorModelMapWith, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.map_comp]

omit [PreservesFiniteLimits F] [PreservesFiniteColimits F] in
private theorem tensorRoute_descend [F.PreservesFlat] (B : C)
    (H : DerivedCategory C ⥤ DerivedCategory C)
    (ε : DerivedCategory.Qh ⋙ H ⟶
      (tensorLeft B).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (e : H ≅ tensorRight ((DerivedCategory.singleFunctor C 0).obj B))
    (m : G.Monoidal)
    (hRoute : ∀ P, F.kFlatMap P →
      (letI := m
       G.map (e.hom.app (DerivedCategory.Qh.obj P)) ≫
          Functor.OplaxMonoidal.δ G (DerivedCategory.Qh.obj P)
            ((DerivedCategory.singleFunctor C 0).obj B) ≫ Functor.tensorModelTargetWith F G γ B P =
        Functor.tensorModelMapWith F G γ B H ε P)) :
    ∀ P, letI := m
      G.map (e.hom.app (DerivedCategory.Qh.obj P)) ≫
          Functor.OplaxMonoidal.δ G (DerivedCategory.Qh.obj P)
            ((DerivedCategory.singleFunctor C 0).obj B) ≫ Functor.tensorModelTargetWith F G γ B P =
        Functor.tensorModelMapWith F G γ B H ε P := by
  let := m
  let α := Functor.whiskerLeft DerivedCategory.Qh
      (Functor.whiskerRight e.hom G ≫
        (Functor.Monoidal.commTensorRight G
          ((DerivedCategory.singleFunctor C 0).obj B)).inv) ≫ targetNat F G γ B
  let β := mapNat F G γ B H ε
  have hα (P) : α.app P =
      G.map (e.hom.app (DerivedCategory.Qh.obj P)) ≫
          Functor.OplaxMonoidal.δ G (DerivedCategory.Qh.obj P)
            ((DerivedCategory.singleFunctor C 0).obj B) ≫
          Functor.tensorModelTargetWith F G γ B P := by
    simp only [α, NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.Monoidal.commTensorRight_inv_app, targetNat_app, Category.assoc]
  intro P
  obtain ⟨R⟩ := LocalizerMorphism.IsLeftDerivabilityStructure.hasLeftResolutions
    (Φ := HomotopyCategory.quasiIsoLocalizerMorphism F.kFlatMap) P
  let w : R.X₁.obj ⟶ P := R.w
  have hw : IsIso (DerivedCategory.Qh.map w) :=
    Localization.inverts DerivedCategory.Qh (HomotopyCategory.quasiIso _ _) _ R.hw
  have h : α.app R.X₁.obj = β.app R.X₁.obj := by
    rw [hα, mapNat_app]
    exact hRoute R.X₁.obj R.X₁.property
  have heq : α.app P = β.app P :=
    descend_natTrans_app DerivedCategory.Qh (H ⋙ G) _ α β w hw h
  exact (hα P).symm.trans (heq.trans (mapNat_app F G γ B H ε P))

end TensorModelNaturality

local instance : EssentiallySmall.{u + 1} Profinite.{u} := essentiallySmallSelf.{0} _

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]

attribute [local irreducible] Functor.leftDerivedFunctor Functor.mapDerivedCategory
  Mod.tensorPresentationDerivedCounit Functor.tensorModelMap

/-- Descent of a natural tensor-route equality from K-flat pullback models.
Source: Bhatt--Scholze, Lemma 6.5.9(3), Remark 6.8.15.
(blueprint: new-integral-residue-tensor-route-descent)

Choose a K-flat left resolution `w : R ⟶ P` in the homotopy category.
The two routes are components of natural transformations with a common source
that factors through `Qh`. Apply the hypothesis at `R`, use naturality along
`w`, and cancel its invertible source image. No factorization of the ordinary
tensor-model target through the derived category is needed. -/
theorem integralResidue_tensorRoute_descend {X Y : Scheme.{u}} (f : X ⟶ Y)
    (m : (f)^*⟦integralCoeff ℓ E⟧.Monoidal)
    (hFlat : (f)^*⟦integralCoeff ℓ E⟧.PreservesFlat)
    (hRoute : ∀ P : HomotopyCategory
      (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
        (condensedRingObj (integralCoeff ℓ E) Y)) (.up ℤ),
      ((f)^*⟦integralCoeff ℓ E⟧).kFlatMap P →
      (letI := residueExchangePullMonoidal ℓ E f m hFlat
       (residueExchangeUpperStar (integralCoeff ℓ E) f).map
            ((residueExchangeTensorIso ℓ E Y).hom.app (DerivedCategory.Qh.obj P)) ≫
          Functor.OplaxMonoidal.δ (residueExchangeUpperStar (integralCoeff ℓ E) f)
            (DerivedCategory.Qh.obj P) (residueExchangeCoefficient ℓ E Y) ≫
          residueExchangeTensorModelTarget ℓ E f P =
        residueExchangeTensorModelMap ℓ E f P)) :
    ∀ P : HomotopyCategory
      (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
        (condensedRingObj (integralCoeff ℓ E) Y)) (.up ℤ),
      letI := residueExchangePullMonoidal ℓ E f m hFlat
      (residueExchangeUpperStar (integralCoeff ℓ E) f).map
            ((residueExchangeTensorIso ℓ E Y).hom.app (DerivedCategory.Qh.obj P)) ≫
          Functor.OplaxMonoidal.δ (residueExchangeUpperStar (integralCoeff ℓ E) f)
            (DerivedCategory.Qh.obj P) (residueExchangeCoefficient ℓ E Y) ≫
          residueExchangeTensorModelTarget ℓ E f P =
        residueExchangeTensorModelMap ℓ E f P := by
  let := residueExchangeOrdinaryPullMonoidal ℓ E f
  let := hFlat
  let H := residueExchangeReduction ℓ E Y ⋙ residueExchangeRestriction ℓ E Y
  let B := residueExchangeOrdinaryCoefficient ℓ E Y
  let ε := residueExchangeTensorCounit ℓ E Y
  have h := tensorRoute_descend (f)^*⟦integralCoeff ℓ E⟧
    (residueExchangeUpperStar (integralCoeff ℓ E) f)
    (residueExchangeUpperStarCounit (integralCoeff ℓ E) f) B H ε
    (residueExchangeTensorIso ℓ E Y) (residueExchangePullMonoidal ℓ E f m hFlat)
  unfold residueExchangeTensorModelTarget residueExchangeTensorModelMap at hRoute ⊢
  exact h hRoute

end AlgebraicGeometry.ProEtale.CondensedRing
