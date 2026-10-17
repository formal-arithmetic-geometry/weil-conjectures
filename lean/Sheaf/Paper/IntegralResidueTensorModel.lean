/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.IntegralResidueTensorPresentation
public import Sheaf.Paper.IntegralResidueOrdinaryMonoidal
public import Sheaf.Paper.IntegralResidueDerivedMonoidal

/-! # A common homotopy-level model for the residue tensor square

Source: Bhatt--Scholze, Lemma 6.5.9(3), Remark 6.8.15.
(blueprint: new-integral-residue-tensor-model)
-/

@[expose] public section

noncomputable section

universe v u u₁ u₂
open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace CategoryTheory.Functor

variable {C : Type u₁} [Category.{v + 1} C] [Abelian C] [IsGrothendieckAbelian.{v + 1} C]
  [MonoidalCategory C] [MonoidalClosed C] [MonoidalPreadditive C] [BraidedCategory C]
  [Abelian.HasFunctorialFlatResolution C]
  {D : Type u₂} [Category.{v + 1} D] [Abelian D] [IsGrothendieckAbelian.{v + 1} D]
  [MonoidalCategory D] [MonoidalClosed D] [MonoidalPreadditive D] [BraidedCategory D]
  [Abelian.HasFunctorialFlatResolution D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

-- Preserve the closed proof appearing in previously compiled consumer signatures.
set_option linter.auxLemma false in
theorem instBraidedCategoryDerivedCategory_sheaf._proof_1 : IsRightCancelAdd ℤ :=
  inferInstance

-- Keep the existing local instance name for already compiled consumers.
local instance instBraidedCategoryDerivedCategory_sheaf :
    BraidedCategory (DerivedCategory D) :=
  DerivedMonoidal.braidedCategory (DerivedCategory.Qh (C := D))
    (HomotopyCategory.quasiIso D (.up ℤ))

attribute [local instance] CategoryTheory.derivedTensorPresentationBraiding

/-- The existing derived monoidal structure, with its base-category data fixed.
Source: the derived tensor construction used by `tensorModelTarget` below.
(blueprint: new-integral-residue-tensor-model) -/
noncomputable abbrev tensorModelDerivedMonoidal : MonoidalCategory (DerivedCategory D) :=
  inferInstance

/-- The existing homotopy monoidal structure, with its base-category data fixed.
Source: the homotopy tensor construction used by `tensorModelTarget` below.
(blueprint: new-integral-residue-tensor-model) -/
noncomputable abbrev tensorModelHomotopyMonoidal :
    MonoidalCategory (HomotopyCategory D (.up ℤ)) :=
  inferInstance

/-- The fixed coefficient concentrated in degree zero in the homotopy category.
Source: Bhatt--Scholze, Lemma 6.5.9(3), Remark 6.8.15; explicit tensor comparisons.
(blueprint: new-integral-residue-tensor-model) -/
noncomputable abbrev tensorModelCoefficient (B : C) :=
  (HomotopyCategory.quotient C (.up ℤ)).obj
    ((HomologicalComplex.single C (.up ℤ) 0).obj B)

/-- The standard comparison between the two degree-zero presentations.
Source: Bhatt--Scholze, Lemma 6.5.9(3), Remark 6.8.15; explicit tensor comparisons.
(blueprint: new-integral-residue-tensor-model) -/
noncomputable def tensorModelCoefficientIso (B : C) :
    (DerivedCategory.singleFunctor C 0).obj B ≅
      DerivedCategory.Qh.obj (tensorModelCoefficient B) :=
  CategoryTheory.homotopySingleComparisonIso B

omit [MonoidalCategory D] [MonoidalClosed D] [MonoidalPreadditive D]
  [BraidedCategory D] [Abelian.HasFunctorialFlatResolution D] in
set_option backward.isDefEq.respectTransparency false in
/-- The single-object comparison commutes with the exact-functor counit.

Expand the exact single comparison, use the counit factorization through the
map on derived categories, and apply naturality of the single/quotient comparisons.
The inverse coefficient isomorphism is the resulting homotopy comparison.

Source: Bhatt--Scholze, Remark 6.8.15; exact-functor single comparison.
(blueprint: new-integral-residue-tensor-model) -/
theorem tensorModelCoefficientIso_counit (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] (B : C) (B' : D)
    (e : F.obj B ≅ B') :
    let c := F.singleFunctorCompLeftDerivedFunctorIso.app B ≪≫
      (DerivedCategory.singleFunctor D 0).mapIso e
    let eH := (F.mapHomotopyCategoryFactors (.up ℤ)).app
        ((CochainComplex.singleFunctor C 0).obj B) ≪≫
      (HomotopyCategory.quotient D (.up ℤ)).mapIso
        ((F.mapCochainComplexSingleFunctor 0).app B ≪≫
          (HomologicalComplex.single D (.up ℤ) 0).mapIso e)
    c.inv ≫ F.leftDerivedFunctor.map (Functor.tensorModelCoefficientIso B).hom ≫
      F.leftDerivedFunctorCounit.app (Functor.tensorModelCoefficient B) =
      (Functor.tensorModelCoefficientIso B').hom ≫ DerivedCategory.Qh.map eH.inv := by
  dsimp only
  have h := NatTrans.congr_app F.leftDerivedFunctorIsoMapDerivedCategory_hom_fac
    (Functor.tensorModelCoefficient B)
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app] at h
  rw [← h]
  simp only [Functor.singleFunctorCompLeftDerivedFunctorIso, NatIso.trans_app, Iso.trans_inv,
    Iso.trans_hom, Iso.app_inv, Functor.isoWhiskerLeft_inv,
    Functor.whiskerLeft_app, Functor.mapIso_inv, Functor.tensorModelCoefficientIso,
    CategoryTheory.homotopySingleComparisonIso,
    Category.assoc]
  erw [F.leftDerivedFunctorIsoMapDerivedCategory.hom.naturality_assoc]
  simp only [Iso.inv_hom_id_app_assoc]
  simp only [Functor.tensorModelCoefficient, Functor.mapDerivedCategoryFactorsh_hom_app,
    DerivedCategory.singleFunctorIsoCompQ, Iso.refl_hom, Iso.app_hom, NatTrans.id_app,
    Iso.symm_hom, Category.id_comp, Functor.map_comp, Category.assoc]
  erw [← F.mapDerivedCategory.map_comp_assoc, Iso.inv_hom_id_app,
    F.mapDerivedCategory.map_id, Category.id_comp,
    F.mapDerivedCategorySingleFunctor_inv_app_mapDerivedCategoryFactors_hom_app_assoc]
  erw [DerivedCategory.quotientCompQhIso_inv_naturality_assoc,
    DerivedCategory.quotientCompQhIso_inv_naturality_assoc]
  rfl

/-- The ordinary tensor model built from a functor on derived categories and
its counit to the homotopy image of F. The definition uses those named data directly.
Source: Bhatt--Scholze, Remark 6.8.15; the standard tensor/counit comparison.
(blueprint: new-integral-residue-tensor-model) -/
@[irreducible] noncomputable def tensorModelTargetWith
    (G : DerivedCategory C ⥤ DerivedCategory D)
    (γ : DerivedCategory.Qh ⋙ G ⟶
      F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (B : C) (P : HomotopyCategory C (.up ℤ)) :
    G.obj (DerivedCategory.Qh.obj P) ⊗
        G.obj ((DerivedCategory.singleFunctor C 0).obj B) ⟶
      DerivedCategory.Qh.obj
        ((F.mapHomotopyCategory (.up ℤ)).obj (tensorModelCoefficient B) ⊗
          (F.mapHomotopyCategory (.up ℤ)).obj P) :=
  (β_ (G.obj ((DerivedCategory.singleFunctor C 0).obj B))
    (G.obj (DerivedCategory.Qh.obj P))).inv ≫
    ((G.map (tensorModelCoefficientIso B).hom ≫ γ.app (tensorModelCoefficient B)) ⊗ₘ
      γ.app P) ≫
    LaxMonoidal.μ (DerivedCategory.Qh (C := D))
      ((F.mapHomotopyCategory (.up ℤ)).obj (tensorModelCoefficient B))
      ((F.mapHomotopyCategory (.up ℤ)).obj P)

/-- Compare the derived target with the ordinary tensor after applying F.
The final tensor factor is K-flat on the representatives used below.
Source: Bhatt--Scholze, Lemma 6.5.9(3), Remark 6.8.15; explicit tensor comparisons.
(blueprint: new-integral-residue-tensor-model) -/
@[irreducible] noncomputable def tensorModelTarget (B : C) (P : HomotopyCategory C (.up ℤ)) :
    F.leftDerivedFunctor.obj (DerivedCategory.Qh.obj P) ⊗
        F.leftDerivedFunctor.obj ((DerivedCategory.singleFunctor C 0).obj B) ⟶
      DerivedCategory.Qh.obj
        ((F.mapHomotopyCategory (.up ℤ)).obj (tensorModelCoefficient B) ⊗
          (F.mapHomotopyCategory (.up ℤ)).obj P) :=
  tensorModelTargetWith F F.leftDerivedFunctor F.leftDerivedFunctorCounit B P

/-- The target comparison is invertible on representatives with K-flat image.
Source: Bhatt--Scholze, Lemma 6.5.9(3), Remark 6.8.15; explicit tensor comparisons.
(blueprint: new-integral-residue-tensor-model) -/
theorem tensorModelTarget_isIso (B : C) (P : HomotopyCategory C (.up ℤ))
    (hP : F.kFlatMap P) : IsIso (tensorModelTarget F B P) := by
  have := isIso_μNatTrans_Qh_app_app_of_kFlat
    ((F.mapHomotopyCategory (.up ℤ)).obj (tensorModelCoefficient B)) _ hP
  have : IsIso (F.leftDerivedFunctorCounit.app (tensorModelCoefficient B)) :=
    inferInstance
  have : IsIso (F.leftDerivedFunctorCounit.app P) := inferInstance
  have : IsIso (LaxMonoidal.μ (DerivedCategory.Qh (C := D))
      ((F.mapHomotopyCategory (.up ℤ)).obj (tensorModelCoefficient B))
      ((F.mapHomotopyCategory (.up ℤ)).obj P)) := ‹_›
  unfold tensorModelTarget tensorModelTargetWith
  infer_instance

variable [F.IsLeftAdjoint] [F.Monoidal]

/-- The common map built directly from a named derived functor and two named counits.
Source: Bhatt--Scholze, Lemma 6.5.9(3), Remark 6.8.15; explicit tensor comparisons.
(blueprint: new-integral-residue-tensor-model) -/
@[irreducible] noncomputable def tensorModelMapWith
    (G : DerivedCategory C ⥤ DerivedCategory D)
    (γ : DerivedCategory.Qh ⋙ G ⟶ F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (B : C) (H : DerivedCategory C ⥤ DerivedCategory C)
    (ε : DerivedCategory.Qh ⋙ H ⟶
      (tensorLeft B).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (P : HomotopyCategory C (.up ℤ)) :
    G.obj (H.obj (DerivedCategory.Qh.obj P)) ⟶
      DerivedCategory.Qh.obj
        ((F.mapHomotopyCategory (.up ℤ)).obj (tensorModelCoefficient B) ⊗
          (F.mapHomotopyCategory (.up ℤ)).obj P) :=
  G.map (ε.app P) ≫ γ.app _ ≫
    DerivedCategory.Qh.map
      ((F.mapHomotopyCategory (.up ℤ)).map
          ((CategoryTheory.homotopyTensorSingleIso B).inv.app P) ≫
        ((OplaxMonoidal.mapHomotopyCategoryδNatTrans (.up ℤ) F).app
          (tensorModelCoefficient B)).app P)


/-- The common map: the tensor counit, the exact-F counit, then the ordinary
comonoidal comparison.
Source: Bhatt--Scholze, Lemma 6.5.9(3), Remark 6.8.15; explicit tensor comparisons.
(blueprint: new-integral-residue-tensor-model) -/
noncomputable def tensorModelMap (B : C) (H : DerivedCategory C ⥤ DerivedCategory C)
    (ε : DerivedCategory.Qh ⋙ H ⟶
      (tensorLeft B).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (P : HomotopyCategory C (.up ℤ)) :
    F.leftDerivedFunctor.obj (H.obj (DerivedCategory.Qh.obj P)) ⟶
      DerivedCategory.Qh.obj
        ((F.mapHomotopyCategory (.up ℤ)).obj (tensorModelCoefficient B) ⊗
          (F.mapHomotopyCategory (.up ℤ)).obj P) :=
  tensorModelMapWith F F.leftDerivedFunctor F.leftDerivedFunctorCounit B H ε P

end CategoryTheory.Functor

local instance : EssentiallySmall.{u + 1} Profinite.{u} := essentiallySmallSelf.{0} _

namespace AlgebraicGeometry.ProEtale.CondensedRing

attribute [local instance 20000] sheafBraidedCategory
attribute [local irreducible] Functor.leftDerivedFunctor Functor.mapDerivedCategory

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]

/-- The residue coefficient as an ordinary integral module.
Source: Bhatt--Scholze, Lemma 6.5.9(3), Remark 6.8.15; explicit tensor comparisons.
(blueprint: new-integral-residue-tensor-model) -/
noncomputable abbrev residueExchangeOrdinaryCoefficient (T : Scheme.{u}) :=
  (Mod.comap (coefficientMap (integralReductionMap ℓ E) T)).obj
    (Mod.regular (condensedRingObj
      (Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)) T))

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

variable (P : HomotopyCategory
  (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
    (condensedRingObj (integralCoeff ℓ E) Y)) (.up ℤ))

/-- The explicit comparison from the target of the residue square to its ordinary model.
Source: Bhatt--Scholze, Lemma 6.5.9(3), Remark 6.8.15; explicit tensor comparisons.
(blueprint: new-integral-residue-tensor-model) -/
@[irreducible]
noncomputable def residueExchangeTensorModelTarget :
    (residueExchangeUpperStar (integralCoeff ℓ E) f).obj (DerivedCategory.Qh.obj P) ⊗
        (residueExchangeUpperStar (integralCoeff ℓ E) f).obj
          (residueExchangeCoefficient ℓ E Y) ⟶
      DerivedCategory.Qh.obj
        (((f)^*⟦integralCoeff ℓ E⟧.mapHomotopyCategory (.up ℤ)).obj
            (Functor.tensorModelCoefficient (residueExchangeOrdinaryCoefficient ℓ E Y)) ⊗
          ((f)^*⟦integralCoeff ℓ E⟧.mapHomotopyCategory (.up ℤ)).obj P) :=
  Functor.tensorModelTargetWith (f)^*⟦integralCoeff ℓ E⟧
    (residueExchangeUpperStar (integralCoeff ℓ E) f)
    (residueExchangeUpperStarCounit (integralCoeff ℓ E) f)
    (residueExchangeOrdinaryCoefficient ℓ E Y) P

/-- The explicit common map for the two routes in the residue square.
Source: Bhatt--Scholze, Lemma 6.5.9(3), Remark 6.8.15; explicit tensor comparisons.
(blueprint: new-integral-residue-tensor-model) -/
noncomputable def residueExchangeTensorModelMap :
    (residueExchangeUpperStar (integralCoeff ℓ E) f).obj
        ((residueExchangeRestriction ℓ E Y).obj
          ((residueExchangeReduction ℓ E Y).obj (DerivedCategory.Qh.obj P))) ⟶
      DerivedCategory.Qh.obj
        (((f)^*⟦integralCoeff ℓ E⟧.mapHomotopyCategory (.up ℤ)).obj
            (Functor.tensorModelCoefficient (residueExchangeOrdinaryCoefficient ℓ E Y)) ⊗
          ((f)^*⟦integralCoeff ℓ E⟧.mapHomotopyCategory (.up ℤ)).obj P) :=
  letI := residueExchangeOrdinaryPullMonoidal ℓ E f
  Functor.tensorModelMapWith (f)^*⟦integralCoeff ℓ E⟧
    (residueExchangeUpperStar (integralCoeff ℓ E) f)
    (residueExchangeUpperStarCounit (integralCoeff ℓ E) f)
    (residueExchangeOrdinaryCoefficient ℓ E Y)
    (residueExchangeReduction ℓ E Y ⋙ residueExchangeRestriction ℓ E Y)
    (residueExchangeTensorCounit ℓ E Y) P

end AlgebraicGeometry.ProEtale.CondensedRing
