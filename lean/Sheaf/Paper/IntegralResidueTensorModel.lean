/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.IntegralResidueTensorPresentation
public import Sheaf.Paper.IntegralResidueTensorCounit
public import Sheaf.Paper.IntegralResidueOrdinaryMonoidal
public import Sheaf.Paper.IntegralResidueDerivedMonoidal
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategoryBraided

/-! # A common homotopy-level model for the residue tensor square

Source: Bhatt--Scholze, Lemma 6.5.9(3), Remark 6.8.15.
(blueprint: new-integral-residue-tensor-model)
-/

@[expose] public section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

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

local instance : BraidedCategory (DerivedCategory D) := DerivedCategory.braidedCategory D


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
  (DerivedCategory.singleFunctorIsoCompQ C 0).app B ≪≫
    (DerivedCategory.quotientCompQhIso C).symm.app _

/-- Counit normalization of the canonical tensor presentation.
Source: Bhatt--Scholze, Lemma 6.5.9(3); uniqueness of left derived functors.
(blueprint: new-integral-residue-tensor-model)
Proof. Expand the fixed presentation, cancel its final braiding and the inverse
single-object comparison, and apply the two left-derived counit identities. -/
theorem derivedTensorPresentationIso_normalization (B : C)
    (H : DerivedCategory C ⥤ DerivedCategory C)
    (ε : DerivedCategory.Qh ⋙ H ⟶
      (tensorLeft B).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    [H.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso C (.up ℤ))]
    (P : HomotopyCategory C (.up ℤ)) :
    letI := DerivedCategory.braidedCategory C
    (derivedTensorPresentationIso B H ε).hom.app (DerivedCategory.Qh.obj P) ≫
      (β_ ((DerivedCategory.singleFunctor C 0).obj B) (DerivedCategory.Qh.obj P)).inv ≫
      ((tensorModelCoefficientIso B).hom ▷ DerivedCategory.Qh.obj P) ≫
      Functor.LaxMonoidal.μ DerivedCategory.Qh (tensorModelCoefficient B) P =
    ε.app P ≫ DerivedCategory.Qh.map ((homotopyTensorSingleIso B).inv.app P) := by
  let := DerivedCategory.braidedCategory C
  unfold derivedTensorPresentationIso derivedTensorSingleIso
  simp only [Iso.trans_hom, NatTrans.comp_app, BraidedCategory.tensorLeftIsoTensorRight,
    Category.assoc, Iso.hom_inv_id_assoc]
  dsimp only [Functor.mapIso_hom, Iso.symm_hom, curriedTensor_map_app]
  change _ ≫ _ ≫ (tensorModelCoefficientIso B).inv ▷ _ ≫
    (tensorModelCoefficientIso B).hom ▷ _ ≫ _ = _
  rw [← comp_whiskerRight_assoc, Iso.inv_hom_id, id_whiskerRight, Category.id_comp]
  change _ ≫ _ ≫ (DerivedCategory.tensorLeftQhObjCounit
    (tensorModelCoefficient B)).app P = _
  simp only [Functor.leftDerivedNatIso_hom]
  rw [Functor.leftDerivedNatTrans_app]
  simp only [Functor.isoWhiskerRight_hom, Iso.symm_hom, Functor.whiskerRight_app]
  rw [Functor.leftDerivedNatTrans_app_assoc]
  simp


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
  (β_ (F.leftDerivedFunctor.obj ((DerivedCategory.singleFunctor C 0).obj B))
    (F.leftDerivedFunctor.obj (DerivedCategory.Qh.obj P))).inv ≫
    ((F.leftDerivedFunctor.map (tensorModelCoefficientIso B).hom ≫
      F.leftDerivedFunctorCounit.app (tensorModelCoefficient B)) ⊗ₘ
      F.leftDerivedFunctorCounit.app P) ≫
    LaxMonoidal.μ (DerivedCategory.Qh (C := D))
      ((F.mapHomotopyCategory (.up ℤ)).obj (tensorModelCoefficient B))
      ((F.mapHomotopyCategory (.up ℤ)).obj P)

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
  unfold tensorModelTarget
  infer_instance

variable [F.IsLeftAdjoint] [F.Monoidal]

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
  F.leftDerivedFunctor.map (ε.app P) ≫ F.leftDerivedFunctorCounit.app _ ≫
    DerivedCategory.Qh.map
      ((F.mapHomotopyCategory (.up ℤ)).map
          ((CategoryTheory.homotopyTensorSingleIso B).inv.app P) ≫
        ((OplaxMonoidal.mapHomotopyCategoryδNatTrans (.up ℤ) F).app
          (tensorModelCoefficient B)).app P)

end CategoryTheory.Functor

local instance : EssentiallySmall.{u + 1} Profinite.{u} := essentiallySmallSelf.{0} _

namespace AlgebraicGeometry.ProEtale.CondensedRing


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
          ((f)^*⟦integralCoeff ℓ E⟧.mapHomotopyCategory (.up ℤ)).obj P) := by
  unfold residueExchangeUpperStar
  exact Functor.tensorModelTarget (f)^*⟦integralCoeff ℓ E⟧
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
          ((f)^*⟦integralCoeff ℓ E⟧.mapHomotopyCategory (.up ℤ)).obj P) := by
  let := residueExchangeOrdinaryPullMonoidal ℓ E f
  unfold residueExchangeUpperStar
  exact Functor.tensorModelMap (f)^*⟦integralCoeff ℓ E⟧
    (residueExchangeOrdinaryCoefficient ℓ E Y)
    (residueExchangeReduction ℓ E Y ⋙ residueExchangeRestriction ℓ E Y)
    (by
      unfold residueExchangeReduction integralReduction residueExchangeRestriction
      exact Mod.tensorPresentationDerivedCounit (coefficientMap (integralReductionMap ℓ E) Y)) P

attribute [local semireducible] residueExchangeUpperStar

/-- Expose the ordinary model target without unfolding the coefficient constructions.
Source: Bhatt--Scholze, Lemma 6.5.9(3); the explicit tensor model.
(blueprint: new-integral-residue-tensor-model)
Proof. This is the defining equation of the concrete target map. -/
theorem residueExchangeTensorModelTarget_eq :
    residueExchangeTensorModelTarget ℓ E f P =
      Functor.tensorModelTarget (f)^*⟦integralCoeff ℓ E⟧
        (residueExchangeOrdinaryCoefficient ℓ E Y) P := by
  unfold residueExchangeTensorModelTarget residueExchangeUpperStar
  rfl

/-- Expose the ordinary model map with its fixed tensor counit.
Source: Bhatt--Scholze, Lemma 6.5.9(3); the explicit tensor model.
(blueprint: new-integral-residue-tensor-model)
Proof. This is the defining equation of the concrete model map. -/
theorem residueExchangeTensorModelMap_eq :
    letI := residueExchangeOrdinaryPullMonoidal ℓ E f
    residueExchangeTensorModelMap ℓ E f P =
      Functor.tensorModelMap (f)^*⟦integralCoeff ℓ E⟧
        (residueExchangeOrdinaryCoefficient ℓ E Y)
        (residueExchangeReduction ℓ E Y ⋙ residueExchangeRestriction ℓ E Y)
        (residueExchangeTensorCounit ℓ E Y) P := by
  unfold residueExchangeTensorModelMap residueExchangeUpperStar residueExchangeTensorCounit
  rfl


end AlgebraicGeometry.ProEtale.CondensedRing
