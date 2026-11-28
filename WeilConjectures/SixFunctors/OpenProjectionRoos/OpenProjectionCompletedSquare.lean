/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.OpenProjectionRoos.OpenProjectionRoosCompletionData
import WeilConjectures.SixFunctors.OpenTensorAugmentation.OpenTensorAugmentationLimitSquare
import WeilConjectures.SixFunctors.CompactSupportCoefficientTensor.ProjectionTensorCoefficientComparison
import WeilConjectures.SixFunctors.OpenProjectionRoos.OpenProjectionRoosProducts
import WeilConjectures.AlgebraicGeometry.FiniteFieldPrimePowerUnit

/-! # Descent of the augmented open tensor square through completion

The completed open projection `openProjectionCompletedSquare` is the ordinary open projection
conjugated by the tensor completion units.

## Implementation details

The completion units are invertible on constructible pairs. The completed representative
equation reduces, through the representative isomorphisms of the tensor models, to the
chain-level identity `roosChainSquare` in the strict Roos cocone, which is checked on both
cocone coordinates (`RoosComparison.augmentation_square`).

## References

* Bhatt--Scholze, Lemmas 6.5.5 and 6.5.8
* Stacks Project, Tag 0940
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.OpenProjectionRoos

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
  (o : IntegralOpenReduction.Operations l E j)

variable
  (SX : CoefficientDerivedSystemCalculus l E X)
  (SU : CoefficientDerivedSystemCalculus l E U)
  (AX : OpenSemilinearTensor.OrdinaryReduction l E X)
  (AU : OpenSemilinearTensor.OrdinaryReduction l E U)
  (st : IntegralOpenReduction.TensorComparison l E j o)
  (m : OpenSemilinearTensor.Comparison l E j o SX SU AX AU st)
  (c : IntegralOpenReduction.Comparison l E j o SX SU st)
  (q : OpenTensorQuotient.Comparison l E j o SX SU AX AU st m c)

/-- On the strict level, the completed open projection square commutes: extending the lower
tensor augmentation along the chain comparison and the Roos comparison of open extension
agrees with the upper tensor augmentation followed by the strict square. -/
theorem roosChainSquare
    (extension : RoosComparison (IntegralOpenReduction.extension l E j o))
    (Q : CochainComplex (scalarReductionSource l E U) ℤ)
    (F : CochainComplex (scalarReductionSource l E X) ℤ)
    (z : OpenTensorQuotient.StrictSquare l E j o m.totalComparison q.scalar st
      q.strictScalar Q F)
    (hup : OpenTensorQuotient.RoosNormalization l E X q.tensorX
      ((OpenSemilinearTensor.extensionComplex l E j o).obj Q) F z.upper)
    (hlow : OpenTensorQuotient.RoosNormalization l E U q.tensorU Q
      ((OpenSemilinearTensor.restrictionComplex l E j o).obj F) z.lower) :
    (m.totalComparison.chain Q F).hom ≫
        (OpenSemilinearTensor.extensionComplex l E j o).map
          (q.tensorU.chain.app (Q, (OpenSemilinearTensor.restrictionComplex l E j o).obj F)) ≫
        extension.iso.hom.app ((integralOperationsTensorTowerFunctor l E U).obj
          (Q, (OpenSemilinearTensor.restrictionComplex l E j o).obj F)) =
      q.tensorX.chain.app ((OpenSemilinearTensor.extensionComplex l E j o).obj Q, F) ≫
        integralOperationsRoosMap z.gamma.hom := by
  refine RoosComparison.augmentation_square (IntegralOpenReduction.extension l E j o) extension
    ((integralOperationsTensorTowerFunctor l E U).obj
      (Q, (OpenSemilinearTensor.restrictionComplex l E j o).obj F))
    ((integralOperationsTensorTowerFunctor l E X).obj
      ((OpenSemilinearTensor.extensionComplex l E j o).obj Q, F))
    z.gamma.hom (m.totalComparison.chain Q F).hom
    (q.tensorU.chain.app (Q, (OpenSemilinearTensor.restrictionComplex l E j o).obj F))
    (q.tensorX.chain.app ((OpenSemilinearTensor.extensionComplex l E j o).obj Q, F))
    z.lower.map z.upper.map (fun n ↦ ?_) (q.tensorU.canonical.1.2 _ _) (fun n ↦ ?_)
    (q.tensorX.canonical.1.2 _ _) (fun n ↦ ?_)
  · apply HomologicalComplex.hom_ext
    intro i
    exact (eq_of_heq (hlow n i)).symm
  · apply HomologicalComplex.hom_ext
    intro i
    exact (eq_of_heq (hup n i)).symm
  · rw [← NatTrans.comp_app, z.square]
    apply HomologicalComplex.hom_ext
    intro i
    exact eq_of_heq (z.lowerRouteFormula (op n) i)

private theorem lowerRoute_assemble {𝒜 ℬ : Type*} [Category 𝒜] [Category ℬ] (S : 𝒜 ⥤ ℬ)
    {A₀ A₁ A₂ A₃ A₄ A₅ : 𝒜} {B₀ Z : ℬ} (e : B₀ ⟶ S.obj A₀) (a₁ : A₀ ⟶ A₁) (a₂ : A₁ ⟶ A₂)
    (a₃ : A₂ ⟶ A₃) (a₄ : A₃ ⟶ A₄) (a₅ : A₄ ⟶ A₅) (d : S.obj A₅ ⟶ Z) (x : A₀ ⟶ A₅)
    (hx : a₁ ≫ a₂ ≫ a₃ ≫ a₄ ≫ a₅ = x) (y : B₀ ⟶ Z) (hy : e ≫ S.map x ≫ d = y) :
    e ≫ S.map a₁ ≫ S.map a₂ ≫ S.map a₃ ≫ S.map a₄ ≫ S.map a₅ ≫ d = y := by
  rw [← hy, ← hx]
  simp

/-- The lower route of the completed representative equation: restriction, the tensor model
on the open, its completion and the Roos comparison of open extension. -/
theorem completedRepresentative_lowerRoute
    [PreservesFiniteLimits (IntegralOpenReduction.restriction l E j o)]
    [PreservesFiniteColimits (IntegralOpenReduction.restriction l E j o)]
    (extension : RoosComparison (IntegralOpenReduction.extension l E j o))
    (flat : ∀ (W : Scheme.{u}) (P : CochainComplex (scalarReductionSource l E W) ℤ),
      integralOperationsGoodComplex l E W P →
        proEtaleFlatRepresentatives W (completedIntegralCommRingSheafUnrestricted l E W) P)
    (restrictGood : ∀ (P : CochainComplex (scalarReductionSource l E X) ℤ),
      integralOperationsGoodComplex l E X P → integralOperationsGoodComplex l E U
        ((OpenSemilinearTensor.restrictionComplex l E j o).obj P))
    (Q : CochainComplex (scalarReductionSource l E U) ℤ)
    (F : CochainComplex (scalarReductionSource l E X) ℤ)
    (hQ : integralOperationsGoodComplex l E U Q) (hF : integralOperationsGoodComplex l E X F) :
    ((IntegralOpenReduction.extension l E j o).mapDerivedCategoryFactors.app
        ((OpenSemilinearTensor.total l E U).obj
          (Q, (OpenSemilinearTensor.restrictionComplex l E j o).obj F))).inv ≫
      (IntegralOpenReduction.shriek l E j o).map
        ((q.tensorU.ordinary.representative.app (⟨Q, flat U Q hQ⟩,
          ⟨(OpenSemilinearTensor.restrictionComplex l E j o).obj F,
            flat U _ (restrictGood F hF)⟩)).hom) ≫
      (IntegralOpenReduction.shriek l E j o).map (q.tensorU.ordinary.tensor.mapIso
        (Iso.prod (Iso.refl _)
          ((IntegralOpenReduction.restriction l E j o).mapDerivedCategoryFactors.app F))).inv ≫
      (IntegralOpenReduction.shriek l E j o).map ((q.tensorU.chi l E).app
        (DerivedCategory.Q.obj Q,
          (IntegralOpenReduction.star l E j o).obj (DerivedCategory.Q.obj F))) ≫
      (IntegralOpenReduction.shriek l E j o).map
        ((integralCompletedTensor l E U).map (Prod.mkHom (𝟙 _)
          ((IntegralOpenReduction.restriction l E j o).mapDerivedCategoryFactors.hom.app F))) ≫
      (IntegralOpenReduction.shriek l E j o).map
        ((integralCompletedTensorComparison l E U).hom.app
          (⟨Q, hQ⟩, ⟨(OpenSemilinearTensor.restrictionComplex l E j o).obj F,
            restrictGood F hF⟩)) ≫
      (extension.derived (IntegralOpenReduction.extension l E j o)
        ((integralOperationsTensorTowerFunctor l E U).obj
          (Q, (OpenSemilinearTensor.restrictionComplex l E j o).obj F))).hom =
      DerivedCategory.Q.map ((OpenSemilinearTensor.extensionComplex l E j o).map
        (q.tensorU.chain.app (Q, (OpenSemilinearTensor.restrictionComplex l E j o).obj F)) ≫
          extension.iso.hom.app ((integralOperationsTensorTowerFunctor l E U).obj
            (Q, (OpenSemilinearTensor.restrictionComplex l E j o).obj F))) := by
  have k1 : (q.tensorU.ordinary.tensor.mapIso
      (Iso.prod (Iso.refl _)
        ((IntegralOpenReduction.restriction l E j o).mapDerivedCategoryFactors.app F))).inv ≫
      (q.tensorU.chi l E).app (DerivedCategory.Q.obj Q,
          (IntegralOpenReduction.star l E j o).obj (DerivedCategory.Q.obj F)) ≫
      (integralCompletedTensor l E U).map (Prod.mkHom (𝟙 _)
          ((IntegralOpenReduction.restriction l E j o).mapDerivedCategoryFactors.hom.app F)) =
      (q.tensorU.chi l E).app (DerivedCategory.Q.obj Q, DerivedCategory.Q.obj
        ((OpenSemilinearTensor.restrictionComplex l E j o).obj F)) := by
    rw [Functor.mapIso_inv]
    erw [(q.tensorU.chi l E).naturality_assoc]
    rw [← Functor.map_comp]
    have h : (Iso.prod (Iso.refl (DerivedCategory.Q.obj Q :
        DerivedCategory (scalarReductionSource l E U)))
        ((IntegralOpenReduction.restriction l E j o).mapDerivedCategoryFactors.app F)).inv ≫
        Prod.mkHom (𝟙 _)
          ((IntegralOpenReduction.restriction l E j o).mapDerivedCategoryFactors.hom.app F) =
        𝟙 _ := (Iso.prod _ _).inv_hom_id
    rw [h, CategoryTheory.Functor.map_id, Category.comp_id]
    rfl
  have k2 : (q.tensorU.ordinary.representative.app (⟨Q, flat U Q hQ⟩,
        ⟨(OpenSemilinearTensor.restrictionComplex l E j o).obj F,
          flat U _ (restrictGood F hF)⟩)).hom ≫
      (q.tensorU.chi l E).app (DerivedCategory.Q.obj Q, DerivedCategory.Q.obj
        ((OpenSemilinearTensor.restrictionComplex l E j o).obj F)) ≫
      (integralCompletedTensorComparison l E U).hom.app
          (⟨Q, hQ⟩, ⟨(OpenSemilinearTensor.restrictionComplex l E j o).obj F,
            restrictGood F hF⟩) =
      DerivedCategory.Q.map
        (q.tensorU.chain.app (Q, (OpenSemilinearTensor.restrictionComplex l E j o).obj F)) :=
    (congrArg (_ ≫ ·) (Category.assoc _ _ _)).trans (q.tensorU.canonical.2 Q _
      (flat U Q hQ) (flat U _ (restrictGood F hF)))
  refine lowerRoute_assemble (IntegralOpenReduction.shriek l E j o) _ _ _ _ _ _ _
    (DerivedCategory.Q.map
      (q.tensorU.chain.app (Q, (OpenSemilinearTensor.restrictionComplex l E j o).obj F)))
    ?_ _ ?_
  · rw [← k2, ← k1]
    simp only [Category.assoc]
    rfl
  · have hn := (IntegralOpenReduction.extension l E j o).mapDerivedCategoryFactors.inv.naturality
      (q.tensorU.chain.app (Q, (OpenSemilinearTensor.restrictionComplex l E j o).obj F))
    have hd : (extension.derived (IntegralOpenReduction.extension l E j o)
        ((integralOperationsTensorTowerFunctor l E U).obj
          (Q, (OpenSemilinearTensor.restrictionComplex l E j o).obj F))).hom =
        (IntegralOpenReduction.extension l E j o).mapDerivedCategoryFactors.hom.app
          (integralOperationsRoos ((integralOperationsTensorTowerFunctor l E U).obj
            (Q, (OpenSemilinearTensor.restrictionComplex l E j o).obj F))) ≫
        DerivedCategory.Q.map (extension.iso.hom.app
          ((integralOperationsTensorTowerFunctor l E U).obj
            (Q, (OpenSemilinearTensor.restrictionComplex l E j o).obj F))) := rfl
    rw [hd]
    erw [← reassoc_of% hn]
    erw [Iso.inv_hom_id_app_assoc]
    exact (DerivedCategory.Q.map_comp _ _).symm

private theorem completedSquare_assemble {C : Type*} [Category C]
    {A₀ A₁ A₂ B P D G G₁ G₂ R Z : C}
    (u : P ≅ B) (v : B ≅ A₀) (o : A₀ ⟶ G) (w : G ≅ G₁) (y : G₁ ≅ G₂) (zz : G₂ ≅ D)
    (ch : P ⟶ D) (hord : u.hom ≫ v.hom ≫ o ≫ w.hom ≫ y.hom ≫ zz.hom = ch)
    (cX : A₀ ⟶ A₁) [IsIso cX] (tail : G ⟶ Z) (e : A₁ ⟶ A₂) (comp : A₂ ⟶ R) (roos : R ⟶ Z)
    (ext : D ⟶ Z) (chX : P ⟶ R) (cX' : B ⟶ A₂)
    (hrest : zz.inv ≫ y.inv ≫ w.inv ≫ tail = ext)
    (hchain : ch ≫ ext = chX ≫ roos)
    (hX : u.hom ≫ cX' ≫ comp = chX)
    (hnat : v.inv ≫ cX' = cX ≫ e) :
    inv cX ≫ o ≫ tail = e ≫ comp ≫ roos := by
  have ho : o = v.inv ≫ u.inv ≫ ch ≫ zz.inv ≫ y.inv ≫ w.inv := by
    rw [← hord]
    simp
  rw [ho]
  simp only [Category.assoc]
  rw [hrest, hchain, ← hX]
  simp [reassoc_of% hnat]

/-- The completed representative equation for the completed open projection
`χ_X⁻¹ ≫ ordinary ≫ j_!(χ_U)` on a pair of good complexes. -/
theorem completedRepresentative_of_ordinary
    [PreservesFiniteLimits (IntegralOpenReduction.restriction l E j o)]
    [PreservesFiniteColimits (IntegralOpenReduction.restriction l E j o)]
    (extension : RoosComparison (IntegralOpenReduction.extension l E j o))
    (flat : ∀ (W : Scheme.{u}) (P : CochainComplex (scalarReductionSource l E W) ℤ),
      integralOperationsGoodComplex l E W P →
        proEtaleFlatRepresentatives W (completedIntegralCommRingSheafUnrestricted l E W) P)
    (extendGood : ∀ (P : CochainComplex (scalarReductionSource l E U) ℤ),
      integralOperationsGoodComplex l E U P → integralOperationsGoodComplex l E X
        ((OpenSemilinearTensor.extensionComplex l E j o).obj P))
    (restrictGood : ∀ (P : CochainComplex (scalarReductionSource l E X) ℤ),
      integralOperationsGoodComplex l E X P → integralOperationsGoodComplex l E U
        ((OpenSemilinearTensor.restrictionComplex l E j o).obj P))
    (ordinary : leftInputs l E j o ⋙ q.tensorX.ordinary.tensor ≅
      rightInputs l E j o ⋙ q.tensorU.ordinary.tensor ⋙ IntegralOpenReduction.shriek l E j o)
    (hord : OrdinaryRepresentative l E j o SX SU AX AU st m c q flat extendGood restrictGood
      ordinary)
    (Q : CochainComplex (scalarReductionSource l E U) ℤ)
    (F : CochainComplex (scalarReductionSource l E X) ℤ)
    (hQ : integralOperationsGoodComplex l E U Q) (hF : integralOperationsGoodComplex l E X F)
    (z : OpenTensorQuotient.StrictSquare l E j o m.totalComparison q.scalar st
      q.strictScalar Q F)
    (hup : OpenTensorQuotient.RoosNormalization l E X q.tensorX
      ((OpenSemilinearTensor.extensionComplex l E j o).obj Q) F z.upper)
    (hlow : OpenTensorQuotient.RoosNormalization l E U q.tensorU Q
      ((OpenSemilinearTensor.restrictionComplex l E j o).obj F) z.lower)
    [IsIso ((q.tensorX.chi l E).app ((IntegralOpenReduction.shriek l E j o).obj
      (DerivedCategory.Q.obj Q), DerivedCategory.Q.obj F))] :
    inv ((q.tensorX.chi l E).app ((IntegralOpenReduction.shriek l E j o).obj
        (DerivedCategory.Q.obj Q), DerivedCategory.Q.obj F)) ≫
      ordinary.hom.app (DerivedCategory.Q.obj Q, DerivedCategory.Q.obj F) ≫
      (IntegralOpenReduction.shriek l E j o).map ((q.tensorU.chi l E).app
        (DerivedCategory.Q.obj Q,
          (IntegralOpenReduction.star l E j o).obj (DerivedCategory.Q.obj F))) ≫
      (IntegralOpenReduction.shriek l E j o).map
        ((integralCompletedTensor l E U).map (Prod.mkHom (𝟙 _)
          ((IntegralOpenReduction.restriction l E j o).mapDerivedCategoryFactors.hom.app F))) ≫
      (IntegralOpenReduction.shriek l E j o).map
        ((integralCompletedTensorComparison l E U).hom.app
          (⟨Q, hQ⟩, ⟨(OpenSemilinearTensor.restrictionComplex l E j o).obj F,
            restrictGood F hF⟩)) ≫
      (extension.derived (IntegralOpenReduction.extension l E j o)
        ((integralOperationsTensorTowerFunctor l E U).obj
          (Q, (OpenSemilinearTensor.restrictionComplex l E j o).obj F))).hom =
      (integralCompletedTensor l E X).map (Prod.mkHom
        ((IntegralOpenReduction.extension l E j o).mapDerivedCategoryFactors.hom.app Q) (𝟙 _)) ≫
      (integralCompletedTensorComparison l E X).hom.app
        (⟨(OpenSemilinearTensor.extensionComplex l E j o).obj Q, extendGood Q hQ⟩, ⟨F, hF⟩) ≫
      DerivedCategory.Q.map (integralOperationsRoosMap z.gamma.hom) := by
  refine completedSquare_assemble (o := ordinary.hom.app (DerivedCategory.Q.obj Q,
      DerivedCategory.Q.obj F))
    (cX := (q.tensorX.chi l E).app ((IntegralOpenReduction.shriek l E j o).obj
      (DerivedCategory.Q.obj Q), DerivedCategory.Q.obj F))
    (e := (integralCompletedTensor l E X).map (Prod.mkHom
      ((IntegralOpenReduction.extension l E j o).mapDerivedCategoryFactors.hom.app Q) (𝟙 _)))
    (comp := (integralCompletedTensorComparison l E X).hom.app
      (⟨(OpenSemilinearTensor.extensionComplex l E j o).obj Q, extendGood Q hQ⟩, ⟨F, hF⟩))
    (roos := DerivedCategory.Q.map (integralOperationsRoosMap z.gamma.hom))
    (u := q.tensorX.ordinary.representative.app
      (⟨(OpenSemilinearTensor.extensionComplex l E j o).obj Q, flat X _ (extendGood Q hQ)⟩,
        ⟨F, flat X F hF⟩))
    (v := q.tensorX.ordinary.tensor.mapIso (Iso.prod
      ((IntegralOpenReduction.extension l E j o).mapDerivedCategoryFactors.app Q).symm
      (Iso.refl (DerivedCategory.Q.obj F))))
    (w := (IntegralOpenReduction.shriek l E j o).mapIso (q.tensorU.ordinary.tensor.mapIso
      (Iso.prod (Iso.refl (DerivedCategory.Q.obj Q))
        ((IntegralOpenReduction.restriction l E j o).mapDerivedCategoryFactors.app F))))
    (y := ((IntegralOpenReduction.shriek l E j o).mapIso
      (q.tensorU.ordinary.representative.app (⟨Q, flat U Q hQ⟩,
        ⟨(OpenSemilinearTensor.restrictionComplex l E j o).obj F,
          flat U _ (restrictGood F hF)⟩))).symm)
    (zz := (IntegralOpenReduction.extension l E j o).mapDerivedCategoryFactors.app
      ((OpenSemilinearTensor.total l E U).obj
        (Q, (OpenSemilinearTensor.restrictionComplex l E j o).obj F)))
    (ch := DerivedCategory.Q.map (m.totalComparison.chain Q F).hom)
    (hord := eq_of_heq (hord Q F hQ hF))
    (ext := DerivedCategory.Q.map ((OpenSemilinearTensor.extensionComplex l E j o).map
      (q.tensorU.chain.app (Q, (OpenSemilinearTensor.restrictionComplex l E j o).obj F)) ≫
        extension.iso.hom.app ((integralOperationsTensorTowerFunctor l E U).obj
          (Q, (OpenSemilinearTensor.restrictionComplex l E j o).obj F))))
    (chX := DerivedCategory.Q.map
      (q.tensorX.chain.app ((OpenSemilinearTensor.extensionComplex l E j o).obj Q, F)))
    (cX' := (q.tensorX.chi l E).app
      (DerivedCategory.Q.obj ((OpenSemilinearTensor.extensionComplex l E j o).obj Q),
        DerivedCategory.Q.obj F))
      _ ?_ ?_ ?_ ?_
  · exact completedRepresentative_lowerRoute l E j o SX SU AX AU st m c q extension flat
      restrictGood Q F hQ hF
  · exact ((DerivedCategory.Q.map_comp _ _).symm.trans (congrArg DerivedCategory.Q.map
      (roosChainSquare l E j o SX SU AX AU st m c q extension Q F z hup hlow))).trans
        (DerivedCategory.Q.map_comp _ _)
  · exact (congrArg (_ ≫ ·) (Category.assoc _ _ _)).trans (q.tensorX.canonical.2
      ((OpenSemilinearTensor.extensionComplex l E j o).obj Q) F
      (flat X _ (extendGood Q hQ)) (flat X F hF))
  · exact (q.tensorX.chi l E).naturality _

attribute [local irreducible] integralOperationsTensorTowerFunctor
  coefficientTotalTensor integralOperationsTensorLevel
  completedIntegralCommRingSheafUnrestricted completedIntegralCoefficientSheafUnrestricted
  unrestrictedIntegralComplexFunctor

/-- There is a completed open tensor isomorphism `gamma` compatible with the augmentations
`chi` (which are invertible on constructible inputs) and satisfying the completed
representative equation. -/
theorem openProjectionCompletedSquare
    (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    [U.Over (Spec (.of D.k))] [X.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (U ↘ Spec (.of D.k))] [QuasiCompact (U ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [j.IsOver (Spec (.of D.k))]
    [restrictionLimits : PreservesFiniteLimits (IntegralOpenReduction.restriction l E j o)]
    [restrictionColimits : PreservesFiniteColimits (IntegralOpenReduction.restriction l E j o)]
    (extension : RoosComparison (IntegralOpenReduction.extension l E j o))
    (flat : ∀ (W : Scheme.{u}) (P : CochainComplex (scalarReductionSource l E W) ℤ),
    integralOperationsGoodComplex l E W P →
      proEtaleFlatRepresentatives W (completedIntegralCommRingSheafUnrestricted l E W) P)
    (extendGood : ∀ (P : CochainComplex (scalarReductionSource l E U) ℤ),
    integralOperationsGoodComplex l E U P → integralOperationsGoodComplex l E X
      ((OpenSemilinearTensor.extensionComplex l E j o).obj P))
    (restrictGood : ∀ (P : CochainComplex (scalarReductionSource l E X) ℤ),
    integralOperationsGoodComplex l E X P → integralOperationsGoodComplex l E U
      ((OpenSemilinearTensor.restrictionComplex l E j o).obj P))
    (ordinary : leftInputs l E j o ⋙ q.tensorX.ordinary.tensor ≅
    rightInputs l E j o ⋙ q.tensorU.ordinary.tensor ⋙ IntegralOpenReduction.shriek l E j o)
    (_ordinary_representative : OrdinaryRepresentative l E j o SX SU AX AU st m c q
      flat extendGood restrictGood ordinary)
    :
    ∃ (gamma : completedLeft l E j o ≅ completedRight l E j o),
    ∃ (_units : ∀ K : sfIntegralConstructibleCategory l E U × sfIntegralConstructibleCategory l E X,
    (q.tensorX.chi l E).app ((leftInputs l E j o).obj (K.1.obj, K.2.obj)) ≫
        gamma.hom.app K =
      ordinary.hom.app (K.1.obj, K.2.obj) ≫
        (IntegralOpenReduction.shriek l E j o).map
          ((q.tensorU.chi l E).app ((rightInputs l E j o).obj (K.1.obj, K.2.obj)))),
    ∃ (_invertibleUnits : ∀ K :
      sfIntegralConstructibleCategory l E U × sfIntegralConstructibleCategory l E X,
    IsIso ((q.tensorX.chi l E).app ((leftInputs l E j o).obj (K.1.obj, K.2.obj))) ∧
      IsIso ((q.tensorU.chi l E).app ((rightInputs l E j o).obj (K.1.obj, K.2.obj)))),
    CompletedRepresentative l E j o SX SU AX AU st m c q
      extension extendGood restrictGood gamma := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of D.k))
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of D.k))
  have : IsNoetherian X := {}
  have : IsLocallyNoetherian U := LocallyOfFiniteType.isLocallyNoetherian (U ↘ Spec (.of D.k))
  have : CompactSpace U := QuasiCompact.compactSpace_of_compactSpace (U ↘ Spec (.of D.k))
  have : IsNoetherian U := {}
  let : ∀ x : X, Invertible (l : X.residueField x) := fun x ↦
    (AlgebraicGeometry.ProEtale.finiteFieldPrime_isUnit_residueField D l hl
      (X ↘ Spec (.of D.k)) x).invertible
  let : ∀ x : U, Invertible (l : U.residueField x) := fun x ↦
    (AlgebraicGeometry.ProEtale.finiteFieldPrime_isUnit_residueField D l hl
      (U ↘ Spec (.of D.k)) x).invertible
  have hinv (K : sfIntegralConstructibleCategory l E U × sfIntegralConstructibleCategory l E X) :
      IsIso ((q.tensorX.chi l E).app ((leftInputs l E j o).obj (K.1.obj, K.2.obj))) ∧
        IsIso ((q.tensorU.chi l E).app ((rightInputs l E j o).obj (K.1.obj, K.2.obj))) :=
    ⟨ProjectionTensorCoefficient.completion_isIso l E X q.tensorX
        ⟨_, q.integralGeometry.1 _ K.1.property⟩ K.2,
      ProjectionTensorCoefficient.completion_isIso l E U q.tensorU K.1
        ⟨_, q.integralGeometry.2.1 _ K.2.property⟩⟩
  let cX : pairs l E (U := U) (X := X) ⋙ leftInputs l E j o ⋙ q.tensorX.ordinary.tensor ⟶
      completedLeft l E j o :=
    Functor.whiskerLeft (pairs l E ⋙ leftInputs l E j o) (q.tensorX.chi l E)
  have : IsIso cX := by
    have : ∀ K, IsIso (cX.app K) := fun K ↦ (hinv K).1
    exact NatIso.isIso_of_isIso_app cX
  let cU : pairs l E (U := U) (X := X) ⋙ rightInputs l E j o ⋙ q.tensorU.ordinary.tensor ⟶
      completedInside l E j o :=
    Functor.whiskerLeft (pairs l E ⋙ rightInputs l E j o) (q.tensorU.chi l E)
  have : IsIso cU := by
    have : ∀ K, IsIso (cU.app K) := fun K ↦ (hinv K).2
    exact NatIso.isIso_of_isIso_app cU
  let gamma : completedLeft l E j o ≅ completedRight l E j o :=
    (asIso cX).symm ≪≫ Functor.isoWhiskerLeft (pairs l E) ordinary ≪≫
      Functor.isoWhiskerRight (asIso cU) (IntegralOpenReduction.shriek l E j o)
  refine ⟨gamma, ?_, hinv, ?_⟩
  · intro K
    have : IsIso ((q.tensorX.chi l E).app ((leftInputs l E j o).obj (K.1.obj, K.2.obj))) :=
      (hinv K).1
    have h : gamma.hom.app K = inv (cX.app K) ≫ ordinary.hom.app _ ≫
        (IntegralOpenReduction.shriek l E j o).map (cU.app K) := by
      simp [gamma]
    rw [h]
    exact IsIso.hom_inv_id_assoc (cX.app K) _
  · intro Q F hQ hF hK hP z hup hlow
    have hi : IsIso ((q.tensorX.chi l E).app ((IntegralOpenReduction.shriek l E j o).obj
        (DerivedCategory.Q.obj Q), DerivedCategory.Q.obj F)) := (hinv (⟨_, hK⟩, ⟨_, hP⟩)).1
    have h : gamma.hom.app (⟨DerivedCategory.Q.obj Q, hK⟩, ⟨DerivedCategory.Q.obj F, hP⟩) =
        inv (cX.app (⟨_, hK⟩, ⟨_, hP⟩)) ≫ ordinary.hom.app _ ≫
          (IntegralOpenReduction.shriek l E j o).map (cU.app (⟨_, hK⟩, ⟨_, hP⟩)) := by
      simp [gamma]
    rw [h]
    simp only [Category.assoc]
    exact completedRepresentative_of_ordinary l E j o SX SU AX AU st m c q extension flat
      extendGood restrictGood ordinary _ordinary_representative Q F hQ hF z hup hlow

end WeilConjectures.OpenProjectionRoos
