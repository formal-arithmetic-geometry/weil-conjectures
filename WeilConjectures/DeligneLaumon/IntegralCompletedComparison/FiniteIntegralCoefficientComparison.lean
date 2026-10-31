/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.IntegralCompletedComparison.IntegralPullbackCompletedComparisonData
import all WeilConjectures.ProperBaseChange.IntegralCoefficientPresentation.IntegralCoefficientPresentationComparison
import all WeilConjectures.AlgebraicGeometry.Completed.Pullback.CompletedPullbackReductionData
import WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafChangeAdjunctionSupplement

/-! # Finite integral coefficient pullback normalization

Source: Stacks Project, sites-modules.tex, Tags 03EK/03EL; proetale.tex, Tag 099N(5).
(blueprint: lem-a1-finite-integral-coefficient-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
attribute [-instance] WeilConjectures.IntegralOnSlice.abLocallyBijective
  WeilConjectures.integralOperationsAbLocallyBijective
  WeilConjectures.integralOperationsCommHasDerivedCategory
  WeilConjectures.IntegralOnSlice.hasDerived
attribute [-instance] WeilConjectures.integralOperationsAbSheafify
  WeilConjectures.integralOperationsSiteSmall
attribute [local irreducible] HasDerivedCategory.standard CategoryTheory.constantSheaf
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [local instance 5000] WeilConjectures.integralTowerHasDerivedCategory
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures
private instance (priority := 6000) fixedAbSheafify (W : Scheme.{u}) :
    HasSheafify (ProEt.topology W) AddCommGrpCat.{u + 1} :=
  integralCoefficientAbSheafify.{u, u} W
private instance (priority := 6000) fixedAbBijective (W : Scheme.{u}) :
    (ProEt.topology W).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  integralCoefficientAbLocallyBijective.{u, u} W
namespace WeilConjectures.IntegralCompletedComparison
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {X Y : Scheme.{u}} (g : X ⟶ Y)

private abbrev completedCoeff (W : Scheme.{u}) :=
  ImmersionCompletedPullback.completedRingIso l E W

private abbrev finiteCoeff (W : Scheme.{u}) (n : ℕ) :=
  ImmersionCompletedPullback.finiteRingIso l E W n

private theorem projection_square (W : Scheme.{u}) (n : ℕ) :
    (completedCoeff l E W).inv ≫ pbcAdicProjection W (pbcIntegralDatum l E) n =
      completedIntegralCommRingProjectionUnrestricted l E W n ≫
        (finiteCoeff l E W n).inv := by
  have h := (ImmersionCompletedPullback.completedRingIso_exists l E W).exists.choose_spec n
  change (completedCoeff l E W).hom ≫ _ = _ at h
  apply (cancel_mono (finiteCoeff l E W n).hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← h, Iso.inv_hom_id_assoc]

private def restrictionSquare (W : Scheme.{u}) (n : ℕ) :=
  (IntegralCoefficientPresentation.restrictionSquare
    (completedCoeff l E W).inv (pbcAdicProjection W (pbcIntegralDatum l E) n)
    (completedIntegralCommRingProjectionUnrestricted l E W n)
    (finiteCoeff l E W n).inv (projection_square l E W n)).symm

private def integralAdj (W : Scheme.{u}) (n : ℕ) :
    unrestrictedIntegralReductionFunctor.{u, u} l E W n ⊣
      scalarReductionRestriction.{u, u} l E W n :=
  (scalarReductionExtension_adjunction.{u, u} l E W n).choose

private theorem integralAdj_unit (W : Scheme.{u}) (n : ℕ)
    (M : integralTowerModules.{u, u} l E W) (U : W.ProEtᵒᵖ) (x : M.val.obj U) :
    ((integralAdj l E W n).unit.app M).val.app U x =
      unrestrictedIntegralTensorSection.{u, u} l E W n M U 1 x := by
  exact (scalarReductionExtension_adjunction.{u, u} l E W n).choose_spec M U x

private theorem reductionComparison_exists (W : Scheme.{u}) (n : ℕ) :
    ∃ a : modules l E W ⋙ unrestrictedIntegralReductionFunctor.{u, u} l E W n ≅
        reductionChange W (pbcAdicProjection W (pbcIntegralDatum l E) n) ⋙
          pbcRestrict (finiteCoeff l E W n).inv,
      ∀ M, (integralAdj l E W n).unit.app ((modules l E W).obj M) ≫
        (scalarReductionRestriction.{u, u} l E W n).map (a.hom.app M) ≫
        (restrictionSquare l E W n).hom.app
          ((reductionChange W (pbcAdicProjection W (pbcIntegralDatum l E) n)).obj M) =
        (modules l E W).map
          ((pbcScalarAdjunction (pbcAdicProjection W (pbcIntegralDatum l E) n)).unit.app M) := by
  have := (IntegralCoefficientPresentation.restrict_equivalence
    (completedCoeff l E W)).2.1
  have := (IntegralCoefficientPresentation.restrict_equivalence
    (finiteCoeff l E W n)).2.1
  exact IntegralCoefficientPresentation.square_iso (integralAdj l E W n)
    (pbcScalarAdjunction (pbcAdicProjection W (pbcIntegralDatum l E) n))
    (modules l E W) (pbcRestrict (finiteCoeff l E W n).inv)
    (restrictionSquare l E W n)

private def finiteStructure (n : ℕ) :
    (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj
        (integralCoefficientCommRingSheaf l E Y n) ≅
      integralCoefficientCommRingSheaf l E X n :=
  (proEtaleSheafInverseImage g CommRingCat.{u + 1}).mapIso
      (finiteCoeff l E Y n).symm ≪≫
    asIso (completedFiniteCoefficientMap g (pbcIntegralDatum l E) n) ≪≫
      finiteCoeff l E X n

private theorem finiteStructure_hom (n : ℕ) :
    (finiteStructure l E g n).hom =
      proEtaleConstantInverseImageMap g CommRingCat.{u + 1}
        (CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))) := by
  apply (cancel_epi ((proEtaleSheafInverseImage g CommRingCat.{u + 1}).map
    (finiteCoeff l E Y n).hom)).1
  dsimp only [finiteStructure, Iso.trans_hom, Functor.mapIso_hom,
    Iso.symm_hom, asIso_hom]
  simp only [← Functor.map_comp_assoc, Iso.hom_inv_id]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]
  symm
  dsimp only [finiteCoeff, ImmersionCompletedPullback.finiteRingIso,
    completedFiniteCoefficientMap, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
  simp only [Functor.map_comp, Category.assoc, Iso.hom_inv_id_assoc]
  exact congrArg (fun z ↦ (proEtaleSheafInverseImage g CommRingCat.{u + 1}).map
    (pbcLevelConstantComparison Y (pbcIntegralDatum l E) n).inv ≫ z)
      (proEtaleConstantInverseImageMap_naturality g
        (ImmersionCompletedPullback.quotientEquiv l E n).toCommRingCatIso.hom)

private theorem finiteDirect_eq (n : ℕ) :
    proEtaleRingModuleDirectImage g (integralCoefficientCommRingSheaf l E Y n)
        (integralCoefficientCommRingSheaf l E X n) (finiteStructure l E g n) =
      coefficientProEtaleModuleDirectImage.{u, u} g
        (CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))) := by
  unfold proEtaleRingModuleDirectImage proEtaleRingDirectImageMap
  rw [finiteStructure_hom]
  change SheafOfModules.pushforward _ = SheafOfModules.pushforward _
  congr 1
  apply Sheaf.hom_ext
  change Functor.whiskerRight _ _ = Functor.whiskerRight _ _
  congr 1
  apply congrArg (fun z : integralCoefficientCommRingSheaf l E Y n ⟶
    (proEtaleSheafDirectImage g CommRingCat.{u + 1}).obj
      (integralCoefficientCommRingSheaf l E X n) ↦ z.hom)
  exact ((proEtaleSheafAdjunction g CommRingCat.{u + 1}).homEquiv _ _).apply_symm_apply _

private theorem finiteStructure_square (n : ℕ) :
    (finiteStructure l E g n).hom ≫ (finiteCoeff l E X n).inv =
      (proEtaleSheafInverseImage g CommRingCat.{u + 1}).map
        (finiteCoeff l E Y n).inv ≫
          (asIso (completedFiniteCoefficientMap g (pbcIntegralDatum l E) n)).hom := by
  simp only [finiteStructure, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
    Category.assoc, Iso.hom_inv_id, Category.comp_id]

private def finiteDirectSquare (n : ℕ) :=
  proEtaleRingRestrictionDirectImage g
    (integralCoefficientCommRingSheaf l E Y n) (reductionCoefficient Y (pbcIntegralDatum l E) n)
    (integralCoefficientCommRingSheaf l E X n) (reductionCoefficient X (pbcIntegralDatum l E) n)
    (finiteCoeff l E Y n).inv (finiteCoeff l E X n).inv
    (finiteStructure l E g n)
    (asIso (completedFiniteCoefficientMap g (pbcIntegralDatum l E) n))
    (finiteStructure_square l E g n)

private def pullbackRightSquare (n : ℕ) :=
  Functor.isoWhiskerLeft (pbcRestrict (finiteCoeff l E X n).inv)
      (eqToIso (finiteDirect_eq l E g n)).symm ≪≫
    (finiteDirectSquare l E g n).symm

private theorem pullbackComparison_exists (n : ℕ) :
    ∃ b : pbcRestrict (finiteCoeff l E Y n).inv ⋙ integralOperationsLevelPullback l E g n ≅
        completedReductionFiniteModules g (pbcIntegralDatum l E) n ⋙
          pbcRestrict (finiteCoeff l E X n).inv,
      ∀ M,
        (coefficientProEtaleModuleAdjunction.{u, u} g
          (CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))))).unit.app
            ((pbcRestrict (finiteCoeff l E Y n).inv).obj M) ≫
          (coefficientProEtaleModuleDirectImage.{u, u} g
            (CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))))).map
              (b.hom.app M) ≫
          (pullbackRightSquare l E g n).hom.app
            ((completedReductionFiniteModules g (pbcIntegralDatum l E) n).obj M) =
          (pbcRestrict (finiteCoeff l E Y n).inv).map
            ((proEtaleRingModuleAdjunction g _ _
              (asIso (completedFiniteCoefficientMap g (pbcIntegralDatum l E) n))).unit.app M) := by
  have := (IntegralCoefficientPresentation.restrict_equivalence
    (finiteCoeff l E Y n)).2.1
  have := (IntegralCoefficientPresentation.restrict_equivalence
    (finiteCoeff l E X n)).2.1
  exact IntegralCoefficientPresentation.square_iso
    (coefficientProEtaleModuleAdjunction.{u, u} g
      (CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))))
    (proEtaleRingModuleAdjunction g _ _
      (asIso (completedFiniteCoefficientMap g (pbcIntegralDatum l E) n)))
    (pbcRestrict (finiteCoeff l E Y n).inv) (pbcRestrict (finiteCoeff l E X n).inv)
    (pullbackRightSquare l E g n)

private theorem restrictionSquare_sections (W : Scheme.{u}) (n : ℕ)
    (M : pbcModules W (reductionCoefficient W (pbcIntegralDatum l E) n))
    (U : W.ProEtᵒᵖ) (x : M.val.obj U) :
    ((restrictionSquare l E W n).hom.app M).val.app U x = x := by
  let r := IntegralCoefficientPresentation.restrictionSquare
    (completedCoeff l E W).inv (pbcAdicProjection W (pbcIntegralDatum l E) n)
    (completedIntegralCommRingProjectionUnrestricted l E W n)
    (finiteCoeff l E W n).inv (projection_square l E W n)
  have h := congrArg (fun k ↦ k.val.app U x) (r.inv_hom_id_app M)
  change (r.hom.app M).val.app U ((r.inv.app M).val.app U x) = x at h
  rw [IntegralCoefficientPresentation.restrictionSquare_hom] at h
  exact h

private def reductionComparison (W : Scheme.{u}) (n : ℕ) :=
  (reductionComparison_exists l E W n).choose

private theorem reductionComparison_unit (W : Scheme.{u}) (n : ℕ)
    (M : pbcModules W (pbcAdicCompletion W (pbcIntegralDatum l E)))
    (U : W.ProEtᵒᵖ) (x : M.val.obj U) :
    ((reductionComparison l E W n).hom.app M).val.app U
      (unrestrictedIntegralTensorSection l E W n ((modules l E W).obj M) U 1 x) =
      pbcTensorSection (pbcAdicProjection W (pbcIntegralDatum l E) n) M U 1 x := by
  have h := congrArg (fun k ↦ k.val.app U x)
    ((reductionComparison_exists l E W n).choose_spec M)
  change ((restrictionSquare l E W n).hom.app _).val.app U
    (((reductionComparison l E W n).hom.app M).val.app U
      (((integralAdj l E W n).unit.app ((modules l E W).obj M)).val.app U x)) =
    ((pbcScalarAdjunction (pbcAdicProjection W (pbcIntegralDatum l E) n)).unit.app M).val.app
      U x at h
  rw [restrictionSquare_sections, integralAdj_unit] at h
  exact h.trans
    ((pbcScalarAdjunction_exists (pbcAdicProjection W (pbcIntegralDatum l E) n)).exists.choose_spec
      M U x)

private theorem eqToIso_inv_sections
    {W : Scheme.{u}} {R : Sheaf (ProEt.topology W) RingCat.{u + 1}}
    {C : Type*} [Category C] {F G : C ⥤ SheafOfModules.{u + 1} R}
    (h : F = G) (M : C) (U : W.ProEtᵒᵖ) (x : (G.obj M).val.obj U) :
    HEq (((eqToIso h).inv.app M).val.app U x) x := by
  subst G
  rfl

private theorem finiteDirectSquare_inv_sections (n : ℕ)
    (M : pbcModules X (reductionCoefficient X (pbcIntegralDatum l E) n))
    (V : Y.ProEtᵒᵖ) (x : M.val.obj ((proEtaleBaseChange g).op.obj V)) :
    ((finiteDirectSquare l E g n).inv.app M).val.app V x = x := by
  let d := finiteDirectSquare l E g n
  have h := congrArg (fun k ↦ k.val.app V x) (d.inv_hom_id_app M)
  change (d.hom.app M).val.app V ((d.inv.app M).val.app V x) = x at h
  rw [show (d.hom.app M).val.app V ((d.inv.app M).val.app V x) =
      (d.inv.app M).val.app V x from
    (Classical.choose_spec (proEtaleRingRestrictionDirectImage_existsUnique g
      (integralCoefficientCommRingSheaf l E Y n)
      (reductionCoefficient Y (pbcIntegralDatum l E) n)
      (integralCoefficientCommRingSheaf l E X n)
      (reductionCoefficient X (pbcIntegralDatum l E) n)
      (finiteCoeff l E Y n).inv (finiteCoeff l E X n).inv
      (finiteStructure l E g n)
      (asIso (completedFiniteCoefficientMap g (pbcIntegralDatum l E) n))
      (finiteStructure_square l E g n))).1 M V _] at h
  exact h

private theorem pullbackRightSquare_sections (n : ℕ)
    (M : pbcModules X (reductionCoefficient X (pbcIntegralDatum l E) n))
    (V : Y.ProEtᵒᵖ) (x : M.val.obj ((proEtaleBaseChange g).op.obj V)) :
    ((pullbackRightSquare l E g n).hom.app M).val.app V x = x := by
  change ((finiteDirectSquare l E g n).inv.app M).val.app V
    (((eqToIso (finiteDirect_eq l E g n)).inv.app
      ((pbcRestrict (finiteCoeff l E X n).inv).obj M)).val.app V x) = x
  rw [finiteDirectSquare_inv_sections]
  exact eq_of_heq (eqToIso_inv_sections (finiteDirect_eq l E g n)
    ((pbcRestrict (finiteCoeff l E X n).inv).obj M) V x)

private def pullbackComparison (n : ℕ) := (pullbackComparison_exists l E g n).choose

private theorem pullbackComparison_unit (n : ℕ)
    (M : pbcModules Y (reductionCoefficient Y (pbcIntegralDatum l E) n))
    (V : Y.ProEt) (x : M.val.obj (op V)) :
    ((pullbackComparison l E g n).hom.app M).val.app (op ((proEtaleBaseChange g).obj V))
      (integralOperationsPullbackGenerator l E g n
        ((pbcRestrict (finiteCoeff l E Y n).inv).obj M) V x) =
      ((proEtaleRingModuleAdjunction g _ _
        (asIso (completedFiniteCoefficientMap g (pbcIntegralDatum l E) n))).unit.app M).val.app
          (op V) x := by
  have h := congrArg (fun k ↦ k.val.app (op V) x)
    ((pullbackComparison_exists l E g n).choose_spec M)
  change ((pullbackRightSquare l E g n).hom.app
    ((completedReductionFiniteModules g (pbcIntegralDatum l E) n).obj M)).val.app (op V)
    (((pullbackComparison l E g n).hom.app M).val.app (op ((proEtaleBaseChange g).obj V))
      (integralOperationsPullbackGenerator l E g n
        ((pbcRestrict (finiteCoeff l E Y n).inv).obj M) V x)) = _ at h
  rw [pullbackRightSquare_sections] at h
  exact h

private theorem integralGenerator_map (n : ℕ)
    {M N : integralOperationsFiniteModules l E Y n} (a : M ⟶ N)
    (V : Y.ProEt) (x : M.val.obj (op V)) :
    ((integralOperationsLevelPullback l E g n).map a).val.app
        (op ((proEtaleBaseChange g).obj V))
        (integralOperationsPullbackGenerator l E g n M V x) =
      integralOperationsPullbackGenerator l E g n N V (a.val.app (op V) x) := by
  exact (congrArg (fun k ↦ k.val.app (op V) x)
    ((coefficientProEtaleModuleAdjunction.{u, u} g
      (CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))))).unit.naturality
        a)).symm

private def finalRestrictionSquare (n : ℕ) :=
  IntegralCoefficientPresentation.restrictionSquare
    (completedIntegralCommRingProjectionUnrestricted l E X n) (finiteCoeff l E X n).inv
    (completedCoeff l E X).inv (pbcAdicProjection X (pbcIntegralDatum l E) n)
    (projection_square l E X n).symm

private theorem finalRestrictionSquare_sections (n : ℕ)
    (M : pbcModules X (reductionCoefficient X (pbcIntegralDatum l E) n))
    (U : X.ProEtᵒᵖ) (x : M.val.obj U) :
    ((finalRestrictionSquare l E (X := X) n).hom.app M).val.app U x = x := by
  exact IntegralCoefficientPresentation.restrictionSquare_hom _ _ _ _ _ M U x

private def comparison (n : ℕ) : finiteIntegral l E g n ≅ finiteCompleted l E g n :=
  Functor.isoWhiskerRight (reductionComparison l E Y n)
      (integralOperationsLevelPullback l E g n ⋙
        pbcRestrict (completedIntegralCommRingProjectionUnrestricted l E X n)) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (reductionChange Y (pbcAdicProjection Y (pbcIntegralDatum l E) n))
      ((Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (pullbackComparison l E g n)
          (pbcRestrict (completedIntegralCommRingProjectionUnrestricted l E X n)) ≪≫
        Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft (completedReductionFiniteModules g (pbcIntegralDatum l E) n)
          (finalRestrictionSquare l E (X := X) n)) ≪≫
    (Functor.associator _ _ _).symm

private theorem finiteGenerator_unit (n : ℕ)
    (M : pbcModules Y (pbcAdicCompletion Y (pbcIntegralDatum l E)))
    (V : Y.ProEt) (x : M.val.obj (op V)) :
    ((proEtaleRingModuleAdjunction g _ _
      (asIso (completedFiniteCoefficientMap g (pbcIntegralDatum l E) n))).unit.app
        ((reductionChange Y (pbcAdicProjection Y (pbcIntegralDatum l E) n)).obj M)).val.app
          (op V) (pbcTensorSection (pbcAdicProjection Y (pbcIntegralDatum l E) n) M (op V) 1 x) =
      completedReductionFiniteGenerator g (pbcIntegralDatum l E) n M V
        ((proEtaleBaseChange g).obj V) (𝟙 _) 1 1 x := by
  have h := ringAdjunction_generator g
    (reductionCoefficient Y (pbcIntegralDatum l E) n)
    (reductionCoefficient X (pbcIntegralDatum l E) n)
    (asIso (completedFiniteCoefficientMap g (pbcIntegralDatum l E) n))
    ((reductionChange Y (pbcAdicProjection Y (pbcIntegralDatum l E) n)).obj M)
    _ (𝟙 _) V (pbcTensorSection (pbcAdicProjection Y (pbcIntegralDatum l E) n) M (op V) 1 x)
  rw [Adjunction.homEquiv_id] at h
  simp only [SheafOfModules.id_val, PresheafOfModules.id_app, ModuleCat.id_apply] at h
  refine h.trans ?_
  unfold completedReductionFiniteGenerator completedReductionFiniteTensor ringTensor
  rfl

attribute [local irreducible] pbcIntegralDatum reductionComparison pullbackComparison

set_option linter.unusedVariables false in
/-- The two ordinary finite coefficient pullbacks have their normalized comparison.

Source: Stacks Project, sites-modules.tex, Tags 03EK and 03EL; the finite-generator
part of lem-a1-completed-integral-finite-tower-transport.
(blueprint: lem-a1-finite-integral-coefficient-comparison).

Proof: identify the positive quotient rings by the unique isomorphisms sending
the class of each integral coefficient to its lifted class. The completed ring
isomorphisms intertwine these quotient maps. Inverse image preserves these
coefficient isomorphisms. Associate scalar extension with inverse image and
restrict along the completed projections. Both resulting functors identify with
the sheafification of the balanced inverse-image tensor over the finite quotient.
Send a pure tensor to the same pure tensor under the coefficient isomorphisms;
the inverse uses their inverses. Balancing follows from the projection square.
The maps commute with restrictions and module morphisms, so sheafification gives
a natural isomorphism for every level. The unit coefficient maps to the unit;
hence the pulled quotient-unit generator has exactly the specified completed
finite-generator value. This is FiniteNormalization. The construction works on
the zero module and on the empty site, and uses only positive exponents n+1. -/
theorem finiteIntegral_coefficientComparison
    (hX : ∀ x : X, IsUnit (l : X.presheaf.stalk x))
    (hY : ∀ y : Y, IsUnit (l : Y.presheaf.stalk y)) :
    ∃ e : ∀ n : ℕ, finiteIntegral l E g n ≅ finiteCompleted l E g n,
      ∀ n : ℕ, FiniteNormalization l E g n (e n) := by
  refine ⟨comparison l E g, ?_⟩
  intro n M V x
  dsimp only [comparison, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app]
  simp only [Category.id_comp]
  change ((finalRestrictionSquare l E (X := X) n).hom.app
      ((completedReductionFiniteModules g (pbcIntegralDatum l E) n).obj
        ((reductionChange Y (pbcAdicProjection Y (pbcIntegralDatum l E) n)).obj M))).val.app
          (op ((proEtaleBaseChange g).obj V))
    (((pullbackComparison l E g n).hom.app
      ((reductionChange Y (pbcAdicProjection Y (pbcIntegralDatum l E) n)).obj M)).val.app
        (op ((proEtaleBaseChange g).obj V))
      (((integralOperationsLevelPullback l E g n).map
        ((reductionComparison l E Y n).hom.app M)).val.app _
          (integralOperationsPullbackGenerator l E g n _ V
            (unrestrictedIntegralTensorSection l E Y n ((modules l E Y).obj M) (op V) 1 x)))) = _
  rw [finalRestrictionSquare_sections]
  erw [integralGenerator_map]
  erw [reductionComparison_unit]
  erw [pullbackComparison_unit]
  exact finiteGenerator_unit l E g n M V x

end WeilConjectures.IntegralCompletedComparison
