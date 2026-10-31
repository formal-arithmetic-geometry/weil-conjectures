/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.FrobeniusCoefficientTwists.FrobeniusCoefficientTwistsCanonical
public import WeilConjectures.SmoothPurity.Supporting.ConstantWeilStructure
import all WeilConjectures.SmoothPurity.Supporting.ConstantWeilStructure

/-! # Agreement of the degree-zero root-line and constant Weil structures -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [local instance_reducible] WeilConjectures.PurCompactSupport.completed
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures.NativeCoefficientCohomology
open FrobeniusCoefficientTwists

private def zeroChainIso (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g] :
    ((modulePull l E g).mapHomologicalComplex (.up ℤ)).obj
      (constantWeilIntegralComplex l E Y) ≅ constantWeilIntegralComplex l E X :=
  ((modulePull l E g).mapCochainComplexSingleFunctor 0).app
      (positiveLine l E Y 0) ≪≫
    (CochainComplex.singleFunctor _ 0).mapIso (positiveLineMaps l E g 0)

set_option maxHeartbeats 1200000 in
-- Sectionwise coefficient transports expand several scalar models.
private theorem zeroChainIso_one (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g] (V : Y.ProEt) :
    ((zeroChainIso l E g).hom.f 0).val.app (op ((proEtaleBaseChange g).obj V))
      (moduleSection l E g ((constantWeilIntegralComplex l E Y).X 0) V
        (constantWeilUnitSection l E Y V)) =
      constantWeilUnitSection l E X ((proEtaleBaseChange g).obj V) := by
  let sY := HomologicalComplex.singleObjXSelf (.up ℤ) 0 (positiveLine l E Y 0)
  let sX := HomologicalComplex.singleObjXSelf (.up ℤ) 0 (positiveLine l E X 0)
  have he : (modulePull l E g).map sY.inv ≫ (zeroChainIso l E g).hom.f 0 =
      (positiveLineMaps l E g 0).hom ≫ sX.inv := by
    simp only [zeroChainIso, Iso.trans_hom, HomologicalComplex.comp_f,
      Functor.mapIso_hom, Iso.app_hom, Functor.mapCochainComplexSingleFunctor,
      HomologicalComplex.singleMapHomologicalComplex_hom_app_self,
      CochainComplex.singleFunctor, CochainComplex.singleFunctors,
      HomologicalComplex.single_map_f_self, Category.assoc,
      ← Functor.map_comp_assoc,
      Iso.inv_hom_id, Iso.inv_hom_id_assoc,
      sY, sX]
    erw [CategoryTheory.Functor.map_id, Category.id_comp]
  let adj := proEtaleRingModuleAdjunction g
    ((PurCompactSupport.completed l E).ring Y)
    ((PurCompactSupport.completed l E).ring X)
    ((PurCompactSupport.completed l E).pull g)
  have hn := congrArg (fun f ↦ f.val.app (op V)
    (1 : (completedIntegralCoefficientSheafUnrestricted l E Y).obj.obj (op V)))
      (adj.unit.naturality sY.inv)
  change moduleSection l E g ((constantWeilIntegralComplex l E Y).X 0) V
      (constantWeilUnitSection l E Y V) =
    ((modulePull l E g).map sY.inv).val.app (op ((proEtaleBaseChange g).obj V))
      (moduleSection l E g (positiveLine l E Y 0) V
        (1 : (completedIntegralCoefficientSheafUnrestricted l E Y).obj.obj (op V))) at hn
  rw [hn]
  change (((modulePull l E g).map sY.inv ≫
    (zeroChainIso l E g).hom.f 0).val.app _) _ = _
  rw [he]
  have hz := (existsUnique_positiveLineMaps l E g).exists.choose_spec 0 V
    (1 : (completedIntegralCoefficientSheafUnrestricted l E Y).obj.obj (op V))
    (fun i ↦ Fin.elim0 i)
  change (positiveLineMaps l E g 0).hom.val.app _
    (moduleSection l E g (positiveLine l E Y 0) V
        (1 : (completedIntegralCoefficientSheafUnrestricted l E Y).obj.obj (op V))) =
      (sfCompletedCoefficientMap l E g).hom.app (op V) 1 at hz
  change sX.inv.val.app (op ((proEtaleBaseChange g).obj V))
      ((positiveLineMaps l E g 0).hom.val.app (op ((proEtaleBaseChange g).obj V))
        (moduleSection l E g (positiveLine l E Y 0) V
          (1 : (completedIntegralCoefficientSheafUnrestricted l E Y).obj.obj (op V)))) =
    constantWeilUnitSection l E X ((proEtaleBaseChange g).obj V)
  erw [hz, map_one]
  rfl

set_option maxHeartbeats 1200000 in
-- The two strict cone components contain the completed coefficient tower.
private theorem zeroChainIso_roos (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g] :
    (zeroChainIso l E g).inv ≫
      (pullbackAugmentation l E g).app (constantWeilIntegralComplex l E Y) =
        constantWeilChainUnit l E g := by
  apply (constantWeilChainUnit_existsUnique l E g).unique
  · constructor
    · intro n V
      have hi : ((zeroChainIso l E g).inv.f 0).val.app
          (op ((proEtaleBaseChange g).obj V))
          (constantWeilUnitSection l E X ((proEtaleBaseChange g).obj V)) =
        moduleSection l E g ((constantWeilIntegralComplex l E Y).X 0) V
          (constantWeilUnitSection l E Y V) := by
        rw [← zeroChainIso_one l E g V]
        exact congrArg (fun f ↦ f.val.app (op ((proEtaleBaseChange g).obj V))
          (moduleSection l E g ((constantWeilIntegralComplex l E Y).X 0) V
            (constantWeilUnitSection l E Y V)))
          (congrArg (fun f ↦ f.f 0) (zeroChainIso l E g).hom_inv_id)
      simp only [HomologicalComplex.comp_f, Category.assoc, SheafOfModules.comp_val,
        PresheafOfModules.comp_app, ModuleCat.comp_apply]
      erw [hi]
      have h := (existsUnique_pullbackAugmentation l E g).exists.choose_spec.1
        (constantWeilIntegralComplex l E Y) 0 n V (constantWeilUnitSection l E Y V)
      have hx : unrestrictedIntegralTensorSection l E Y n
          ((constantWeilIntegralComplex l E Y).X 0) (op V) 1
          (constantWeilUnitSection l E Y V) = constantWeilReducedUnitSection l E Y n V := by
        unfold constantWeilReducedUnitSection constantWeilUnitSection
        rw [reduction_map_tensor]
        rfl
      exact h.trans (congrArg (integralOperationsPullbackGenerator l E g n _ V) hx)
    · intro i
      simp only [HomologicalComplex.comp_f, Category.assoc]
      have h := (existsUnique_pullbackAugmentation l E g).exists.choose_spec.2
        (constantWeilIntegralComplex l E Y) i
      change ((pullbackAugmentation l E g).app (constantWeilIntegralComplex l E Y)).f i ≫
        (CochainComplex.mappingCocone.snd
          (constantWeilPullbackRoosEndomorphism l E g)).v i (i - 1) (by omega) = 0 at h
      erw [h]
      simp only [comp_zero]
  · exact (constantWeilChainUnit_existsUnique l E g).exists.choose_spec

set_option maxHeartbeats 1200000 in
-- Compare the normalized derived maps on their actual good representatives.
/-- The degree-zero root line carries the published constant Weil structure.

Source: coefficient-twist conventions and the normalized strict Roos coefficient unit.
(blueprint: lem-sf-coefficient-tate-zero-normalization).

Proof: the positive-line comparison in degree zero sends the adjunction unit of
one to one. Its single-complex comparison therefore sends the corresponding unit
section to the regular unit section. Precompose the normalized ordinary-to-Roos
augmentation with the inverse of this comparison. Its finite product components
are the prescribed reductions of one and its shifted cone components vanish.
Uniqueness of the strict constant chain unit identifies these chain maps. After
localization, the exact single comparison cancels the ordinary derived factor.
The remaining inverse augmentation is the constant Roos structure, which is also
the constant integral theta after its termwise comparison and inverse cancel. -/
theorem coefficient_tate_zero_normalization
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] :
    (integralDerivedLineMap l E g 0).hom = (constantWeilIntegralTheta l E g).hom := by
  have ht : signedLineMaps l E g (0 : ℤ) = positiveLineMaps l E g 0 :=
    eq_of_heq ((existsUnique_signedLineMaps l E g).exists.choose_spec.1 0)
  have hl := (existsUnique_completedToOrdinary l E g).exists.choose_spec
    (constantWeilIntegralComplex l E Y) (constantWeilIntegralComplex_good l E Y)
    (sfIntegralTwistingCoefficient l E Y 0).property
  change (completedToOrdinary l E g).hom.app (sfIntegralTwistingCoefficient l E Y 0) =
    (completedToOrdinaryOnGood l E g (constantWeilIntegralComplex l E Y)
      (constantWeilIntegralComplex_good l E Y)
      (sfIntegralTwistingCoefficient l E Y 0).property).hom at hl
  have hchain := congrArg DerivedCategory.Q.map (zeroChainIso_roos l E g)
  rw [Functor.map_comp] at hchain
  have hloc : (ordinaryDerivedLineMap l E g 0).inv ≫
      (modulePull l E g).mapDerivedCategoryFactors.hom.app
        (constantWeilIntegralComplex l E Y) =
      DerivedCategory.Q.map (zeroChainIso l E g).inv := by
    have h := Functor.mapDerivedCategorySingleFunctor_inv_app_mapDerivedCategoryFactors_hom_app
      (modulePull l E g) (positiveLine l E Y 0)
    change ((modulePull l E g).mapDerivedCategorySingleFunctor 0).inv.app
        (positiveLine l E Y 0) ≫
        (modulePull l E g).mapDerivedCategoryFactors.hom.app
          (constantWeilIntegralComplex l E Y) = _ at h
    dsimp only [ordinaryDerivedLineMap, Iso.trans_inv, Functor.mapIso_inv, Iso.app_inv]
    rw [ht]
    erw [Category.assoc, h]
    change DerivedCategory.Q.map
        ((CochainComplex.singleFunctor _ 0).map (positiveLineMaps l E g 0).inv) ≫
        DerivedCategory.Q.map
          (((modulePull l E g).mapCochainComplexSingleFunctor 0).inv.app
            (positiveLine l E Y 0)) = _
    rw [← Functor.map_comp]
    rfl
  have := pullbackAugmentation_isIso l E g (constantWeilIntegralComplex l E Y)
    (constantWeilIntegralComplex_good l E Y)
    (sfIntegralTwistingCoefficient l E Y 0).property
  have hi : (constantWeilIntegralTheta l E g).hom ≫
      (ordinaryDerivedLineMap l E g 0).inv =
      (completedToOrdinary l E g).hom.app (sfIntegralTwistingCoefficient l E Y 0) := by
    rw [hl]
    apply (cancel_mono ((modulePull l E g).mapDerivedCategoryFactors.hom.app
      (constantWeilIntegralComplex l E Y) ≫
      DerivedCategory.Q.map ((pullbackAugmentation l E g).app
        (constantWeilIntegralComplex l E Y)))).mp
    simp only [Category.assoc]
    rw [← Category.assoc (ordinaryDerivedLineMap l E g 0).inv, hloc, hchain]
    simp only [constantWeilIntegralTheta, constantWeilIntegralLambda,
      constantWeilIntegralRoosComparison, completedToOrdinaryOnGood,
      Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv, Iso.app_hom,
      Iso.app_inv, Category.assoc, Iso.inv_hom_id_assoc]
    have := constantWeilChainUnit_isIso l E g
    have hc : (asIso (DerivedCategory.Q.map (constantWeilChainUnit l E g))).inv ≫
        DerivedCategory.Q.map (constantWeilChainUnit l E g) = 𝟙 _ :=
      (asIso (DerivedCategory.Q.map (constantWeilChainUnit l E g))).inv_hom_id
    have ha : (asIso (DerivedCategory.Q.map ((pullbackAugmentation l E g).app
        (constantWeilIntegralComplex l E Y)))).inv ≫
        DerivedCategory.Q.map ((pullbackAugmentation l E g).app
          (constantWeilIntegralComplex l E Y)) = 𝟙 _ :=
      (asIso (DerivedCategory.Q.map ((pullbackAugmentation l E g).app
        (constantWeilIntegralComplex l E Y)))).inv_hom_id
    erw [Iso.inv_hom_id_app_assoc, hc, ha, Category.comp_id]
  dsimp only [integralDerivedLineMap, Iso.trans_hom, Iso.app_hom]
  rw [← hi]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

end WeilConjectures.NativeCoefficientCohomology
