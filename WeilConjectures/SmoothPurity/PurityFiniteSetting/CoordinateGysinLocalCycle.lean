/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.CoordinateGysinCycle
/-! # Local class of the explicit coefficient-unit cycle
Source: latest blueprint, `lem-pur-gysin-structure.proof.md`, second assertion.
(blueprint: lem-pur-coordinate-gysin-local-cycle).
-/
@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.RetractedSupport
namespace WeilConjectures.PurityFiniteSetting

private theorem evaluate_comp (P : PurityFiniteSetting.{u}) (T : Scheme.{u})
    {F G : ProSheaves P T} (f : P.constant T ⟶ F) (g : F ⟶ G) :
    P.gysinEvaluate T (f ≫ g) =
      (globalSectionsFunctor (Modules P) T).map g (P.gysinEvaluate T f) := by
  simp only [gysinEvaluate, Adjunction.homEquiv_naturality_right]
  rfl

private theorem local_cycle_morphism (P : PurityFiniteSetting.{u}) (T : Scheme.{u})
    (I : CochainComplex (ProSheaves P T) ℤ)
    (φ : gysinSingleComplex P T ⟶ I⟦(2 : ℤ)⟧) :
    (DerivedCategory.singleFunctorCompHomologyFunctorIso (ProSheaves P T) 0).inv.app
        (P.constant T) ≫
      (DerivedCategory.homologyFunctor (ProSheaves P T) 0).map
        (gysinChainMorphism P T I φ) ≫
      (((DerivedCategory.homologyFunctor (ProSheaves P T) 0).shiftIso
        (2 : ℤ) 0 2 (add_zero 2)).hom.app (DerivedCategory.Q.obj I)) =
    I.liftCycles (gysinChainComponent P T I φ) 3 (by simp)
        (gysinChainComponent_closed P T I φ) ≫ I.homologyπ 2 ≫
      (DerivedCategory.homologyFunctorFactors (ProSheaves P T) 2).inv.app I := by
  let S := gysinSingleComplex P T
  have hs :
      (DerivedCategory.singleFunctorCompHomologyFunctorIso (ProSheaves P T) 0).inv.app
          (P.constant T) =
        (HomologicalComplex.singleObjHomologySelfIso (.up ℤ) 0 (P.constant T)).inv ≫
          (DerivedCategory.homologyFunctorFactors (ProSheaves P T) 0).inv.app S := by
    simp only [Functor.comp_obj, Functor.id_obj,
      DerivedCategory.singleFunctorCompHomologyFunctorIso, SingleFunctors.evaluation,
      HomologicalComplex.homologyFunctorSingleIso, Iso.trans_inv, Functor.isoWhiskerRight_inv,
      Functor.mapIso_inv, DerivedCategory.singleFunctorsPostcompQIso_inv_hom,
      Functor.whiskerRight_id', Functor.isoWhiskerLeft_inv, Category.comp_id, NatTrans.comp_app,
      Functor.associator_inv_app, Functor.whiskerLeft_app, NatIso.ofComponents_inv_app]
    rfl
  rw [hs]
  change _ ≫ (DerivedCategory.homologyFunctor (ProSheaves P T) 0).shiftMap
    (ShiftedHom.map φ DerivedCategory.Q) 0 2 (add_zero 2) = _
  rw [DerivedCategory.shiftMap_homologyFunctor_map_Q φ 0 2 (add_zero 2)]
  simp only [S, Functor.shiftMap, CochainComplex.homologyFunctor_shift,
    HomologicalComplex.homologyFunctor_map, Category.assoc, Iso.inv_hom_id_app_assoc]
  rw [← HomologicalComplex.singleObjCyclesSelfIso_inv_homologyπ,
    Category.assoc, HomologicalComplex.homologyπ_naturality_assoc]
  have hz :
      (HomologicalComplex.singleObjCyclesSelfIso (.up ℤ) 0 (P.constant T)).inv ≫
        HomologicalComplex.cyclesMap φ 0 =
      (I⟦(2 : ℤ)⟧).liftCycles
        ((HomologicalComplex.singleObjXSelf (.up ℤ) 0 (P.constant T)).inv ≫ φ.f 0)
        1 (by simp) (by
          have hd : (gysinSingleComplex P T).d 0 1 = 0 := rfl
          erw [Category.assoc, φ.comm 0 1, hd, zero_comp]) := by
    apply (cancel_mono ((I⟦(2 : ℤ)⟧).iCycles 0)).mp
    simp only [Category.assoc, HomologicalComplex.cyclesMap_i,
      HomologicalComplex.liftCycles_i]
    exact HomologicalComplex.singleObjCyclesSelfIso_inv_iCycles_assoc _ _ _ _
  rw [← Category.assoc
    (HomologicalComplex.singleObjCyclesSelfIso (.up ℤ) 0 (P.constant T)).inv, hz]
  rw [CochainComplex.liftCycles_shift_homologyπ_assoc _ _ 1 (by simp) _
    2 (add_zero 2) 3 (by simp)]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
  congr 3

/-- H^0 of a chain lift, evaluated on the unit and shifted, is the local class of
Γ(φ^0)(1). This assertion contains no derived global class or local-class edge.
Source: latest blueprint, `lem-pur-gysin-structure.proof.md`, second assertion,
and step 2 of `lem-pur-coordinate-gysin-edge-evaluation`.
(blueprint: lem-pur-coordinate-gysin-local-cycle).

Proof: `shiftMap_homologyFunctor_map_Q` identifies the derived shifted homology
map with the ordinary chain homology map, with its homology-factor comparisons.
The single-object comparison identifies its source with the single-complex cycle.
Naturality of `homologyπ` gives the cycle lift of the degree-zero component of φ.
The ordinary shift comparison `liftCycles_shift_homologyπ` identifies its class
with the class of `gysinChainComponent` in degree two. Apply evaluation naturality
for the two adjunctions. By definition `gysinChainCycle` is the inverse cycle
comparison of the evaluated kernel lift, so the forward comparison cancels.
This proves the formula for every chain lift without a K-injectivity hypothesis.
The argument also applies to zero coefficients, zero maps and empty schemes. -/
theorem coordinateGysin_local_cycle (P : PurityFiniteSetting.{u}) (T : Scheme.{u})
    (I : CochainComplex (ProSheaves P T) ℤ)
    (φ : gysinSingleComplex P T ⟶ I⟦(2 : ℤ)⟧) :
    (globalSectionsFunctor (Modules P) T).map
        (((DerivedCategory.homologyFunctor (ProSheaves P T) 0).shiftIso
          (2 : ℤ) 0 2 (add_zero 2)).hom.app (DerivedCategory.Q.obj I))
        (P.gysinEvaluate T
          ((DerivedCategory.singleFunctorCompHomologyFunctorIso (ProSheaves P T) 0).inv.app
            (P.constant T) ≫
            (DerivedCategory.homologyFunctor (ProSheaves P T) 0).map
              (gysinChainMorphism P T I φ))) =
      ((gysinCycleSectionsIso P T I).hom ≫
        (globalSectionsFunctor (Modules P) T).map (I.homologyπ 2) ≫
        (globalSectionsFunctor (Modules P) T).map
          ((DerivedCategory.homologyFunctorFactors (ProSheaves P T) 2).inv.app I))
        (gysinChainCycle P T I φ) := by
  have h := congrArg (P.gysinEvaluate T) (local_cycle_morphism P T I φ)
  simp only [DerivedCategory.shift_homologyFunctor, evaluate_comp, Functor.map_comp,
    gysinChainCycle, Iso.inv_hom_id_apply, ConcreteCategory.comp_apply] at h ⊢
  exact h

end WeilConjectures.PurityFiniteSetting
