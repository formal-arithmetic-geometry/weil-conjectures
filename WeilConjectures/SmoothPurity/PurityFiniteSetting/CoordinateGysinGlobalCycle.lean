/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.CoordinateGysinCycle
import WeilConjectures.CategoryTheory.RightDerivedSingleZeroUnit
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.UnitShift
import WeilConjectures.CategoryTheory.DerivedCategory.ProjectiveSingleHom
/-! # Global class of the explicit coefficient-unit cycle
Source: latest blueprint, `lem-pur-gysin-structure.proof.md`, second assertion.
(blueprint: lem-pur-coordinate-gysin-global-cycle).
-/
@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.RetractedSupport
namespace WeilConjectures.PurityFiniteSetting

section DerivedUnit
variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D]
  [CategoryTheory.Abelian.HasKInjectiveResolutions C]

private def chainDerivedUnit (F : C ⥤ D) [F.Additive] :
    F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ F.rightDerivedFunctor :=
  (Functor.isoWhiskerLeft _ (DerivedCategory.quotientCompQhIso D)).inv ≫
    (Functor.associator _ _ _).inv ≫
    (Functor.isoWhiskerRight (F.mapHomotopyCategoryFactors (.up ℤ)) _).inv ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft _ F.rightDerivedFunctorUnit ≫
    (Functor.associator _ _ _).inv ≫
    (Functor.isoWhiskerRight (DerivedCategory.quotientCompQhIso C) _).hom

private instance (F : C ⥤ D) [F.Additive] :
    NatTrans.CommShift (chainDerivedUnit F) ℤ := by
  dsimp only [chainDerivedUnit, Functor.isoWhiskerLeft_inv,
    Functor.isoWhiskerRight_inv, Functor.isoWhiskerRight_hom]
  infer_instance

private theorem chainDerivedUnit_single (F : C ⥤ D) [F.Additive] (M : C) :
    DerivedCategory.Q.map ((F.mapCochainComplexSingleFunctor 0).inv.app M) ≫
      (chainDerivedUnit F).app ((CochainComplex.singleFunctor C 0).obj M) =
        F.rightDerivedSingleUnit M := by
  simp only [chainDerivedUnit, Functor.isoWhiskerLeft_inv, Functor.whiskerLeft_app,
    Functor.isoWhiskerRight_inv, Functor.whiskerRight_app, NatTrans.comp_app,
    Functor.associator_inv_app, Functor.associator_hom_app,
    Functor.isoWhiskerRight_hom, Category.id_comp]
  simp only [Functor.mapHomotopyCategoryFactors, Quotient.lift.isLift_inv,
    Functor.rightDerivedSingleUnit, DerivedCategory.quotientCompQhIso,
    HomologicalComplexUpToQuasiIso.quotientCompQhIso, Quotient.lift.isLift_hom]
  erw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id,
    Category.id_comp, Category.comp_id, Category.id_comp]

private theorem chainDerivedUnit_injective (F : C ⥤ D) [F.Additive]
    (I : CochainComplex C ℤ) [I.IsKInjective] :
    (chainDerivedUnit F).app I = (F.rightDerivedFunctorObjQIso I).inv := by
  simp only [chainDerivedUnit, Functor.isoWhiskerLeft_inv, Functor.whiskerLeft_app,
    Functor.isoWhiskerRight_inv, Functor.whiskerRight_app, NatTrans.comp_app,
    Functor.associator_inv_app, Functor.associator_hom_app,
    Functor.isoWhiskerRight_hom, Category.id_comp]
  simp [Functor.rightDerivedFunctorObjQIso, Functor.mapHomotopyCategoryFactors,
    Quotient.lift.isLift_inv]

private theorem chainDerivedUnit_shiftMap (F : C ⥤ D) [F.Additive]
    {S I : CochainComplex C ℤ} (φ : S ⟶ I⟦(2 : ℤ)⟧) :
    (DerivedCategory.homologyFunctor D 0).map ((chainDerivedUnit F).app S) ≫
        (DerivedCategory.homologyFunctor D 0).shiftMap
          ((ShiftedHom.map φ DerivedCategory.Q).map F.rightDerivedFunctor) 0 2 rfl =
      (DerivedCategory.homologyFunctor D 0).shiftMap
          ((ShiftedHom.map φ (F.mapHomologicalComplex (.up ℤ))).map DerivedCategory.Q)
          0 2 rfl ≫
        (DerivedCategory.homologyFunctor D 2).map ((chainDerivedUnit F).app I) := by
  have h := congrArg
    (fun f ↦ (DerivedCategory.homologyFunctor D 0).shiftMap
      (n := (2 : ℤ)) f 0 2 rfl)
    (ShiftedHom.map_naturality φ (chainDerivedUnit F))
  simp only [ShiftedHom.comp_map, ShiftedHom.comp_mk₀, ShiftedHom.mk₀_comp] at h
  simp only [Functor.shiftMap, Functor.map_comp, Category.assoc] at h
  rw [Functor.shiftIso_hom_naturality] at h
  simpa only [Functor.shiftMap, Category.assoc, DerivedCategory.shift_homologyFunctor,
    Functor.comp_obj] using h.symm

private theorem single_unit_normalization (F : C ⥤ D) [F.Additive]
    [EnoughInjectives C] [PreservesFiniteLimits F] (M : C) :
    F.toRightDerivedZero.app M ≫
        (F.homologyRightDerivedFunctorObjSingleFunctorIso M 0).inv =
      (DerivedCategory.singleFunctorCompHomologyFunctorIso D 0).inv.app (F.obj M) ≫
        (DerivedCategory.homologyFunctor D 0).map (F.rightDerivedSingleUnit M) := by
  apply (cancel_mono
    (F.homologyRightDerivedFunctorObjSingleFunctorIso M 0 ≪≫
      F.rightDerivedZeroIsoSelf.app M).hom).mp
  have h := F.rightDerivedSingleUnit_zero M
  dsimp only [Iso.trans_hom] at h ⊢
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [h, Iso.inv_hom_id_app]
  exact F.rightDerivedZeroIsoSelf_inv_hom_id_app M

private theorem single_shift_class {M : D} {L : CochainComplex D ℤ}
    (ψ : (CochainComplex.singleFunctor D 0).obj M ⟶ L⟦(2 : ℤ)⟧) :
    (DerivedCategory.singleFunctorCompHomologyFunctorIso D 0).inv.app M ≫
        (DerivedCategory.homologyFunctor D 0).shiftMap
          (ShiftedHom.map ψ DerivedCategory.Q) 0 2 rfl =
      (L⟦(2 : ℤ)⟧).liftCycles
          ((HomologicalComplex.singleObjXSelf (.up ℤ) 0 M).inv ≫ ψ.f 0)
          1 (by simp) (by
            erw [Category.assoc, ψ.comm, HomologicalComplex.single_obj_d,
              zero_comp, comp_zero]) ≫
        (L⟦(2 : ℤ)⟧).homologyπ 0 ≫
        ((HomologicalComplex.homologyFunctor D (.up ℤ) 0).shiftIso
          (2 : ℤ) 0 2 rfl).hom.app L ≫
        (DerivedCategory.homologyFunctorFactors D 2).inv.app L := by
  rw [DerivedCategory.shiftMap_homologyFunctor_map_Q ψ 0 2 rfl,
    DerivedCategory.singleFunctorCompHomologyFunctorIso_inv_app_zero]
  simp only [Functor.shiftMap, Category.assoc]
  erw [Iso.inv_hom_id_app_assoc]
  erw [← Category.assoc, DerivedCategory.singleObjHomologySelfIso_inv_homologyMap]
  simp only [Category.assoc]
  rfl

end DerivedUnit

private theorem evaluate_comp (P : PurityFiniteSetting.{u}) (T : Scheme.{u})
    {F G : ProSheaves P T} (f : P.constant T ⟶ F) (g : F ⟶ G) :
    P.gysinEvaluate T (f ≫ g) =
      (globalSectionsFunctor (Modules P) T).map g (P.gysinEvaluate T f) := by
  simp only [gysinEvaluate, Adjunction.homEquiv_naturality_right]
  rfl

private theorem chain_component (P : PurityFiniteSetting.{u}) (T : Scheme.{u})
    (I : CochainComplex (ProSheaves P T) ℤ)
    (φ : gysinSingleComplex P T ⟶ I⟦(2 : ℤ)⟧) :
    let E := globalSectionsFunctor (Modules P) T
    let ψ := (E.mapCochainComplexSingleFunctor 0).inv.app (P.constant T) ≫
      (ShiftedHom.map φ (E.mapHomologicalComplex (.up ℤ)))
    (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (E.obj (P.constant T))).inv ≫
        ψ.f 0 ≫
        (CochainComplex.shiftFunctorObjXIso
          ((E.mapHomologicalComplex (.up ℤ)).obj I) 2 0 2 rfl).hom =
      E.map (gysinChainComponent P T I φ) := by
  dsimp only
  simp only [HomologicalComplex.comp_f, Functor.mapCochainComplexSingleFunctor,
    HomologicalComplex.singleMapHomologicalComplex_inv_app_self, Category.assoc,
    Iso.inv_hom_id_assoc, ShiftedHom.map]
  simp only [Functor.mapHomologicalComplex_map_f]
  simp [gysinChainComponent, CochainComplex.HomComplex.Cocycle.equivHomShift_apply,
    CochainComplex.HomComplex.Cochain.rightUnshift_v]

private theorem chain_cycle_i (P : PurityFiniteSetting.{u}) (T : Scheme.{u})
    (I : CochainComplex (ProSheaves P T) ℤ)
    (φ : gysinSingleComplex P T ⟶ I⟦(2 : ℤ)⟧) :
    (((globalSectionsFunctor (Modules P) T).mapHomologicalComplex (.up ℤ)).obj I).iCycles 2
        (gysinChainCycle P T I φ) =
      P.gysinEvaluate T (gysinChainComponent P T I φ) := by
  dsimp only [gysinChainCycle]
  rw [← ConcreteCategory.comp_apply, gysinCycleSectionsIso_inv_i]
  erw [← evaluate_comp, HomologicalComplex.liftCycles_i]

/-- The global derived class of a chain map is the homology class of Γ(φ^0)(1).
This assertion contains no local-class edge or sheaf-homology evaluation.
Source: latest blueprint, `lem-pur-gysin-structure.proof.md`, second assertion,
and step 1 of `lem-pur-coordinate-gysin-edge-evaluation`.
(blueprint: lem-pur-coordinate-gysin-global-cycle).

Proof plan: apply `rightDerivedSingleUnit_zero` to the constant sheaf. Its inverse
single-object homology comparison sends `toRightDerivedZero` of the coefficient unit
to the unit augmentation class. Naturality of the right-derived unit for the chain map
φ transports this augmentation to its degree-zero component in I[2]. The Q-shift
comparison, the right-derived shift comparison and the homology shift isomorphism
identify this component with the closed map `gysinChainComponent` in I^2. The latter
has zero differential by `gysinChainComponent_closed`; left exactness of global
sections identifies its kernel lift with `gysinChainCycle`. The comparison
`rightDerivedFunctorObjQIso I` computes derived sections on the K-injective I,
so its H^2 inverse and `homologyFunctorFactors` take `homologyπ` of this explicit
cycle to the displayed global class. The shift is two, hence has positive sign.
A homotopy changes the component by a boundary, killed by `homologyπ`; the formula
therefore holds for every lift, including the zero map and the zero complex. -/
theorem coordinateGysin_global_cycle (P : PurityFiniteSetting.{u}) (T : Scheme.{u})
    (I : CochainComplex (ProSheaves P T) ℤ) [I.IsKInjective]
    (φ : gysinSingleComplex P T ⟶ I⟦(2 : ℤ)⟧) :
    P.gysinGlobalClass T 2 (gysinChainMorphism P T I φ) =
      ((((globalSectionsFunctor (Modules P) T).mapHomologicalComplex (.up ℤ)).obj I).homologyπ
          2 ≫
        (DerivedCategory.homologyFunctorFactors (Modules P) 2).inv.app _ ≫
        (DerivedCategory.homologyFunctor (Modules P) 2).map
          ((globalSectionsFunctor (Modules P) T).rightDerivedFunctorObjQIso I).inv)
        (gysinChainCycle P T I φ) := by
  let E := globalSectionsFunctor (Modules P) T
  let L : CochainComplex (Modules P) ℤ := (E.mapHomologicalComplex (.up ℤ)).obj I
  let H := DerivedCategory.homologyFunctor (Modules P) 0
  let t := (E.mapCochainComplexSingleFunctor 0).inv.app (P.constant T)
  let ψ := t ≫ ShiftedHom.map φ (E.mapHomologicalComplex (.up ℤ))
  let x := P.gysinEvaluate T (𝟙 (P.constant T))
  have ht : H.map (E.rightDerivedSingleUnit (P.constant T)) ≫
      H.shiftMap ((ShiftedHom.map φ DerivedCategory.Q).map E.rightDerivedFunctor)
        0 2 rfl =
      H.shiftMap (ShiftedHom.map ψ DerivedCategory.Q) 0 2 rfl ≫
        (DerivedCategory.homologyFunctor (Modules P) 2).map ((chainDerivedUnit E).app I) := by
    calc
      _ = H.map (DerivedCategory.Q.map t) ≫
          (H.map ((chainDerivedUnit E).app (gysinSingleComplex P T)) ≫
            H.shiftMap ((ShiftedHom.map φ DerivedCategory.Q).map E.rightDerivedFunctor)
              0 2 rfl) := by
        rw [← chainDerivedUnit_single E (P.constant T), Functor.map_comp, Category.assoc]
      _ = H.map (DerivedCategory.Q.map t) ≫
          (H.shiftMap
            ((ShiftedHom.map φ (E.mapHomologicalComplex (.up ℤ))).map DerivedCategory.Q)
            0 2 rfl ≫
            (DerivedCategory.homologyFunctor (Modules P) 2).map
              ((chainDerivedUnit E).app I)) := by
        rw [chainDerivedUnit_shiftMap]
      _ = _ := by
        simp only [ψ, ShiftedHom.map, Functor.map_comp, Functor.shiftMap, Category.assoc]
        rfl
  have hp :
      ((HomologicalComplex.singleObjXSelf (.up ℤ) 0 (E.obj (P.constant T))).inv ≫ ψ.f 0) ≫
        (L.shiftFunctorObjXIso 2 0 2 rfl).hom = E.map (gysinChainComponent P T I φ) := by
    simpa only [Category.assoc] using chain_component P T I φ
  let c' := L.liftCycles (E.map (gysinChainComponent P T I φ)) 3 (by simp) (by
    change E.map (gysinChainComponent P T I φ) ≫ E.map (I.d 2 3) = 0
    rw [← E.map_comp, gysinChainComponent_closed, E.map_zero])
  have hc := L.liftCycles_shift_homologyπ
    ((HomologicalComplex.singleObjXSelf (.up ℤ) 0 (E.obj (P.constant T))).inv ≫ ψ.f 0)
    1 (by simp) (by
      erw [Category.assoc, ψ.comm, HomologicalComplex.single_obj_d, zero_comp, comp_zero])
    2 rfl 3 (by simp)
  simp only [hp] at hc
  have hcycle : c' x = gysinChainCycle P T I φ := by
    apply (ModuleCat.mono_iff_injective (L.iCycles 2)).mp inferInstance
    calc
      L.iCycles 2 (c' x) = E.map (gysinChainComponent P T I φ) x := by
        rw [← ConcreteCategory.comp_apply, HomologicalComplex.liftCycles_i]
        rfl
      _ = P.gysinEvaluate T (gysinChainComponent P T I φ) := by
        simpa only [Category.id_comp] using
          (evaluate_comp P T (𝟙 (P.constant T)) (gysinChainComponent P T I φ)).symm
      _ = L.iCycles 2 (gysinChainCycle P T I φ) := (chain_cycle_i P T I φ).symm
  have hclass :
      E.toRightDerivedZero.app (P.constant T) ≫
          (E.homologyRightDerivedFunctorObjSingleFunctorIso (P.constant T) 0).inv ≫
          H.shiftMap ((ShiftedHom.map φ DerivedCategory.Q).map E.rightDerivedFunctor)
            0 2 rfl =
        c' ≫ L.homologyπ 2 ≫
          (DerivedCategory.homologyFunctorFactors (Modules P) 2).inv.app L ≫
          (DerivedCategory.homologyFunctor (Modules P) 2).map
            (E.rightDerivedFunctorObjQIso I).inv := by
    rw [← Category.assoc, single_unit_normalization, Category.assoc, ht,
      ← Category.assoc,
      single_shift_class ψ]
    simp only [Category.assoc]
    erw [reassoc_of% hc, Iso.inv_hom_id_app_assoc]
    rw [chainDerivedUnit_injective]
  have he := ConcreteCategory.congr_hom hclass x
  simp only [ConcreteCategory.comp_apply] at he
  rw [hcycle] at he
  simp only [ConcreteCategory.comp_apply, gysinGlobalClass, gysinChainMorphism,
    Functor.shiftMap, ShiftedHom.map, E, H, L, x,
    DerivedCategory.shift_homologyFunctor, hyper, global, Functor.comp_obj] at he ⊢
  convert he using 1
  rfl

end WeilConjectures.PurityFiniteSetting
