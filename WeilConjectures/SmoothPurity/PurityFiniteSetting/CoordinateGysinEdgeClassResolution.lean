/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
/- copyright (c) 2026 The SHEAF contributors. -/
module
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Affine.PurityAffineLineOrientationData
@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.RetractedSupport
namespace WeilConjectures.PurityFiniteSetting

private theorem gysinGlobalClass_naturality (P : PurityFiniteSetting.{u}) (T : Scheme.{u})
    {K L : DerivedCategory (ProSheaves P T)} (q : ℤ)
    (m : (DerivedCategory.singleFunctor (ProSheaves P T) 0).obj
      (P.constant T) ⟶ K⟦q⟧) (f : K ⟶ L) :
    (hyper P T q).map f (P.gysinGlobalClass T q m) =
      P.gysinGlobalClass T q (m ≫ f⟦q⟧') := by
  let E := (globalSectionsFunctor (Modules P) T).rightDerivedFunctor
  let H := DerivedCategory.homologyFunctor (Modules P) 0
  have hshift := (E.commShiftIso q).hom.naturality f
  have hhom := (H.shiftIso q 0 q (add_zero q)).hom.naturality (E.map f)
  dsimp only [Functor.comp_map] at hshift hhom
  change H.map ((E.map f)⟦q⟧') ≫
      (H.shiftIso q 0 q (add_zero q)).hom.app (E.obj L) =
    (H.shiftIso q 0 q (add_zero q)).hom.app (E.obj K) ≫
      (DerivedCategory.homologyFunctor (Modules P) q).map (E.map f) at hhom
  have heq :
      H.map (E.map m ≫ (E.commShiftIso q).hom.app K) ≫
          (H.shiftIso q 0 q (add_zero q)).hom.app (E.obj K) ≫
          (DerivedCategory.homologyFunctor (Modules P) q).map (E.map f) =
        H.map (E.map (m ≫ f⟦q⟧') ≫ (E.commShiftIso q).hom.app L) ≫
          (H.shiftIso q 0 q (add_zero q)).hom.app (E.obj L) := by
    have hshiftH := congrArg H.map hshift
    simp only [Functor.map_comp] at hshiftH
    simp only [Functor.map_comp, Category.assoc]
    rw [← hhom, ← reassoc_of% hshiftH]
  dsimp only [gysinGlobalClass]
  exact ConcreteCategory.congr_hom heq
      (((globalSectionsFunctor (Modules P) T).homologyRightDerivedFunctorObjSingleFunctorIso
        (P.constant T) 0).inv
        (((globalSectionsFunctor (Modules P) T).toRightDerivedZero.app (P.constant T))
          (P.gysinEvaluate T (𝟙 (P.constant T)))))

/-- Resolve the global Gysin class before evaluating its normalized edge.
Source: latest blueprint, `lem-pur-gysin-structure.proof.md`, second assertion.
(blueprint: lem-pur-coordinate-gysin-edge-class-resolution).

Proof: evaluation of a derived class on the fixed coefficient unit commutes with
postcomposition, by the shift comparisons' naturality. Apply naturality of the
comparison edge to e.inv and evaluate on the class represented by f. Substitute hf
and cancel the shifted e.hom followed by e.inv. This is class transport only;
it requires no chain lift, no edge normalization and no homotopy argument. -/
theorem coordinateGysin_edge_class_resolution
    (P : PurityFiniteSetting.{u}) (h : P.ramificationIndex ∣ P.level)
    (T : Scheme.{u}) (D : OrientationSupportData P h T)
    (m : P.derivedSheaf h T false ⟶ P.gysinValue h T)
    (I : CochainComplex (ProSheaves P T) ℤ) [I.IsKInjective]
    (e : P.gysinClosed h T ≅ DerivedCategory.Q.obj I)
    (f : (DerivedCategory.singleFunctor (ProSheaves P T) 0).obj (P.constant T) ⟶
      (DerivedCategory.Q.obj I)⟦(2 : ℤ)⟧)
    (hf : f = m ≫ (e.hom⟦(2 : ℤ)⟧')) :
    D.edge.hom (P.gysinGlobalClass T 2 m) =
      (globalSectionsFunctor (Modules P) T).map
        ((DerivedCategory.homologyFunctor (ProSheaves P T) 2).map e.inv)
        ((D.comparison.edge 2).app (DerivedCategory.Q.obj I)
          (P.gysinGlobalClass T 2 f)) := by
  rw [D.edge_spec, hf]
  have hn := ConcreteCategory.congr_hom ((D.comparison.edge 2).naturality e.inv)
    (P.gysinGlobalClass T 2 (m ≫ e.hom⟦(2 : ℤ)⟧'))
  change (D.comparison.edge 2).app (P.gysinClosed h T)
      ((hyper P T 2).map e.inv (P.gysinGlobalClass T 2 (m ≫ e.hom⟦(2 : ℤ)⟧'))) =
    (globalSectionsFunctor (Modules P) T).map
      ((DerivedCategory.homologyFunctor (ProSheaves P T) 2).map e.inv)
      ((D.comparison.edge 2).app (DerivedCategory.Q.obj I)
        (P.gysinGlobalClass T 2 (m ≫ e.hom⟦(2 : ℤ)⟧'))) at hn
  rw [gysinGlobalClass_naturality] at hn
  have hc : (m ≫ e.hom⟦(2 : ℤ)⟧') ≫ e.inv⟦(2 : ℤ)⟧' = m := by
    let E := (shiftFunctor (DerivedCategory (ProSheaves P T)) (2 : ℤ)).mapIso e
    change (m ≫ E.hom) ≫ E.inv = m
    rw [Category.assoc, E.hom_inv_id]
    exact Category.comp_id m
  rw [hc] at hn
  exact hn

end WeilConjectures.PurityFiniteSetting
