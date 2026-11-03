/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
/- copyright (c) 2026 The SHEAF contributors. -/
module
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Affine.PurityAffineLineOrientationData
import WeilConjectures.SmoothPurity.PurityFiniteSetting.CoordinateGysinGlobalCycle
import WeilConjectures.SmoothPurity.PurityFiniteSetting.CoordinateGysinLocalCycle
@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.RetractedSupport
namespace WeilConjectures.PurityFiniteSetting

/-- The degree-two evaluation obtained from a chosen K-injective resolution.
(blueprint: lem-pur-coordinate-gysin-resolution-evaluation).

This is derived H^0 evaluation, before comparison with degree two. The actual chain
cycle is constructed separately by `gysinChainCycle`. -/
def resolvedGysinEvaluation
    (P : PurityFiniteSetting.{u}) (T : Scheme.{u})
    (I : CochainComplex (ProSheaves P T) ℤ)
    (f : (DerivedCategory.singleFunctor (ProSheaves P T) 0).obj (P.constant T) ⟶
      (DerivedCategory.Q.obj I)⟦(2 : ℤ)⟧) :
    (globalSectionsFunctor (Modules P) T).obj
      ((DerivedCategory.homologyFunctor (ProSheaves P T) 0).obj
        ((DerivedCategory.Q.obj I)⟦(2 : ℤ)⟧)) :=
  P.gysinEvaluate T
    ((DerivedCategory.singleFunctorCompHomologyFunctorIso (ProSheaves P T) 0).inv.app
      (P.constant T) ≫
      (DerivedCategory.homologyFunctor (ProSheaves P T) 0).map f)

/-- The edge of the chosen resolution is evaluation on its degree-two cycle.
(blueprint: lem-pur-coordinate-gysin-resolution-evaluation).

Proof: lift f to an actual chain map φ using the proved K-injective lifting theorem.
The global-cycle lemma expresses the left input as homologyπ of Γ(φ^0)(1).
Apply the specified `comparison.edge_normalized` morphism equality to that cycle.
The local-cycle lemma identifies its output with H^0(f) evaluated on one.
Both cycle lemmas quantify over every chain lift, so this argument is independent
of which lift was obtained. -/
theorem coordinateGysin_resolution_evaluation
    (P : PurityFiniteSetting.{u}) (h : P.ramificationIndex ∣ P.level)
    (T : Scheme.{u}) (D : OrientationSupportData P h T)
    (I : CochainComplex (ProSheaves P T) ℤ) [I.IsKInjective]
    (f : (DerivedCategory.singleFunctor (ProSheaves P T) 0).obj (P.constant T) ⟶
      (DerivedCategory.Q.obj I)⟦(2 : ℤ)⟧) :
    (D.comparison.edge 2).app (DerivedCategory.Q.obj I)
        (P.gysinGlobalClass T 2 f) =
      (globalSectionsFunctor (Modules P) T).map
        (((DerivedCategory.homologyFunctor (ProSheaves P T) 0).shiftIso
          (2 : ℤ) 0 2 (add_zero 2)).hom.app (DerivedCategory.Q.obj I))
        (resolvedGysinEvaluation P T I f) := by
  obtain ⟨φ, rfl⟩ := exists_gysinChainMorphism P T I f
  rw [coordinateGysin_global_cycle P T I φ]
  have hn := ConcreteCategory.congr_hom (D.comparison.edge_normalized 2 I)
    (gysinChainCycle P T I φ)
  calc
    _ = ((gysinCycleSectionsIso P T I).hom ≫
        (globalSectionsFunctor (Modules P) T).map (I.homologyπ 2) ≫
        (globalSectionsFunctor (Modules P) T).map
          ((DerivedCategory.homologyFunctorFactors (ProSheaves P T) 2).inv.app I))
        (gysinChainCycle P T I φ) := by
      convert hn using 1 <;> rfl
    _ = _ := (coordinateGysin_local_cycle P T I φ).symm

end WeilConjectures.PurityFiniteSetting
