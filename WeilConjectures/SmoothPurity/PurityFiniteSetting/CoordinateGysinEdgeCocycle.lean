/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
/- copyright (c) 2026 The SHEAF contributors. -/
module
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.CoordinateGysinResolutionEvaluation
import WeilConjectures.SmoothPurity.PurityFiniteSetting.CoordinateGysinEdgeClassResolution
@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.RetractedSupport
namespace WeilConjectures.PurityFiniteSetting

/-- The normalized edge after choosing a K-injective representative and a lift.
(blueprint: lem-pur-coordinate-gysin-edge-cocycle).

Proof: the proved edge-class-resolution naturality formula transports the global
class. The resolution-evaluation theorem lifts f to an actual chain map, uses the
global homologyπ formula for its coefficient-unit cycle, applies edge_normalized
to that cycle, and uses the local homologyπ formula. Substitute that equality into
the transported class. -/
theorem coordinateGysin_edge_cocycle
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
        ((globalSectionsFunctor (Modules P) T).map
          (((DerivedCategory.homologyFunctor (ProSheaves P T) 0).shiftIso
            (2 : ℤ) 0 2 (add_zero 2)).hom.app (DerivedCategory.Q.obj I))
          (resolvedGysinEvaluation P T I f)) := by
  calc
    _ = (globalSectionsFunctor (Modules P) T).map
        ((DerivedCategory.homologyFunctor (ProSheaves P T) 2).map e.inv)
        ((D.comparison.edge 2).app (DerivedCategory.Q.obj I)
          (P.gysinGlobalClass T 2 f)) :=
      coordinateGysin_edge_class_resolution P h T D m I e f hf
    _ = _ := by
      rw [coordinateGysin_resolution_evaluation P h T D I f]

end WeilConjectures.PurityFiniteSetting
