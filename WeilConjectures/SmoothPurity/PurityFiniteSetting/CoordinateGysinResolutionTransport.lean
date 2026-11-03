/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
/- copyright (c) 2026 The SHEAF contributors. -/
module
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.CoordinateGysinEdgeCocycle
@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.RetractedSupport
namespace WeilConjectures.PurityFiniteSetting

/-- Transport the chosen resolution evaluation back to `gysinClosed`.
(blueprint: lem-pur-coordinate-gysin-resolution-transport).

Proof: expand `resolvedGysinEvaluation`, use naturality of evaluation on the constant
unit, the inverse comparison `e`, the degree-zero single-object comparison and the
canonical homology shift comparison. The equation `hf` identifies the lifted morphism
with `m`; cancellation of the comparison isomorphisms gives the displayed equality. -/
theorem coordinateGysin_resolution_transport
    (P : PurityFiniteSetting.{u}) (h : P.ramificationIndex ∣ P.level)
    (T : Scheme.{u})
    (m : P.derivedSheaf h T false ⟶ P.gysinValue h T)
    (I : CochainComplex (ProSheaves P T) ℤ) [I.IsKInjective]
    (e : P.gysinClosed h T ≅ DerivedCategory.Q.obj I)
    (f : (DerivedCategory.singleFunctor (ProSheaves P T) 0).obj (P.constant T) ⟶
      (DerivedCategory.Q.obj I)⟦(2 : ℤ)⟧)
    (hf : f = m ≫ (e.hom⟦(2 : ℤ)⟧')) :
    (globalSectionsFunctor (Modules P) T).map
        ((DerivedCategory.homologyFunctor (ProSheaves P T) 2).map e.inv)
        ((globalSectionsFunctor (Modules P) T).map
          (((DerivedCategory.homologyFunctor (ProSheaves P T) 0).shiftIso
            (2 : ℤ) 0 2 (add_zero 2)).hom.app (DerivedCategory.Q.obj I))
          (resolvedGysinEvaluation P T I f)) =
      (globalSectionsFunctor (Modules P) T).map
        (((DerivedCategory.homologyFunctor (ProSheaves P T) 0).shiftIso
          (2 : ℤ) 0 2 (add_zero 2)).hom.app (P.gysinClosed h T))
        (P.gysinHomToSections h T m) := by
  rw [hf]
  dsimp [resolvedGysinEvaluation, gysinHomToSections]
  simp only [Functor.map_comp]
  have hs := (DerivedCategory.homologyFunctor (ProSheaves P T) 0).shiftIso_hom_naturality
    (2 : ℤ) 0 2 (add_zero 2) e.inv
  simp only [DerivedCategory.shift_homologyFunctor] at hs
  have hsE := congrArg (fun k ↦ (globalSectionsFunctor (Modules P) T).map k) hs
  have hsEval := ConcreteCategory.congr_hom hsE
    (P.gysinEvaluate T
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso (ProSheaves P T) 0).inv.app
        (P.constant T) ≫
        (DerivedCategory.homologyFunctor (ProSheaves P T) 0).map m ≫
        (DerivedCategory.homologyFunctor (ProSheaves P T) 0).map
          (e.hom⟦(2 : ℤ)⟧')))
  have hsEval' := hsEval.symm
  simp only [Functor.map_comp] at hsEval'
  have gysinEvaluate_naturality {F G : ProSheaves P T} (a : F ⟶ G)
      (q : P.constant T ⟶ F) :
      (globalSectionsFunctor (Modules P) T).map a (P.gysinEvaluate T q) =
        P.gysinEvaluate T (q ≫ a) := by
    dsimp [gysinEvaluate]
    have h2 := (comparisonAdjunction (Modules P) T).homEquiv_naturality_right q a
    have h1 := Adjunction.homEquiv_naturality_right
      (constantSheafAdj T.smallEtaleTopology (Modules P)
        (Scheme.Etale.isTerminalMkId T))
      ((comparisonAdjunction (Modules P) T).homEquiv _ _ q)
      ((comparisonLowerStar (Modules P) T).map a)
    have h2c := congrArg (fun z ↦
      (constantSheafAdj T.smallEtaleTopology (Modules P)
        (Scheme.Etale.isTerminalMkId T)).homEquiv _ _ z) h2
    have h2d := by simpa only [constantEtale] using h2c
    rw [← h2d] at h1
    have h1' := congrArg (fun k ↦ k 1) h1.symm
    change _ = _
    convert h1' using 1 <;> rfl
  convert hsEval' using 1
  · rfl
  · rfl
  · simp only [ConcreteCategory.comp_apply]
    change (globalSectionsFunctor (Modules P) T).map
        (((DerivedCategory.homologyFunctor (ProSheaves P T) 0).shiftIso
          (2 : ℤ) 0 2 (add_zero 2)).hom.app (P.gysinClosed h T))
        (P.gysinEvaluate T
          ((DerivedCategory.singleFunctorCompHomologyFunctorIso (ProSheaves P T) 0).inv.app
            (P.constant T) ≫ (DerivedCategory.homologyFunctor (ProSheaves P T) 0).map m)) = _
    rw [gysinEvaluate_naturality]
    rw [gysinEvaluate_naturality, gysinEvaluate_naturality]
    congr 1
    simp only [Category.assoc]
    rw [← Category.assoc
      ((DerivedCategory.homologyFunctor (ProSheaves P T) 0).map
        ((shiftFunctor (DerivedCategory (ProSheaves P T)) 2).map e.hom))
      ((DerivedCategory.homologyFunctor (ProSheaves P T) 0).map
        ((shiftFunctor (DerivedCategory (ProSheaves P T)) 2).map e.inv))
      (((DerivedCategory.homologyFunctor (ProSheaves P T) 0).shiftIso
        (2 : ℤ) 0 2 (add_zero 2)).hom.app (P.gysinClosed h T))]
    rw [← (DerivedCategory.homologyFunctor (ProSheaves P T) 0).map_comp]
    rw [← (shiftFunctor (DerivedCategory (ProSheaves P T)) (2 : ℤ)).map_comp,
      e.hom_inv_id, (shiftFunctor (DerivedCategory (ProSheaves P T)) (2 : ℤ)).map_id,
      (DerivedCategory.homologyFunctor (ProSheaves P T) 0).map_id,
      Category.id_comp]

end WeilConjectures.PurityFiniteSetting
