/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.CoordinateGlobalSectionsUnit
public import WeilConjectures.CategoryTheory.CoordinateDerivedTransportNormalization
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.Ext.CoordinateExtPullbackEvaluation
import all Mathlib.CategoryTheory.Iso
import all Mathlib.CategoryTheory.Equivalence
import all Mathlib.CategoryTheory.Limits.HasLimits
import all Mathlib.Logic.Small.Defs

/-! # Transport of the punctured coordinate class
Source: Milne Theorem 9.4, evaluation on the constant unit.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures.PurityFiniteSetting

attribute [local implicit_reducible] Scheme.Etale Scheme.instCategoryEtale
  MorphismProperty MorphismProperty.Comma.instCategory constantEtale twistEtale
  Functor.mapDerivedCategoryPlus DerivedCategory.Plus.homologyFunctor

/-- The degree-one pullback on punctured global sections, with the actual twist
coefficient map. Source: Milne Section 9
(blueprint: aux-lem-pur-coordinate-punctured-class-transport). -/
def coordinatePuncturedPullback (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) {T Y : Scheme.{u}} (g : T ⟶ Y) :
    (Sheaf.sectionHypercohomologyFunctor (Punctured Y).smallEtaleTopology
      (ModuleCat.{u + 1} P.Coefficient) (Scheme.Etale.mk (𝟙 (Punctured Y))) 1).obj
        (P.coordinateEtaleInput h (Punctured Y)) ⟶
    (Sheaf.sectionHypercohomologyFunctor (Punctured T).smallEtaleTopology
      (ModuleCat.{u + 1} P.Coefficient) (Scheme.Etale.mk (𝟙 (Punctured T))) 1).obj
        (P.coordinateEtaleInput h (Punctured T)) :=
  (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} P.Coefficient) 1).map
    ((Functor.coordinateSectionTransport
      (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) (puncturedMap g))
      (Etale.sectionsFunctor (ModuleCat.{u + 1} P.Coefficient) (Punctured Y))
      (Etale.sectionsFunctor (ModuleCat.{u + 1} P.Coefficient) (Punctured T))
      (P.coordinateGlobalSectionsUnit (puncturedMap g))).app
        (P.coordinateEtaleInput h (Punctured Y)) ≫
      (Etale.sectionsFunctor (ModuleCat.{u + 1} P.Coefficient)
        (Punctured T)).rightDerivedFunctorPlus.map
          (P.coordinateEtaleCoefficientPullback h (puncturedMap g)))

/-- The exact Ext pullback square carries the punctured coordinate evaluation to
its target evaluation.
Source: Milne Theorem 9.4; the relative Kummer coefficient normalization.
Proof: apply exact-functor naturality of derived evaluation to the two Kummer Ext
classes. Their source map is the canonical constant comparison, whose adjoint mate
sends the constant unit to the constant unit. Evaluate the resulting morphism
square on that unit.
(blueprint: aux-lem-pur-coordinate-punctured-class-transport). -/
theorem coordinate_punctured_class_transport (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) {T Y : Scheme.{u}} (g : T ⟶ Y)
    (a : Y ⟶ Spec (CommRingCat.of P.field.k))
    (hk : P.CoordinateKummerPullback h g a) :
    P.coordinatePuncturedPullback h g
        (P.coordinateClassSection (Punctured Y) (P.twistEtale h (Punctured Y))
          (P.coordinateEtaleKummer h Y a)) =
      P.coordinateClassSection (Punctured T) (P.twistEtale h (Punctured T))
        (P.coordinateEtaleKummer h T (g ≫ a)) := by
  have hh := Abelian.Ext.coordinateSectionMap_exact_naturality
    (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) (puncturedMap g))
    (Etale.sectionsFunctor (ModuleCat.{u + 1} P.Coefficient) (Punctured Y))
    (Etale.sectionsFunctor (ModuleCat.{u + 1} P.Coefficient) (Punctured T))
    (P.coordinateGlobalSectionsUnit (puncturedMap g))
    ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} P.Coefficient)
      (puncturedMap g)).hom.app (ModuleCat.of P.Coefficient P.Coefficient))
    (P.twistEtalePullback h (puncturedMap g))
    (P.coordinateEtaleKummer h Y a) (P.coordinateEtaleKummer h T (g ≫ a)) hk.1
  have hu := P.coordinateGlobalSectionsUnit_one (puncturedMap g)
  have he := ConcreteCategory.congr_hom (congrArg (fun z ↦
    (constantSheafAdj (Punctured Y).smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)
      (Scheme.Etale.isTerminalMkId (Punctured Y))).unit.app
        (ModuleCat.of P.Coefficient P.Coefficient) ≫ z) hh) (1 : P.Coefficient)
  have hue := ConcreteCategory.congr_hom hu (1 : P.Coefficient)
  simp only [ConcreteCategory.comp_apply] at he hue
  erw [hue] at he
  change _ = _
  exact he

end WeilConjectures.PurityFiniteSetting
