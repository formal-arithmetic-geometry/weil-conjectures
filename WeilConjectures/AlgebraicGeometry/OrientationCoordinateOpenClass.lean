/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PurityAffineLineOrientationData
import WeilConjectures.AlgebraicGeometry.OrientationGlobalClassComparison
import WeilConjectures.AlgebraicGeometry.OrientationOpenLocalizationComparison

/-! # Comparison of the two affine-line open coordinate classes

The ordinary Gysin and finite pro-etale presentations evaluate the same Kummer
class after the canonical coefficient and localization comparisons.
(blueprint: lem-pur-orientation-coordinate-open-class).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.RetractedSupport

namespace WeilConjectures.PurityFiniteSetting

/-- Evaluating the constant unit after the comparison adjunction gives the
section-comparison image of the etale unit. Source: the comparison unit in the
coordinate-class construction (blueprint: lem-pur-orientation-coordinate-open-class). -/
private theorem comparison_unit_one (P : PurityFiniteSetting.{u}) (T : Scheme.{u}) :
    P.gysinEvaluate T (𝟙 (P.constant T)) =
      ((finiteComparisonSectionUnit T P.Coefficient (Scheme.Etale.mk (𝟙 T))).app
        (P.constantEtale T))
        ((((constantSheafAdj T.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)
          (Scheme.Etale.isTerminalMkId T)).homEquiv _ _
            (𝟙 (P.constantEtale T)))) 1) := by
  simp [gysinEvaluate, constant, constantEtale, finiteComparisonSectionUnit,
    Adjunction.homEquiv]
  rfl

/-- The global evaluation formula follows by evaluating the comparison square at
one and cancelling the bounded-below/unbounded section isomorphism.
Source: coordinate evaluation and site comparison
(blueprint: lem-pur-orientation-coordinate-open-class). -/
private theorem global_class_of_comparison (P : PurityFiniteSetting.{u})
    (T : Scheme.{u}) (F : Sheaf T.smallEtaleTopology (Modules P))
    (c : Abelian.Ext (P.constantEtale T) F 1) :
    P.gysinGlobalClass T 1
        (c.mapExactFunctor (comparisonUpperStar (Modules P) T)).hom =
      ((finiteComparisonSectionHypercohomology T P.Coefficient
          (Scheme.Etale.mk (𝟙 T)) 1).app
            ((DerivedCategory.Plus.singleFunctor _ 0).obj F) ≫
        (Sheaf.sectionHypercohomologyFunctor (Scheme.ProEt.topology T) (Modules P)
          (Scheme.ProEt.mk (𝟙 T)) 1).map
            (((comparisonUpperStar (Modules P) T).mapDerivedCategoryPlusSingleFunctor
              0).hom.app F) ≫
        (sectionPlusIso P T (Scheme.ProEt.mk (𝟙 T)) 1).inv.app
          ((DerivedCategory.Plus.singleFunctor _ 0).obj
            ((comparisonUpperStar (Modules P) T).obj F)))
        (P.coordinateClassSection T F c) := by
  let one := (((constantSheafAdj T.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)
    (Scheme.Etale.isTerminalMkId T)).homEquiv _ _ (𝟙 (P.constantEtale T)))) 1
  have he := congrArg (fun f ↦ f one) (P.orientation_global_class_comparison T F c)
  change (Abelian.Ext.coordinateSectionMap (globalSectionsFunctor (Modules P) T)
      (c.mapExactFunctor (comparisonUpperStar (Modules P) T)))
      (((finiteComparisonSectionUnit T P.Coefficient (Scheme.Etale.mk (𝟙 T))).app
        (P.constantEtale T)) one) = _ at he
  rw [← comparison_unit_one P T] at he
  let K := (DerivedCategory.Plus.singleFunctor _ 0).obj
    ((comparisonUpperStar (Modules P) T).obj F)
  let e := (sectionPlusIso P T (Scheme.ProEt.mk (𝟙 T)) 1).app K
  change e.hom (P.gysinGlobalClass T 1
    (c.mapExactFunctor (comparisonUpperStar (Modules P) T)).hom) = _ at he
  have hi := congrArg (fun x ↦ e.inv x) he
  have hc : e.inv (e.hom (P.gysinGlobalClass T 1
      (c.mapExactFunctor (comparisonUpperStar (Modules P) T)).hom)) =
      P.gysinGlobalClass T 1
        (c.mapExactFunctor (comparisonUpperStar (Modules P) T)).hom := by
    exact ConcreteCategory.congr_hom e.hom_inv_id _
  rw [hc] at hi
  dsimp only [e, K, one, hyper, global, globalSectionsFunctor, Scheme.ProEt.mk,
    DerivedCategory.Plus.singleFunctor, DerivedCategory.Plus.singleFunctors,
    SingleFunctors.lift, Functor.comp_obj, ObjectProperty.ι_obj,
    ObjectProperty.lift_obj_obj] at hi ⊢
  simp only [Iso.app_inv, coordinateClassSection, ConcreteCategory.comp_apply] at hi ⊢
  convert hi using 1; rfl

/-- The ordinary and pro-etale affine-line coordinate open classes agree after their canonical
coefficient identifications.

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-lem-sp-reduction/
thm-pur-affine-line-orientation.proof.md, rank-one coordinate localization.
Proof: unfold both evaluations, identify `gysinInput` with `coordinateProInput`, and
cancel the comparison unit, root-line pullback, and open-localization comparison.
The remaining maps are the same evaluation of the ordinary Kummer Ext class on one.
(blueprint: lem-pur-orientation-coordinate-open-class). -/
theorem orientation_coordinate_open_class (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) (Y : Scheme.{u})
    (a : Y ⟶ Spec (CommRingCat.of P.field.k))
    (D : OrientationSupportData P h Y) (M : CoordinateBoundaryModel P Y) :
    P.gysinKummerSection h Y a D.comparison D.openCoefficient =
      M.openProClass P h a := by
  let c := P.kummerEtale h (Punctured Y)
    (P.exponent_isUnit (Punctured Y) (puncturedProjection Y ≫ a)) (coordinateUnit Y)
  change P.orientationOpenClassTransport h Y D
      (P.gysinGlobalClass (Punctured Y) 1
        (c.mapExactFunctor (comparisonUpperStar (Modules P) (Punctured Y))).hom) =
    (finiteComparisonSectionHypercohomology (Line Y) P.Coefficient
      (Scheme.Etale.mk (zeroSection Y).openComplement.ι) 1).app
        (P.coordinateEtaleInput h (Line Y))
      (P.coordinateEtaleOpenClassTransport h Y a M.complementIso
        (P.coordinateClassSection (Punctured Y) (P.twistEtale h (Punctured Y)) c))
  rw [global_class_of_comparison P (Punctured Y) (P.twistEtale h (Punctured Y)) c]
  exact congrArg (fun f ↦ f
    (P.coordinateClassSection (Punctured Y) (P.twistEtale h (Punctured Y)) c))
      (P.orientation_open_localization_comparison h Y a D M)

end WeilConjectures.PurityFiniteSetting
