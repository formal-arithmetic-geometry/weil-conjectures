/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Coordinate.CoordinateOrdinaryGysinRealizationData
public import Mathlib.Logic.Small.Defs
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.CoordinateBoundaryImageHomComparison
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.CoordinateOrdinaryBoundaryAntecedent

/-! # Counit transport for ordinary coordinate Gysin evaluation

This is the realization-side calculation in the ordinary evaluation argument.
(blueprint: lem-pur-coordinate-ordinary-gysin-support-evaluation).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits AlgebraicGeometry

namespace WeilConjectures.PurityFiniteSetting

/-- The chosen affine-line realization evaluates the coordinate ordinary transpose as
its site-supported Hom class.  This is the counit, comparison and bounded-transpose
calculation; the normalization of an arbitrary supported-Hom identification is
handled separately.

Source: current blueprint, cor-pur-affine-space-zero-section-purity.proof.md, finite
etale-origin transport paragraph; Milne, Etale Cohomology, Section 9, Example 9.5
(blueprint: lem-pur-coordinate-ordinary-gysin-support-evaluation-realization).

Proof: `coordinateOrdinary_boundaryAntecedent` supplies b whose exceptional
comparison is the coordinate transpose and whose ordinary counit evaluation is
c.hom. Substitute the first equality into `R.evaluation`, using `R.eK_spec`.
Apply `coordinateBoundaryImageHomComparison` to b and postcompose its equation
with the closed image of `R.eK.hom` and `R.epsilon`. By `R.d_spec` and
`R.counit_eq`, the last three factors become the comparison image of the ordinary
counit followed by the site shift comparison. Functoriality combines the two
ordinary images; substitute the second equation for b. Expanding `v.homMap`
gives exactly the remaining composite.
-/
theorem coordinateOrdinary_gysinSupportEvaluation_realization
    (P : PurityFiniteSetting.{u}) (h : P.ramificationIndex ∣ P.level)
    (T : Scheme.{u}) (aT : T ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aT] [QuasiCompact aT] [IsSeparated aT]
    (D : OrientationSupportData P h T)
    (R : CoordinateOrdinaryGysinRealizationData P h T D)
    (v : siteSupportHomTransport P (zeroSection T))
    (c : Ext ((Etale.lowerStar (ModuleCat.{u + 1} P.Coefficient)
      (zeroSection T)).obj (P.constantEtale T)) (P.twistEtale h (Line T)) 2) :
    (R.chi.hom.app (P.gysinInput h T))
        (R.e.hom (P.gysinHomToSections h T
          (P.coordinateOrdinaryToGysin h T
            (Etale.supportedExactDerivedMap
              (Etale.lowerStar (ModuleCat.{u + 1} P.Coefficient) (zeroSection T))
              (P.constantEtale T) (P.twistEtale h (Line T)) c)))) =
      v.homMap (hB := Scheme.isContinuous_toProEt (Line T))
        (P.coordinateEtaleInput h (Line T)) 2 c.hom := by
  obtain ⟨b, hm, hb⟩ := coordinateOrdinary_boundaryAntecedent P h T aT c
  rw [← R.eK_spec] at hm
  erw [R.evaluation, hm]
  have hB := coordinateBoundaryImageHomComparison P T v
    ⟨P.boundaryEtaleValue h T, R.hb⟩ b
  have hB' := congrArg (fun q ↦ q ≫
    (lowerStar (Modules P) (zeroSection T)).mapDerivedCategory.map R.eK.hom ≫
      R.epsilon) hB
  simp only [Category.assoc] at hB'
  rw [← R.d_spec, R.counit_eq] at hB'
  erw [← (nu P (Line T)).map_comp_assoc] at hB'
  have hb' := (Category.assoc
    (((Etale.lowerStar (Modules P) (zeroSection T)).mapDerivedCategorySingleFunctor
      0).inv.app (P.constantEtale T))
    ((Etale.lowerStar (Modules P) (zeroSection T)).mapDerivedCategory.map b)
    (P.boundaryEtaleCounit h T)).trans hb
  erw [hb'] at hB'
  let F := (lowerStar (Modules P) (zeroSection T)).mapDerivedCategory
  let a := ((comparisonUpperStar (Modules P) T).mapDerivedCategorySingleFunctor
    0).inv.app (P.constantEtale T)
  let t := (nu P T).map b
  erw [← Category.assoc a t R.eK.hom, F.map_comp (a ≫ t) R.eK.hom,
    Category.assoc (F.map (a ≫ t)) (F.map R.eK.hom) R.epsilon]
  erw [hB']
  rfl

end WeilConjectures.PurityFiniteSetting
