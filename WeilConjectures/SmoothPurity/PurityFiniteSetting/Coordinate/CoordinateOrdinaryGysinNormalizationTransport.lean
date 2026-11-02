/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Coordinate.CoordinateOrdinaryGysinRealizationData
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.CoordinateGysinEdgeEvaluation
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.CoordinateGysinSupportCounit

/-! # Normalized supported-Hom transport for ordinary coordinate evaluation

This is the cocycle-normalization and site-transport calculation in the ordinary
evaluation argument. (blueprint: lem-pur-coordinate-ordinary-gysin-support-evaluation).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits AlgebraicGeometry

namespace WeilConjectures.PurityFiniteSetting

/-- Every normalized supported-Hom identification agrees on the chosen realization
chart with the realization's supported-Hom map.  The statement omits the orientation
chart and the exceptional transpose; those are handled by the companion realization
transport theorem.

Source: current blueprint, cor-pur-affine-space-zero-section-purity.proof.md, finite
etale-origin transport paragraph; Milne, Etale Cohomology, Theorem 9.4 and Example 9.5
(blueprint: lem-pur-coordinate-ordinary-gysin-support-evaluation-normalization).

Proof: put `m` for the coordinate morphism. (1) By `R.chart_eq` and `D.support_spec`,
`R.e.hom (gysinHomToSections m)` is the shift comparison, then `D.edge.inv`, then
`supportIso`; the normalized edge evaluation `coordinateGysin_edge_evaluation` and
`D.edge.hom_inv_id` identify it with `supportIso` of the global class of `m`.
(2) `R.evaluation` rewrites the right side as inverse single comparison, then `map m`,
then `R.epsilon`; the support-counit calculation `coordinateGysin_support_counit`,
applied with `R.eK`, `R.d` and their specifications, computes the left side as the same
composite with the transported counit `map R.eK.inv ≫ R.d.inv ≫ nu(counit) ≫ shift`
in place of `R.epsilon`. (3) `R.counit_eq` and cancellation of `R.d.inv` against
`R.d.hom` and of `map R.eK.inv` against `map R.eK.hom` identify that composite with
`R.epsilon`.
-/
theorem coordinateOrdinary_gysinSupportEvaluation_normalization
    (P : PurityFiniteSetting.{u}) (h : P.ramificationIndex ∣ P.level)
    (T : Scheme.{u}) (aT : T ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aT] [QuasiCompact aT] [IsSeparated aT]
    (D : OrientationSupportData P h T)
    (R : CoordinateOrdinaryGysinRealizationData P h T D)
    (chi : (proEtaleSupportHomPair P (zeroSection T)).Identification)
    (c : Ext ((Etale.lowerStar (ModuleCat.{u + 1} P.Coefficient)
      (zeroSection T)).obj (P.constantEtale T)) (P.twistEtale h (Line T)) 2) :
    (chi.chi (P.coordinateProInput h (Line T)) 2)
        (R.e.hom (P.gysinHomToSections h T
          (P.coordinateOrdinaryToGysin h T
            (Etale.supportedExactDerivedMap
              (Etale.lowerStar (ModuleCat.{u + 1} P.Coefficient) (zeroSection T))
              (P.constantEtale T) (P.twistEtale h (Line T)) c)))) =
      (R.chi.hom.app (P.gysinInput h T))
        (R.e.hom (P.gysinHomToSections h T
          (P.coordinateOrdinaryToGysin h T
            (Etale.supportedExactDerivedMap
              (Etale.lowerStar (ModuleCat.{u + 1} P.Coefficient) (zeroSection T))
              (P.constantEtale T) (P.twistEtale h (Line T)) c)))) := by
  let m := P.coordinateOrdinaryToGysin h T
    (Etale.supportedExactDerivedMap
      (Etale.lowerStar (ModuleCat.{u + 1} P.Coefficient) (zeroSection T))
      (P.constantEtale T) (P.twistEtale h (Line T)) c)
  have hchart : R.e.hom (P.gysinHomToSections h T m) =
      ((D.comparison.supportIso 2).hom.app (P.gysinEtaleInput h T))
        (P.gysinGlobalClass T 2 m) := by
    rw [R.chart_eq, D.support_spec]
    have he := coordinateGysin_edge_evaluation P h T D m
    have he' := (congrArg (fun x ↦ D.edge.inv x) he).symm.trans
      (ConcreteCategory.congr_hom D.edge.hom_inv_id (P.gysinGlobalClass T 2 m))
    exact congrArg (fun x ↦
      ((D.comparison.supportIso 2).hom.app (P.gysinEtaleInput h T)) x) he'
  change (chi.chi (P.gysinInput h T) 2) (R.e.hom (P.gysinHomToSections h T m)) =
    (R.chi.hom.app (P.gysinInput h T)) (R.e.hom (P.gysinHomToSections h T m))
  rw [R.evaluation, hchart]
  rw [coordinateGysin_support_counit P h T aT D R.hb R.eK R.d
    R.eK_spec R.d_spec chi m]
  have hepsilon :
      (lowerStar (Modules P) (zeroSection T)).mapDerivedCategory.map R.eK.inv ≫
        R.d.inv ≫ (nu P (Line T)).map (P.boundaryEtaleCounit h T) ≫
        ((nu P (Line T)).commShiftIso (2 : ℤ)).hom.app (P.gysinEtaleInput h T).obj =
      R.epsilon := by
    rw [← R.counit_eq]
    simp only [Iso.inv_hom_id_assoc, ← Functor.map_comp_assoc,
      R.eK.inv_hom_id]
    exact (congrArg (fun f ↦ f ≫ R.epsilon)
      ((lowerStar (Modules P) (zeroSection T)).mapDerivedCategory.map_id
        (P.gysinValue h T))).trans (Category.id_comp R.epsilon)
  rw [hepsilon]

end WeilConjectures.PurityFiniteSetting
