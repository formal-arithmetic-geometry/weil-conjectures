/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Coordinate.CoordinateOrdinaryGysinRealizationData

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

Proof: by `R.evaluation` the left side is the inverse single comparison, followed by
closed direct image of `coordinateOrdinaryToGysin` of the ordinary derived
realization of `c`, followed by `R.epsilon`.  By the adjunct-counit identity the
inverse closed adjunct of that realization is closed direct image of its transpose
followed by the ordinary exceptional counit.  Transport this through the canonical
closed image mate `R.d` (`R.d_spec`) and the exceptional comparison `R.eK`
(`R.eK_spec`); `R.counit_eq` replaces `R.d.hom ≫ map R.eK.hom ≫ R.epsilon` by the
comparison image of the ordinary counit followed by the shift map.  The
single-functor, exceptional-shift and site-shift comparisons and the shifted
`boundedSiteRho` that make up `coordinateOrdinaryToGysin` cancel against these by
naturality, the triangle identity and `boundedSiteAdjunctionTranspose`.  What is left
is the comparison pullback of `c.hom` precomposed with the closed comparison, which
is `v.homMap` by its definition and the specifications `constantIso_spec`,
`closedIso_spec` of `v`.
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
  sorry

end WeilConjectures.PurityFiniteSetting
