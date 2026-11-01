/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Coordinate.CoordinateOrdinaryGysinRealizationData

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

Proof: by `R.evaluation` the right side is the closed supported morphism
`inverse single comparison ≫ map m ≫ R.epsilon`, with `R.epsilon` fixed by
`R.counit_eq`.  Choose a bounded-below injective resolution of the coefficient
object.  On it the class `R.e.hom (gysinHomToSections m)` is represented by a
supported cocycle `x` whose value at the terminal object is the image of the
constant scalar one under that morphism; this is the hypothesis of
`chi.normalization`, which then gives `chi.chi` of the class as the cocycle morphism
of the same supported morphism.  Unwinding the cocycle morphism through the
quotient comparison gives the right side.  Naturality of `chi` and of the
resolution identifies the formulas on the input itself.
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
  sorry

end WeilConjectures.PurityFiniteSetting
