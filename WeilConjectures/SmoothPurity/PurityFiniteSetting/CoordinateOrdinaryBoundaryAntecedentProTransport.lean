/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Coordinate.CoordinateLocalizationSplice
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Affine.PurityAffineLineBoundaryRealization
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.CoordinateOrdinaryBoundaryProCoordinateCancellation
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.CoordinateOrdinaryBoundaryProCounitNormalization

/-! Pro-etale counit transport for the coordinate ordinary antecedent.
(blueprint: new-lem-pur-coordinate-ordinary-boundary-antecedent-pro-transport).

The proof expands the specified coordinate comparison and the affine-line realization
counit square.  It is split from the parent because the expansion crosses the etale
right-adjoint shift and the closed-image comparison independently.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.RetractedSupport

namespace WeilConjectures.PurityFiniteSetting

/-- The comparison equation for an antecedent implies its transported ordinary counit
identity after applying the site comparison and the displayed shift comparison.

Source: current blueprint, cor-pur-affine-space-zero-section-purity.proof.md, composition
of adjunctions in the first paragraph and the transport of compositions and counits to
finite etale-origin objects
(blueprint: new-lem-pur-coordinate-ordinary-boundary-antecedent-pro-transport).

Proof: let f be the exact derived realization of c, aj the chosen adjunction of the
derived closed direct image with its right adjoint J, ag the published exceptional
adjunction and beta = aj.rightAdjointUniq ag. Expand coordinateOrdinaryToGysin and
boundaryExceptionalComparison: after the inverse single comparison both sides are nu of
an etale map followed by the shift comparisons, the collapse inverse/hom pair and the
comparison unit boundedSiteRho; these common factors are isomorphisms, so full
faithfulness of nu on bounded-below objects (sk-prop-sf-comparison) turns hb into
b = ag.homEquiv f followed by the degree-two shift comparison of G and beta inverse
shifted by two. For this b, naturality of the exact/right-derived comparison moves it
past the direct image of b; right-adjoint uniqueness identifies the image of beta
inverse followed by the aj counit with the ag counit; compatibility of the adjunction
with shifts identifies the shifted counit with its value on K[2]; the adjunct-counit
identity returns f, and the inverse single comparison cancels the defining single
comparison of f, leaving c.hom. Apply nu and compose with its shift comparison. -/
theorem coordinateOrdinary_boundaryAntecedent_proTransport
    (P : PurityFiniteSetting.{u}) (h : P.ramificationIndex ∣ P.level)
    (T : Scheme.{u}) (aT : T ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aT] [QuasiCompact aT] [IsSeparated aT]
    (c : Ext ((Etale.lowerStar (Modules P) (zeroSection T)).obj (P.constantEtale T))
      (P.twistEtale h (Line T)) 2)
    (b : (DerivedCategory.singleFunctor (EtSheaves P T) 0).obj
      (P.constantEtale T) ⟶ P.boundaryEtaleValue h T)
    (hb :
      ((comparisonUpperStar (Modules P) T).mapDerivedCategorySingleFunctor 0).inv.app
          (P.constantEtale T) ≫ (nu P T).map b ≫ P.boundaryExceptionalComparison h T =
        P.coordinateOrdinaryToGysin h T
          (Etale.supportedExactDerivedMap (Etale.lowerStar (Modules P) (zeroSection T))
            (P.constantEtale T) (P.twistEtale h (Line T)) c)) :
    (nu P (Line T)).map
        (((Etale.lowerStar (Modules P) (zeroSection T)).mapDerivedCategorySingleFunctor
          0).inv.app (P.constantEtale T) ≫
          (Etale.lowerStar (Modules P) (zeroSection T)).mapDerivedCategory.map b ≫
          P.boundaryEtaleCounit h T) ≫
        ((nu P (Line T)).commShiftIso (2 : ℤ)).hom.app
          (P.gysinEtaleInput h T).obj =
      (nu P (Line T)).map c.hom ≫
        ((nu P (Line T)).commShiftIso (2 : ℤ)).hom.app
          (P.gysinEtaleInput h T).obj := by
  let f := Etale.supportedExactDerivedMap
      (Etale.lowerStar (Modules P) (zeroSection T)) (P.constantEtale T)
      (P.twistEtale h (Line T)) c
  have hcoord : P.coordinateOrdinaryToGysin h T f =
      ((comparisonUpperStar (Modules P) T).mapDerivedCategorySingleFunctor 0).inv.app
          (P.constantEtale T) ≫
        (nu P T).map (coordinateOrdinaryTranspose P h T f) ≫
        (nu P T).map (((Etale.rightDerivedUpperShriek P.Coefficient
          (zeroSection T)).commShiftIso (2 : ℤ)).hom.app
            (P.gysinEtaleInput h T).obj) ≫
        ((nu P T).commShiftIso (2 : ℤ)).hom.app _ ≫
        (shiftFunctor _ (2 : ℤ)).map
          (boundedSiteRho P.Coefficient
            (Etale.rightDerivedUpperShriek P.Coefficient (zeroSection T))
            (P.gysinEtaleInput h T).obj) := by
    with_unfolding_all rfl
  obtain ⟨m, hm⟩ := coordinateOrdinary_boundary_proCounitNormalization P h T aT b
  simpa [hm] using coordinateOrdinary_boundary_proCoordinateCancellation
    P h T aT c b m hb hm

end WeilConjectures.PurityFiniteSetting
