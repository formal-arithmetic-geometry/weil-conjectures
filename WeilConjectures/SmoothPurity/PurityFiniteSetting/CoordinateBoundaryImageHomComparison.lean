/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Affine.PurityAffineLineBoundaryRealization
public import WeilConjectures.AlgebraicGeometry.Supported.SupportedHomPullback
import WeilConjectures.SmoothPurity.PurityFiniteSetting.CoordinateBoundaryImageHomComparisonMate
import WeilConjectures.SmoothPurity.PurityFiniteSetting.CoordinateBoundaryImageHomComparisonClosed
import WeilConjectures.AlgebraicGeometry.SupportedConstantNormalization.SupportedConstantExchangeNormalization

/-! # Closed image comparison on represented morphisms

The exact closed-image mate is evaluated on a map from the constant object.
(blueprint: lem-pur-coordinate-boundary-image-hom-comparison).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.RetractedSupport

namespace WeilConjectures.PurityFiniteSetting

/-- The exact closed-image comparison transports represented morphisms with the
specified supported-constant comparison.

Source: current blueprint, cor-pur-affine-space-zero-section-purity.proof.md,
finite etale-origin transport paragraph; Milne, Section 9, Example 9.5.
(blueprint: lem-pur-coordinate-boundary-image-hom-comparison).

Proof: the underived comparison on the closed direct image of the constant sheaf
is fixed by the constant-unit equation and the restriction equation for v.closedIso.
Localize this square using the single-object comparisons. The canonical derived
closed-image mate is natural on bounded-below etale objects. Apply that naturality
to b and compose with the localized constant square. The exact/right-derived
comparisons in boundaryImageComparison cancel, yielding the displayed equality.
There is no exceptional functor or shift in this calculation. -/
theorem coordinateBoundaryImageHomComparison
    (P : PurityFiniteSetting.{u}) (T : Scheme.{u})
    (v : siteSupportHomTransport P (zeroSection T))
    (B : DerivedCategory.Plus (EtSheaves P T))
    (b : (DerivedCategory.singleFunctor (EtSheaves P T) 0).obj
      (P.constantEtale T) ⟶ B.obj) :
    ((lowerStar (Modules P) (zeroSection T)).mapDerivedCategorySingleFunctor 0).inv.app
        (P.constant T) ≫
      (lowerStar (Modules P) (zeroSection T)).mapDerivedCategory.map
        (((comparisonUpperStar (Modules P) T).mapDerivedCategorySingleFunctor 0).inv.app
          (P.constantEtale T) ≫ (nu P T).map b) =
    (DerivedCategory.singleFunctor (ProSheaves P (Line T)) 0).map v.closedIso.inv ≫
      ((comparisonUpperStar (Modules P) (Line T)).mapDerivedCategorySingleFunctor 0).inv.app
        ((Etale.lowerStar (Modules P) (zeroSection T)).obj (P.constantEtale T)) ≫
      (nu P (Line T)).map
        (((Etale.lowerStar (Modules P) (zeroSection T)).mapDerivedCategorySingleFunctor
          0).inv.app (P.constantEtale T) ≫
            (Etale.lowerStar (Modules P) (zeroSection T)).mapDerivedCategory.map b) ≫
      P.boundaryImageComparison T B := by
  exact coordinateBoundaryImageHomComparison_mate P T v
    (coordinateBoundaryImageHomComparison_closed_prefix P T v) B b

end WeilConjectures.PurityFiniteSetting
