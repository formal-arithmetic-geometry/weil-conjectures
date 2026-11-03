/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Coordinate.CoordinateLocalizationSplice
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Affine.PurityAffineLineBoundaryRealization
@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.RetractedSupport
namespace WeilConjectures.PurityFiniteSetting
/-- The chosen ordinary closed counit transports through the comparison factors.
This is the counit-normalization subcalculation in the pro-etale transport proof.
(blueprint: new-lem-pur-coordinate-ordinary-boundary-antecedent-pro-transport). -/
theorem coordinateOrdinary_boundary_proCounitNormalization
    (P : PurityFiniteSetting.{u}) (h : P.ramificationIndex ∣ P.level)
    (T : Scheme.{u}) (aT : T ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aT] [QuasiCompact aT] [IsSeparated aT]
    (b : (DerivedCategory.singleFunctor (EtSheaves P T) 0).obj
      (P.constantEtale T) ⟶ P.boundaryEtaleValue h T) :
    ∃ m : (DerivedCategory.singleFunctor (EtSheaves P (Line T)) 0).obj
        ((Etale.lowerStar (Modules P) (zeroSection T)).obj (P.constantEtale T)) ⟶
      (P.gysinEtaleInput h T).obj⟦(2 : ℤ)⟧,
      m = ((Etale.lowerStar (Modules P) (zeroSection T)).mapDerivedCategorySingleFunctor
          0).inv.app (P.constantEtale T) ≫
        (Etale.lowerStar (Modules P) (zeroSection T)).mapDerivedCategory.map b ≫
        P.boundaryEtaleCounit h T := by sorry
end WeilConjectures.PurityFiniteSetting
