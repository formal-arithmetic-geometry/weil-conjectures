/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Coordinate.CoordinateLocalizationSplice
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Affine.PurityAffineLineBoundaryRealization
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Affine.PurityAffineLineOrientationData

/-! # Realization data for ordinary coordinate Gysin evaluation

This packages the affine-line supported-Hom realization and its chart comparison.
(blueprint: lem-pur-coordinate-ordinary-gysin-support-evaluation).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.RetractedSupport

namespace WeilConjectures.PurityFiniteSetting

/-- A chosen affine-line supported-Hom realization, together with its comparison to a
published orientation chart and its evaluation formula.  The fields are supplied by
`affine_line_boundary_realization`.  The counit `epsilon` is pinned by the counit
equation `counit_eq` through the canonical comparisons `eK` and `d` (their specs
`eK_spec`, `d_spec`), so `chi` is fixed on every realized support class by
`evaluation`; neither is a freely chosen isomorphism.
Source: current blueprint, cor-pur-affine-space-zero-section-purity.proof.md,
finite etale-origin transport paragraph; the realization lem-pur-affine-line-boundary-realization
(blueprint: def-pur-coordinate-ordinary-gysin-realization-data). -/
structure CoordinateOrdinaryGysinRealizationData (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) (T : Scheme.{u})
    (D : OrientationSupportData P h T) where
  chi : BoundarySupportedHom P T
  e : (localClasses P T 0).obj (P.gysinValue h T) ≅ P.gysinSupport h T
  epsilon : (lowerStar (Modules P) (zeroSection T)).mapDerivedCategory.obj
      (P.gysinValue h T) ⟶ (P.gysinInput h T).obj⟦(2 : ℤ)⟧
  hb : DerivedCategory.TStructure.t.plus (P.boundaryEtaleValue h T)
  eK : (nu P T).obj (P.boundaryEtaleValue h T) ≅ P.gysinValue h T
  d : (nu P (Line T)).obj
      ((Etale.lowerStar (Modules P) (zeroSection T)).mapDerivedCategory.obj
        (P.boundaryEtaleValue h T)) ≅
    (lowerStar (Modules P) (zeroSection T)).mapDerivedCategory.obj
      ((nu P T).obj (P.boundaryEtaleValue h T))
  eK_spec : eK.hom = P.boundaryExceptionalComparison h T
  d_spec : d.hom = P.boundaryImageComparison T ⟨P.boundaryEtaleValue h T, hb⟩
  counit_eq : d.hom ≫ (lowerStar (Modules P) (zeroSection T)).mapDerivedCategory.map eK.hom ≫
      epsilon =
    (nu P (Line T)).map (P.boundaryEtaleCounit h T) ≫
      ((nu P (Line T)).commShiftIso (2 : ℤ)).hom.app (P.gysinEtaleInput h T).obj
  chart_eq : e.hom = D.support.hom
  evaluation : ∀ m : P.derivedSheaf h T false ⟶ P.gysinValue h T,
    (chi.hom.app (P.gysinInput h T))
        (e.hom (P.gysinHomToSections h T m)) =
      ((lowerStar (Modules P) (zeroSection T)).mapDerivedCategorySingleFunctor 0).inv.app
          (P.constant T) ≫
        (lowerStar (Modules P) (zeroSection T)).mapDerivedCategory.map m ≫ epsilon

end WeilConjectures.PurityFiniteSetting
