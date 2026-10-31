/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityGysinStructure
public import WeilConjectures.AlgebraicGeometry.Supported.SupportedHomPullback
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Coordinate.CoordinateBoundaryGeometricPullback
public import WeilConjectures.AlgebraicGeometry.Support.SupportComparisonBoundary

/-! # Normalized affine-line support charts and their canonical pullback

Source: blueprint main-20261015, affine-line orientation construction
(blueprint: thm-pur-affine-line-orientation).

These are the data and canonical maps shared by the orientation theorem and its
coordinate-pullback and local-residue steps.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.RetractedSupport

namespace WeilConjectures.PurityFiniteSetting

/-- The canonical support chart of lem-pur-gysin-structure together with the actual
snake boundary. The formulas fix both the identification and its sign; none of the
maps is an unconstrained support isomorphism.
Source: blueprint main-20261015, Gysin identification and orientation construction
(blueprint: thm-pur-affine-line-orientation). -/
structure OrientationSupportData (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) (Y : Scheme.{u}) where
  comparison : Comparison P (lineProjection Y) (zeroSection Y) (openImmersion Y)
    (AffineSpace.zeroSection_comp_over (ULift.{u} (Fin 1)) Y)
  openCoefficient : (upperStar (Modules P) (openImmersion Y)).mapDerivedCategory.obj
    (P.gysinInput h Y).obj ≅ P.derivedSheaf h (Punctured Y) true
  openCoefficient_spec : openCoefficient.hom = P.gysinOpenCoefficient h Y
  edge : (hyper P Y 2).obj (P.gysinClosed h Y) ≅
    (localClasses P Y 2).obj (P.gysinClosed h Y)
  edge_spec : edge.hom = (comparison.edge 2).app (P.gysinClosed h Y)
  support : (localClasses P Y 0).obj (P.gysinValue h Y) ≅ P.gysinSupport h Y
  support_spec : support.hom = (globalSectionsFunctor (Modules P) Y).map
      (((DerivedCategory.homologyFunctor (ProSheaves P Y) 0).shiftIso
        (2 : ℤ) 0 2 (add_zero 2)).hom.app (P.gysinClosed h Y)) ≫
      edge.inv ≫ (comparison.supportIso 2).hom.app (P.gysinEtaleInput h Y)
  boundary : Sheaf.SupportSequenceBoundary (Scheme.ProEt.topology (Line Y)) (Modules P)
    (supportRestrictionArrow (zeroSection Y)) ⊤
  boundary_exact : Sheaf.SupportSequenceExact (Scheme.ProEt.topology (Line Y)) (Modules P)
    (supportRestrictionArrow (zeroSection Y)) ⊤ boundary
  boundary_normalized : supportBoundaryNormalization (Scheme.ProEt.topology (Line Y))
    P.Coefficient (supportRestrictionArrow (zeroSection Y)) boundary

/-- The actual supported coordinate boundary in the published Gysin chart.
Source: blueprint orientation construction, pur_s sends 1 to the boundary of kappa(t)
(blueprint: thm-pur-affine-line-orientation). -/
def OrientationSupportData.coordinateBoundary (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) {Y : Scheme.{u}}
    (D : OrientationSupportData P h Y) (a : Y ⟶ Spec (CommRingCat.of P.field.k)) :
    P.gysinSupport h Y :=
  (D.boundary 1).app ⟨P.gysinInput h Y, trivial⟩
    (P.gysinKummerSection h Y a D.comparison D.openCoefficient)

/-- Canonical inverse image of the affine-line coefficient complex, through comparison
and the scalar-extended root pullback. This is defined for arbitrary base morphisms.
Source: blueprint affine-line datum and geometric-fibre paragraph
(blueprint: thm-pur-affine-line-orientation). -/
def orientationInputPullback (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) {T Y : Scheme.{u}} (f : T ⟶ Y) :
    (upperStar (Modules P) (AffineSpace.map (ULift.{u} (Fin 1)) f)).mapDerivedCategoryPlus.obj
      (P.gysinInput h Y) ⟶ P.gysinInput h T :=
  P.coordinateProCoefficientPullback h (coordinateLineMap f)

/-- Pullback on the actual supported cohomology, with the canonical coefficient map.
The transport's supportUnit_spec fixes the underived kernel map by its inclusion;
derivedMap is its published right-derived base-change map.
Source: Milne, Section 9; blueprint orientation proof, restriction to a geometric point
(blueprint: thm-pur-affine-line-orientation). -/
def orientationSupportRestriction (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) {T Y : Scheme.{u}} (f : T ⟶ Y)
    (p : proEtaleSupportHomTransport P (zeroSection Y) (zeroSection T)
      (AffineSpace.map (ULift.{u} (Fin 1)) f)) :
    P.gysinSupport h Y ⟶ P.gysinSupport h T :=
  (DerivedCategory.Plus.homologyFunctor (Modules P) 2).map
      ((p.derivedMap (hB := Scheme.ProEt.isContinuous_overPullback
        (AffineSpace.map (ULift.{u} (Fin 1)) f))).app (P.gysinInput h Y)) ≫
    (Sheaf.supportHypercohomologyFunctor (Scheme.ProEt.topology (Line T)) (Modules P)
      (supportRestrictionArrow (zeroSection T)) 2).map (P.orientationInputPullback h f)

end WeilConjectures.PurityFiniteSetting
