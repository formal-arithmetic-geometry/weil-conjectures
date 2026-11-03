/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Diagonal.DiagonalDncChartNormalization

/-! # The ordinary inverse orientation in a specified affine coordinate chart -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace WeilConjectures.PurityFiniteSetting.AffineOrdinaryIntegrationCoordinates

section Coordinate
variable (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
  (r : ℕ) (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  [SmoothOfRelativeDimension r f]
  (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
  (c : X ≅ affineTraceTower Y r) (w : c.hom ≫ affineTraceProjection Y r = f)
  (N : Etale.EtaleCompactSupportNormalization P.Coefficient)
  (t : Etale.OrdinaryFiniteTwistTransport P.Coefficient P.diagonalExponent
    P.diagonalExponent_annihilates)
  (D : ∀ (T : Scheme.{u}) [IsNoetherian T]
    (hT : IsUnit (P.diagonalExponent : Γ(T, ⊤))),
    Etale.OrdinaryFiniteP1Datum P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates t T hT)

/-- The normalized coordinate integration adjunct, using only the ordered affine counit,
coefficient pullback and source locality. No diagonal orientation enters this construction.
Source: composition proof Step 1, trivial-frame normalization of vector integration.
(blueprint: new-pur-affine-integration-ordinary-coordinate-transpose). -/
def gamma :
    letI := P.noetherian aY
    letI := P.noetherian (f ≫ aY)
    letI := affineTraceNoetherian Y r
    letI := Dnc.compactifiable P f aY
    letI : HasCompactification (c.hom ≫ affineTraceProjection Y r) :=
      HasCompactification.of_eq w.symm
    P.diagonalTwistEtale X r ⟶ P.diagonalOrdinaryDualizing f := by
  letI := P.noetherian aY
  letI := P.noetherian (f ≫ aY)
  letI := affineTraceNoetherian Y r
  letI := Dnc.compactifiable P f aY
  letI : HasCompactification (c.hom ≫ affineTraceProjection Y r) :=
    HasCompactification.of_eq w.symm
  exact (Etale.vectorIntegrationBaseCoefficientPullback P.Coefficient P.diagonalExponent
    P.diagonalExponent_annihilates t c.hom
      (affineTraceInvertible P.diagonalExponent Y (P.diagonalExponent_isUnit aY) r) r).inv ≫
    (Etale.ordinaryFinitePullback P.Coefficient c.hom).map
      (P.diagonalAffineMate t D Y (P.diagonalExponent_isUnit aY) r) ≫
    (P.diagonalEtaleLocality N c.hom (affineTraceProjection Y r)).hom ≫
    (P.diagonalDualizingCongr w).hom

/-- The ordinary diagonal orientation is inverse to the specified coordinate integration.
Source: composition proof Step 1 and orientation-charts Step 4.
(blueprint: new-pur-affine-integration-ordinary-coordinate-transpose).
Proof: the chart is an isomorphism and hence etale, separated, quasi-compact and locally
of finite type. Apply the normalization formula for the ordinary orientation to precisely
this chart and its structural equation w. No choice of a new comparison is made. -/
theorem orientation_inv :
    letI := P.noetherian aY
    letI := P.noetherian (f ≫ aY)
    letI := Dnc.compactifiable P f aY
    (P.chartOrdinaryOrientation r f aY).inv = gamma P r f aY c w N t D := by
  exact P.chartOrientation_coordinate_formula r f aY c.hom w N t D

end Coordinate

end WeilConjectures.PurityFiniteSetting.AffineOrdinaryIntegrationCoordinates
