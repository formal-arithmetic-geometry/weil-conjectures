/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SecSmoothPurity.TransportAffineGeometry
public import WeilConjectures.SecSmoothPurity.TransportFiniteLineDerived
public import WeilConjectures.SecSmoothPurity.TransportFiniteSupport
public import WeilConjectures.AlgebraicGeometry.ProjectiveLineTraceSupplement
public import WeilConjectures.AlgebraicGeometry.AffineTraceConstruction

/-! # Purity transport statement interfaces

Source: current blueprint sk-thm-purity-transport, canonical comparison clauses.
(blueprint: def-pur-transport-affine-integration). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.PurityTransport

/-- Integration on the affine line is Rq_* of the open counit followed by the
projective trace whose Kummer Chern generator maps to +1. The compactification is
literally the standard chart; no arbitrary trace or orientation is introduced.
Source: affine-line integration (blueprint: def-pur-transport-affine-integration). -/
def ordinaryAffineIntegration (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (Y : Scheme.{u}) [IsNoetherian Y] (hY : IsUnit (N : Γ(Y, ⊤))) :=
  (Etale.ordinaryFinitePushforward A (ProjectiveLine Y ↘ Y)).map
    ((Etale.affineTraceOpenLeft A Y).map
      (Etale.ordinaryFiniteShiftedLinePullback A N hA
        (Etale.projectiveLineTraceTransport N hN A hA) (ProjectiveLine.affineChart Y)
        (affineTraceProjectiveInvertible N Y hY)).inv ≫
      (Etale.affineTraceOpenAdjunction A Y).counit.app
        ((Etale.ordinaryFiniteLine A N hA (ProjectiveLine Y)) ⟦(2 : ℤ)⟧)) ≫
    Etale.projectiveLineTrace N hN A hA Y hY

end AlgebraicGeometry.ProEtale.PurityTransport
