/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.OrientationEtaleCoefficientTwists
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFiniteExceptionalComposition
public import WeilConjectures.AlgebraicGeometry.Projective.ProjectiveLineTraceSupplement
public import WeilConjectures.AlgebraicGeometry.Affine.Trace.AffineTraceConstruction
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriekCanonicalMaps
public import WeilConjectures.SixFunctors.Etale.Derived.Shift

/-!
# Coherent six-functor orientations

Source: main-20261015, sec-six-functors/sk-def-sf-orientation/def-sf-orientation.md
(blueprint: def-sf-orientation-etale-family).

The two comparison arrows below are counit transposes. In particular, an
orientation never supplies an arbitrary replacement for either arrow.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option genSizeOfSpec false
set_option genSizeOf false
set_option genCtorIdx false
set_option genInjectivity false
universe u v w v' w'
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Functor
namespace WeilConjectures

/-- The canonical affine-line integration: comparison with the standard
projective compactification, Rq_* of the open counit, then the normalized P1 trace.
It applies to a Noetherian base without a separatedness hypothesis.
Source: clause 4 (blueprint: def-sf-orientation-etale-family). -/
def sfOrientationAffineTrace (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (Y : Scheme.{u}) [IsNoetherian Y] (hY : IsUnit (N : Γ(Y, ⊤)))
    [HasCompactification (AffineSpace PUnit.{u + 1} Y ↘ Y)] :=
  (Etale.rightDerivedLowerShriekOfCompactificationIso A
    (HasCompactification.compactification (AffineSpace PUnit.{u + 1} Y ↘ Y))
    (affineTraceLineCompactification Y)).hom.app _ ≫
    (Etale.ordinaryFinitePushforward A (ProjectiveLine Y ↘ Y)).map
      ((Etale.affineTraceOpenLeft A Y).map
        (Etale.ordinaryFiniteShiftedLinePullback A N hA
          (Etale.projectiveLineTraceTransport N hN A hA) (ProjectiveLine.affineChart Y)
          (affineTraceProjectiveInvertible N Y hY)).inv ≫
        (Etale.affineTraceOpenAdjunction A Y).counit.app
          ((Etale.ordinaryFiniteLine A N hA (ProjectiveLine Y))⟦(2 : ℤ)⟧)) ≫
    Etale.ordinaryFiniteProjectiveLineTrace N hN A hA Y hY ≫
    (Etale.singleFunctorObjUnitIso (ModuleCat.{u + 1} A) Y).hom

end WeilConjectures
