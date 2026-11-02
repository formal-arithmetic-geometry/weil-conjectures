/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.DiagonalClassRootLimitProjection
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.DiagonalClassSingleReductionPullback
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.DiagonalClassFiniteOrdinaryRootPullback

/-! # Finite positive Cartier pullback

Source: diagonal coefficient changes, paragraph (3). -/
@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients
open DiagonalTrace
attribute [local irreducible] DerivedCategory Functor.mapDerivedCategory
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor diagonalCompletedSource

variable {l : ℕ} [Fact l.Prime] {Y Y' : Scheme.{u}} {g : Y' ⟶ Y}
  [DiagonalTraceLocalizations l (diagonalSurface Y)]
  [DiagonalTraceLocalizations l (diagonalSurface Y')]
  {hY : IsUnit (l : Γ(Y, ⊤))} {hY' : IsUnit (l : Γ(Y', ⊤))}
  {D : DiagonalDerivedReduction l (diagonalScalarExtension l (diagonalSurface Y))}
  {D' : DiagonalDerivedReduction l (diagonalScalarExtension l (diagonalSurface Y'))}
  {d : ClassLimitPresentation l Y hY D} {d' : ClassLimitPresentation l Y' hY' D'}
  {e : CompletedRealization l (diagonalSurface Y)}
  {e' : CompletedRealization l (diagonalSurface Y')}

/-- Finite Cartier classes commute with the normalized source pullback and
canonical root pullback.
Source: diagonal coefficient changes, paragraph (3), naturality of Cartier
extensions and the positive Kummer boundary.
(blueprint: lem-diagonal-class-finite-root-pullback).

Proof: the regular-source counit calculation identifies the normalized
source transport with the exact single of the ordinary reduction/source map.
The finite ordinary Cartier square then gives the desired equality. Apply the
derived evaluation functor to the source identification postcomposed with
the upstairs class and use transitivity. No derived-level detection is used. -/
theorem diagonalClassFiniteRootPullback
    (frame : DiagonalClassPullbackFrame l g d d' e e') (n : ℕ) :
    let V := (evaluation ℕᵒᵖ (DiagonalMod l (diagonalSurface Y'))).obj (op n)
    V.mapDerivedCategory.map
      ((diagonalClassTowerPull l (baseW g)).mapDerivedCategory.map d.c.hom ≫
        diagonalClassRootShiftedPullback frame) =
      V.mapDerivedCategory.map
        (((diagonalClassTowerPull l (baseW g)).mapDerivedCategory.map d.a.inv ≫
          frame.systemSource ≫ d'.a.hom) ≫ d'.c.hom) := by
  let V := (evaluation ℕᵒᵖ (DiagonalMod l (diagonalSurface Y'))).obj (op n)
  have hs := congrArg (fun s ↦ V.mapDerivedCategory.map (s ≫ d'.c.hom))
    (diagonalClassSourcePullback frame)
  exact (diagonalClassFiniteOrdinaryRootPullback frame n).trans hs.symm

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
