/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.DiagonalClassRootLimitProjection

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

/-- The finite positive Cartier square, with the source written entirely in
ordinary sheaves and the canonical exact single comparison.
Source: diagonal coefficient changes (3), naturality of Cartier extensions
and Kummer maps and the finite positive normalization of the system class.
(blueprint: lem-diagonal-class-finite-ordinary-root-pullback).

Proof: unpack finite_normalization on both bases at n. Exact evaluation
commutes with geometric inverse image, singles and the degree-two shift.
The quotient equations for ordinaryReduction identify the source comparison
with finite closed base change: transpose through the scalar adjunction and
precompose with the quotient map; both send every supported integral section
to its pulled-back section modulo l^(n+1). Since the quotient map is epic this
identifies the ordinary maps. The finite root normalizations identify the
target comparison with the canonical Kummer kernel map: forgetting scalars
and composing with the monic roots inclusion reduces this to pullback of
units. The normalized Cartier reduction comparison identifies the finite
classes with the relative supported Kummer classes. Pullback of the pole
extension preserves the positive inverse-equation generator, so naturality
of its boundary followed by the Kummer boundary gives the finite Cartier
square. The exact scalar-restriction comparison carries this equality back
to the fixed p-adic module category; the exact evaluation/single and shift
comparisons give exactly the displayed derived equality. All sources and
root maps retain their specified normalization; no derived-level faithfulness
or assertion about arbitrary Cartier class families is used. -/
theorem diagonalClassFiniteOrdinaryRootPullback
    (frame : DiagonalClassPullbackFrame l g d d' e e') (n : ℕ) :
    let V := (evaluation ℕᵒᵖ (DiagonalMod l (diagonalSurface Y'))).obj (op n)
    V.mapDerivedCategory.map
      ((diagonalClassTowerPull l (baseW g)).mapDerivedCategory.map d.c.hom ≫
        diagonalClassRootShiftedPullback frame) =
      V.mapDerivedCategory.map
        ((((diagonalClassTowerPull l (baseW g)).mapDerivedCategorySingleFunctor 0).hom.app
            (D.ordinary.E.obj (diagonalIntegralSource Y)) ≫
          (DerivedCategory.singleFunctor _ 0).map
            (frame.ordinaryReduction.hom.app (diagonalIntegralSource Y) ≫
              D'.ordinary.E.map (diagonalBoundarySource (baseW g) (baseP g)
                (diagonalBaseChange_cartesian g).toCommSq))) ≫ d'.c.hom) := by
  sorry

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
