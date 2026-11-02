/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.DiagonalClassPullbackFrame
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.DiagonalClassRootPullback

/-! # Shifted root pullback and completed endpoint composite

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

/-- The right composite in the root-limit endpoint equation: the scalar comparison
at the completed codomain, restriction of the line comparison, and the target map.
Source: literature/blueprint/latest/blueprint/part-six-operations/
sec-constructibility-upper-shriek/sec-ladic-summary/sec-late-coefficients/
sk-prop-diagonal-tower/sk-prop-diagonal-tower-coefficients.proof.md, paragraph (3).
(blueprint: def-diagonal-class-root-limit-endpoint-rhs). -/
def diagonalClassRootLimitEndpointRhs
    (frame : DiagonalClassPullbackFrame l g d d' e e') :=
  frame.scalarComparison.hom.app (diagonalCompletedCodomain l Y) ≫
      (diagonalCompletedUnderlying l (diagonalSurface Y')).map
        frame.lineComparison.hom ≫ d'.targetMap

/-- The canonical shifted map of ordinary root towers: degree-two shift comparison,
exact single comparison, and the single functor applied to the canonical ordinary
root pullback.
Source: literature/blueprint/latest/blueprint/part-six-operations/
sec-constructibility-upper-shriek/sec-ladic-summary/sec-late-coefficients/
sk-prop-diagonal-tower/sk-prop-diagonal-tower-coefficients.proof.md,
paragraph (3), Kummer sequences natural under pullback.
(blueprint: def-diagonal-class-root-limit-projection). -/
def diagonalClassRootShiftedPullback
    (frame : DiagonalClassPullbackFrame l g d d' e e') :=
  ((diagonalClassTowerPull l (baseW g)).mapDerivedCategory.commShiftIso (2 : ℤ)).hom.app
      ((DerivedCategory.singleFunctor _ 0).obj d.H) ≫
    (((diagonalClassTowerPull l (baseW g)).mapDerivedCategorySingleFunctor 0).hom.app d.H ≫
      (DerivedCategory.singleFunctor _ 0).map
        (diagonalClassOrdinaryRootPullback frame))⟦(2 : ℤ)⟧'

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
