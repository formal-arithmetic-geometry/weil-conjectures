/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.DiagonalClassRootLimitProjection

/-! # Transport of the entire root cone

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

/-- Pullback of the normalized root cone agrees with completed line transport.
This statement uses the canonical ordinary root map, and contains no reduced
Kummer units map or boundary equation.

Source: literature/blueprint/latest/blueprint/part-six-operations/
sec-constructibility-upper-shriek/sec-ladic-summary/sec-late-coefficients/
sk-prop-diagonal-tower/sk-prop-diagonal-tower-coefficients.proof.md,
paragraph (3), entire root cones and the root-line limit endpoint.
(blueprint: lem-diagonal-class-root-cone-transport).

Proof: use target_normalization to identify t0 and t0prime with the actual
root-limit cones. Compare the ordinary pulled cones by their finite projections.
The canonical roots-of-unity inverse-image map, the section normalizations of
scalarDirect and the realization direct-image square, and the line normalization
of both realizations identify these projections with the adjoint of the supplied
integral Tate-line pullback. The ordinary limit universal property identifies
the full cone maps. Transpose under the normalized constant/derived-limit
adjunctions; the full K-injective counit normalization identifies their transposes
before evaluation. Exact single comparisons and the mate's shift compatibility
give degree two. Full faithfulness of realization identifies the completed map
with frame.lineComparison. Naturality moves b to the right of the limit mate,
which gives the equation below. Empty bases and the prime two require no changes. -/
theorem diagonalClassRootConeTransport
    (frame : DiagonalClassPullbackFrame l g d d' e e') :
    (diagonalClassPull l (baseW g)).mapDerivedCategory.map d.targetMap ≫
        frame.limitComparison.app
          (D.T.obj (((DerivedCategory.singleFunctor _ 0).obj
            (diagonalComparisonUnits Y))⟦(1 : ℤ)⟧)) ≫
        d'.L.R.map ((diagonalClassTowerPull l (baseW g)).mapDerivedCategory.map d.b.hom) ≫
        d'.L.R.map (diagonalClassRootShiftedPullback frame) =
      diagonalClassRootLimitEndpointRhs frame ≫ d'.L.R.map d'.b.hom := by
  sorry

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
