/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.DiagonalClassPullbackFrame

/-! # The Kummer root-line limit endpoint
Source: the latest blueprint, diagonal coefficient changes, paragraph (3).
-/

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

/-- Root-limit and degree-two shift normalization for the pulled Kummer endpoint.
This is independent of the supported source and of any completed class arrow.

Source: literature/blueprint/latest/blueprint/sec-six-functors-basics/
sk-prop-diagonal-tower/sk-prop-diagonal-tower-coefficients.proof.md, paragraph (3),
Cartesian roots, the entire Kummer system, and the root-line limit endpoint.
(blueprint: lem-diagonal-class-root-limit-endpoint).

Proof: construct the canonical map of the positive Kummer short exact sequences
using inverse image of units and the kernel-normalized root maps. On a regular
resolution the normalized quotient comparison computes frame.reduction, so its
map on the Kummer complexes is the canonical one. Compare d.b and d'.b after
transport through the supplied d.roots and d'.roots to the canonical root
systems. These ordinary comparisons are linear: a level is annihilated by its
prime power, so its scalar action is determined by the integer residue. Their
boundary equations and finite_normalization identify every finite positive
Cartier class. To see that this fixes the root identification, turn a comparison
of shifted singles
into a morphism of ordinary root sheaves. Etale locally those sheaves are free
of rank one over the residue coefficient. The Cartier purity normalization on
the diagonal detects the scalar of this morphism there: on a standard chart
the equation is t = a - b, and the prescribed positive Cartier residue of
the inverse-equation generator is +1. Multiplying the class by a scalar
multiplies that residue by the same scalar, so the finite positive normalization
forces the scalar to be 1 on the
diagonal. The nonzero locus of a locally constant scalar difference is clopen.
Each geometric fibre of the relative product is connected, so such a locus
either contains the entire fibre or misses it. Since the diagonal meets every
fibre, a scalar difference vanishing there vanishes everywhere. Thus the
normalized finite root maps agree. Equality at each level now
gives equality of ordinary strict-system maps, not arbitrary derived maps.

The target_normalization equations identify t₀ and t₀' with the actual root
limit cones. Cartesian integral Tate pullback and the line_normalization of the
two realizations identify their pulled map with frame.data.endpoints.lineW.
Compare the entire cones by the ordinary limit universal property. Transpose
under the normalized constant/derived-limit adjunctions; their full counit
normalizations on K-injective towers give equality before evaluation. Naturality
with the root identification gives the unshifted endpoint equation. The exact
single and canonical shift comparisons, including the constant/limit mate's
shift compatibility, give its degree-two shift. Full faithfulness of realization
identifies the resulting completed-line transport with frame.lineComparison,
which proves limit_endpoint. Empty bases give the unique maps between zero
objects; residue levels have positive exponent, including at the prime two. -/
theorem diagonalClassRootLimitEndpoint (l : ℕ) [Fact l.Prime]
    {Y Y' : Scheme.{u}} (g : Y' ⟶ Y)
    [DiagonalTraceLocalizations l (diagonalSurface Y)]
    [DiagonalTraceLocalizations l (diagonalSurface Y')]
    (hY : IsUnit (l : Γ(Y, ⊤))) (hY' : IsUnit (l : Γ(Y', ⊤)))
    (D : DiagonalDerivedReduction l (diagonalScalarExtension l (diagonalSurface Y)))
    (D' : DiagonalDerivedReduction l (diagonalScalarExtension l (diagonalSurface Y')))
    (d : ClassLimitPresentation l Y hY D) (d' : ClassLimitPresentation l Y' hY' D')
    (e : CompletedRealization l (diagonalSurface Y))
    (e' : CompletedRealization l (diagonalSurface Y'))
    (frame : DiagonalClassPullbackFrame l g d d' e e') :
    DiagonalClassLineEndpoint frame := by sorry

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
