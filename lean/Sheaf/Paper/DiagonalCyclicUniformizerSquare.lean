/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R4
-/
module

public import Sheaf.Paper.DiagonalUniformizerRootFrame

/-! # Reassociation of cyclic and uniformizer coefficient reductions

Source: diagonal tower coefficient changes, paragraph (1), derived coefficient
transitivity and normalized root projections.
(blueprint: lem-diagonal-cyclic-uniformizer-square).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

attribute [local irreducible] quotientLine quotientLineMap cyclicLine cyclicLineMap
  derivedScalars QuotientLineRealization finiteRealizedClass CyclicCartierFrame.reduce

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

/-- The coefficient square for an arbitrary initial arrow and scalar-compatible
integral and quotient diagrams. There is no completed arrow, limit equation or
Cartier normalization of that initial arrow among the hypotheses.

Source: latest blueprint, sec-six-functors-basics/sk-prop-diagonal-tower/
sk-prop-diagonal-tower-coefficients.proof.md (1), coefficient extension and cofinal
finite reductions; Cartier class coefficient naturality, paragraph (4).
(blueprint: lem-diagonal-cyclic-uniformizer-square).

Proof: Pull the maps Z_l -> O_E -> O_E/(pi)^(n+1) to W and P. The
coefficient isomorphisms of the finite realizations identify their target ring
objects with the ordinary constant A. Since hA kills l^(n+1), these pulled-back
maps factor through the cyclic quotient. The sheafified quotient universal
property identifies the induced map from R with cartierResidueAlgebra: both are
the unital map fixed by the integer action.
Transitivity of derived extension identifies the two routes from Z_l to A.
Its adjunction unit sends a pure tensor (x tensor r) tensor a to x tensor ra.
Use this formula and the Endpoint.normalization equations to identify the
source units with direct images of eta. On the target, IntegralRoots.projections
and the kernel inclusions of FiniteRoots identify the root tensor map with
theta; the two LineEndpoint normalizations make the same statement after finite
realization. The supplied source_normalization and line_normalization determine these maps on the
sheafified constant generators and pure root tensors. Naturality of the exact
realization's single and shift comparisons carries these endpoint equations
to derived categories. Apply the two supplied ScalarCompatibility.delta
squares, then cancel their endpoint isomorphisms. This gives the displayed
Yoneda square, since Ext.homEquiv identifies composition with degree-zero
classes with composition of the corresponding single and shifted-single maps.
No property of d0.delta is used. In particular no Cartier class is assumed or
proved here, and no detection from separate finite projections is invoked.
This works for a ramified quotient: transitivity uses derived tensor, not
flatness over Z/l^(n+1). The finite realization identifies the supplied ordinary coefficient ring A
with the pulled-back quotient ring object; its coefficient unit fixes the ring action.
For the zero coefficient ring both sides are zero. -/
theorem diagonalCyclic_uniformizerSquare
    (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
    (E : PadicAlgCl.FiniteIntermediateField l) (π : PadicAlgCl.integers l E) (n : ℕ)
    (A : Type (u + 1)) [CommRing A]
    (hA : ((l ^ (n + 1) : ℕ) : A) = 0)
    (q : UniformizerSquareData l Y E π n A hA) :
    q.equation l Y E π n A hA := by sorry

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
