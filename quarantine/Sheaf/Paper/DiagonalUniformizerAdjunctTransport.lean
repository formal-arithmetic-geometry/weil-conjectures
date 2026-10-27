/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D7
-/
module

public import Sheaf.Paper.DiagonalUniformizerAdjunctConditions

/-! # Transport of the canonical completed Chern adjunct

Source: diagonal tower coefficient changes proof (1), reduction of the section class.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

attribute [local irreducible] quotientLine quotientLineMap derivedScalars
  QuotientLineRealization Functor.mapDerivedCategory Functor.leftAdjoint
  Functor.rightAdjoint RestrictionSquare.mate CompletedRealization.singleUnit
  CompletedRealization.shiftedLine FiniteRealization.derivedUnit

variable (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
  [IsNoetherian Y] [IsNoetherian (ProjectiveLine Y)]
  [DiagonalTraceLocalizations l Y]
  [DiagonalTraceLocalizations l (ProjectiveLine Y)]


/-- The prescribed comparisons transport the model adjunct to the local coefficient image.

Source: latest blueprint, diagonal tower coefficient changes proof (1), applying
coefficient functors to the section-class construction; trace proof (1), adjunction.
(blueprint: lem-diagonal-uniformizer-adjunct-transport).

Proof: use the actual model.chernAdjoint defining systemChern. The identity model
q_model identifies its pulled-back Picard class with O(1). The coefficient-pullback
normalization sends one to one. The ordinary section and varying_normalization
equations identify the varying comparison with its derived adjunction mate. The full
derived-unit equations for the limit and completed squares then show that the
constant-scalar restriction of the completed adjunct of p.z is the prescribed limit
of systemChern. The two normalization conditions in p, fullness of completed scalar
restriction, and completeness of the unit and shifted line identify this adjunct
with p.c. Direct image preserves completeness by its exact additive left adjoint.

Apply the two coefficient adjunctions next. RestrictionSquare.mate is the mate of
its normalized restriction comparison. Naturality of adjunction transports an
adjunct to that of the scalar image of its local arrow. Endpoint.normalization
identifies the unit endpoints with scalar insertion and the positive-line endpoints
with the prescribed shifted maps, also for the nonflat quotient. Finally the finite
ordinary square and full universal-unit equation identify its comparison with the
finite adjunction mate; presentation.hcanonical fixes the canonical derived model
after q_canonical. Composing the four equations gives exactly Transported, including
all eight endpoints. No finite Kummer normalization, trace or degree equation is
used. The calculation includes n=0, the empty scheme and the zero coefficient ring. -/
theorem diagonalUniformizer_adjunctTransport
    (s : UniformizerChernNormalizationData l Y)
    (p : NormalizedAdjunctPair l Y s) : p.Transported l Y s := by sorry

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
