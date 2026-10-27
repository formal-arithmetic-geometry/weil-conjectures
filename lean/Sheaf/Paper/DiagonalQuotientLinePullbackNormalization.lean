/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R3
-/
module

public import Sheaf.Paper.DiagonalCoefficientFamilyPullback
public import Sheaf.Paper.DiagonalScalarPullbackComparison

/-! # Quotient line normalization of the scalar/pullback mate

Source: diagonal coefficient changes, paragraph (3), line endpoint normalization.
(blueprint: lem-diagonal-quotient-line-pullback-normalization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

attribute [local irreducible] quotientLine quotientLineMap derivedUpper derivedScalars
  singlePullback PullEndpoint.shift Endpoint.shift scalarPullbackComparison
  Functor.leftDerivedFunctor Functor.mapDerivedCategory spIntegralTwist spIntegralComparison

/-- The scalar/pullback mate respects the prescribed quotient line endpoints after shift.
This identity involves no diagonal class, diagram, supported source, or trace.

Source: latest blueprint, sec-six-functors-basics/sk-prop-diagonal-tower/
sk-prop-diagonal-tower-coefficients.proof.md, paragraph (3), coefficient functors
commuting with pullback; lem-diagonal-quotient-class-pullback, proof step 1 (line part).
(blueprint: lem-diagonal-quotient-line-pullback-normalization).

Proof: Transpose both composites through the derived scalar/restriction adjunction at X.
Endpoint.normalization replaces the scalar endpoints by the degree-zero images of their
specified semilinear maps. The exact inverse-image single comparison transports these
images by the ordinary restriction/pullback comparison. Transpose the integral and
quotient PullEndpoints through the module inverse-image adjunction. Their normalizations
identify their underlying adjoints with the supplied sheaf maps. The remaining ordinary
square is the tensor quotient formula: precompose by the pulled-back extendπ, use
QuotientPullMap, and naturality of the tensor extension unit. The pulled-back extendπ is
epic, so its cancellation proves the square. Faithfulness of the module forgetful functor
then proves the module square and injectivity of the derived adjunction proves the
unshifted identity. The comparison is a mate of exact restriction/pullback, so commutes
with shifts, with the adjunction-induced shift structures. Shift by two and use naturality
of those structures to obtain the displayed equation. This is valid also for n = 0,
π = 0, unit π, and ramified quotient levels: no flatness of the coefficient map is used. -/
theorem diagonalQuotient_linePullbackNormalization
    (l : ℕ) [Fact l.Prime] (E : PadicAlgCl.FiniteIntermediateField l)
    (π : PadicAlgCl.integers l E) (n : ℕ)
    {X S : Scheme.{u}} (f : X ⟶ S)
    (e₀ : PullEndpoint (Profinite.padicIntegersRingObj.{u} l E.1) f
      (spIntegralTwist S l E) (spIntegralTwist X l E) (spIntegralComparison f l E))
    (eS : Endpoint (quotientMap l E π n) (spIntegralTwist S l E)
      (quotientLine l E π n S) (quotientLineMap l E π n S))
    (eX : Endpoint (quotientMap l E π n) (spIntegralTwist X l E)
      (quotientLine l E π n X) (quotientLineMap l E π n X))
    (m : (upperStar Ab.{u + 1} f).obj (quotientLine l E π n S).X ⟶
      (quotientLine l E π n X).X)
    (hm : QuotientPullMap l E π n f m)
    (e : PullEndpoint
      (Profinite.continuousMapRingObj.{u} (completedResidue l E π n)) f
      (quotientLine l E π n S) (quotientLine l E π n X) m) :
    ScalarPullbackEndpointSquare (quotientMap l E π n) f e₀ eS eX e := by sorry

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
