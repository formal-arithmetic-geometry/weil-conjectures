/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Y3
-/
module

public import Sheaf.Paper.DiagonalCoefficientFamilyPullback
public import Sheaf.Paper.DiagonalPullbackSquares

/-! # Scalar pasting of the three trace squares

Source: diagonal tower coefficient changes, paragraph (3), scalar base change.
(blueprint: lem-diagonal-quotient-trace-pullback).
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

attribute [local irreducible] quotientLine quotientLineMap derivedUpper derivedLower
  derivedScalars modelExchange singlePullback PullEndpoint.shift Endpoint.shift

/-- The three trace base-change squares after uniformizer reduction. This
contains exchange invertibility on the specified shifted lines but asserts no
compatibility of the diagonal class.

Source: latest blueprint, sec-six-functors-basics/sk-prop-diagonal-tower/
sk-prop-diagonal-tower-coefficients.proof.md, paragraph (3), compatibility of the
trace with the coefficient functors; original quotient-base-change proof, step 2.
(blueprint: lem-diagonal-quotient-trace-pullback).

Proof: Use the given scalar.q.comparison_iso and scalar'.q.comparison_iso
(and the p1 and p2 fields) on the shifted integral lines. After inverse image,
these comparisons remain invertible. The integral PullEndpoints identify the
pulled-back integral lines with those on the new base; naturality of the scalar
mates transports the second comparison_iso along this line isomorphism. Thus
all scalar/direct-image comparisons used in the pasting are already known to
be invertible. No assertion for arbitrary complexes or resolution of the
quotient coefficient is needed.
For each of q, p1 and p2, apply quotient extension to the integral trace square.
Paste with scalar.q.trace and scalar'.q.trace (respectively the p1 and p2
fields). The scalar/inverse-image compositors identify the coefficient-unit
endpoints by their ordinary adjunction normalization. They identify the line
endpoints by the two QuotientPullMap equations, checked after the epic tensor
quotient projection. Naturality of the compositor under shifting identifies the
shifted endpoints. The interchange identity for adjunction mates identifies the
pasted direct-image morphism with derivedExchange; q_unit, p1_unit and p2_unit
of the four diagrams identify their right derived presentations with the
canonical units, hence the resulting morphism is exactly modelExchange.
Its invertibility follows by cancelling the pulled-back scalar comparison in
the cube identity: the other boundary consists of the integral exchange
isomorphism, the scalar comparison on the new base, and the scalar/pullback
compositors. All these are isomorphisms on the specified shifted lines.
Cancel these isomorphisms in the pasted trace equality. This gives both
conjuncts of each TracePullback. No diagonal class equation, integration
identity, flatness of the quotient, or regularity of pi is needed. In particular
the argument applies at n = 0, at ramified levels, and even to an arbitrary pi
when the two scalar compatibilities are supplied. -/
theorem diagonalQuotient_tracePullback
    (l : ℕ) [Fact l.Prime] {Y Y' : Scheme.{u}} (g : Y' ⟶ Y)
    [IsNoetherian Y] [IsNoetherian Y']
    (E : PadicAlgCl.FiniteIntermediateField l)
    (π : PadicAlgCl.integers l E) (n : ℕ)
    (d₀ : Diagram (Profinite.padicIntegersRingObj.{u} l E.1) Y
      (fun X ↦ spIntegralTwist X l E))
    (d₀' : Diagram (Profinite.padicIntegersRingObj.{u} l E.1) Y'
      (fun X ↦ spIntegralTwist X l E))
    (integral : PullbackCompatibility (Profinite.padicIntegersRingObj.{u} l E.1) g
      (fun X ↦ spIntegralTwist X l E) d₀ d₀'
      (spIntegralComparison (baseP g) l E) (spIntegralComparison (baseW g) l E))
    (d : Diagram (Profinite.continuousMapRingObj.{u} (completedResidue l E π n))
      Y (quotientLine l E π n))
    (d' : Diagram (Profinite.continuousMapRingObj.{u} (completedResidue l E π n))
      Y' (quotientLine l E π n))
    (scalar : ScalarCompatibility (quotientMap l E π n) Y
      (fun X ↦ spIntegralTwist X l E) (quotientLine l E π n)
      (quotientLineMap l E π n) d₀ d)
    (scalar' : ScalarCompatibility (quotientMap l E π n) Y'
      (fun X ↦ spIntegralTwist X l E) (quotientLine l E π n)
      (quotientLineMap l E π n) d₀' d')
    (mP : (upperStar Ab.{u + 1} (baseP g)).obj
      (quotientLine l E π n (ProjectiveLine Y)).X ⟶
        (quotientLine l E π n (ProjectiveLine Y')).X)
    (mW : (upperStar Ab.{u + 1} (baseW g)).obj
      (quotientLine l E π n (diagonalSurface Y)).X ⟶
        (quotientLine l E π n (diagonalSurface Y')).X)
    (_hP : QuotientPullMap l E π n (baseP g) mP)
    (_hW : QuotientPullMap l E π n (baseW g) mW)
    (s : SourcePullback
      (Profinite.continuousMapRingObj.{u} (completedResidue l E π n)) g
      (quotientLine l E π n) mP mW) :
    TracePullbackSquares
      (Profinite.continuousMapRingObj.{u} (completedResidue l E π n)) g
      (quotientLine l E π n) d d' mP mW s := by sorry

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
