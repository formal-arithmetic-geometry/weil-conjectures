/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Y3
-/
module

public import Sheaf.Paper.DiagonalCoefficientFamilyPullback
public import Sheaf.Paper.DiagonalPullbackSquares

/-! # Scalar transport of the diagonal class square

Source: diagonal tower coefficient changes, paragraph (3), scalar base change.
(blueprint: lem-diagonal-quotient-class-pullback).
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

/-- The diagonal class square after quotient reduction, with ordinary source
and line maps supplied separately. This asserts no trace equation or exchange
isomorphism.

Source: latest blueprint, sec-six-functors-basics/sk-prop-diagonal-tower/
sk-prop-diagonal-tower-coefficients.proof.md, paragraph (3), naturality of the
class under the coefficient functors; original quotient-base-change proof, step 2.
(blueprint: lem-diagonal-quotient-class-pullback).

Proof: Apply derived quotient extension to integral.delta. The scalar/inverse-image
compositor identifies the two ways to pull back the extended integral line. Its
single-complex and shift normalizations identify this compositor with the supplied
quotient PullEndpoint: precomposition with the pulled-back extendπ gives
QuotientPullMap, and that map is epic. On the supported source the same identity
follows from the coefficient-unit normalization and supported_normalization:
both adjoints are obtained by the same coefficient unit and diagonal counit.
Paste the resulting square with scalar.delta and scalar'.delta. The two
Endpoint.normalization equations fix the derived scalar endpoints uniquely
through the scalar adjunction, so these are the specified endpoints, without any
rescaling. Cancel the supported scalar isomorphism and the scalar/pullback
compositor. The remaining boundary is exactly the displayed quotient class
square. No trace equation or property of a particular Cartier class is used.
This reasoning also applies to n = 0, ramified levels, and the zero quotient. -/
theorem diagonalQuotient_classPullback
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
    ClassPullbackSquare
      (Profinite.continuousMapRingObj.{u} (completedResidue l E π n)) g
      (quotientLine l E π n) d d' mP mW s := by sorry

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
