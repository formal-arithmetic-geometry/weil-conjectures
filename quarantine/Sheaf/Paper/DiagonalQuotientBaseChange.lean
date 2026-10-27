/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U4
-/
module

public import Sheaf.Paper.DiagonalCoefficientFamilyPullback
import Sheaf.Paper.DiagonalQuotientSourcePullback
import Sheaf.Paper.DiagonalQuotientClassPullback
import Sheaf.Paper.DiagonalQuotientTracePullback

/-! # Pullback of scalar-compatible quotient diagrams

Source: coefficient changes, paragraph (3c), final coefficient comparison.
(blueprint: lem-diagonal-quotient-base-change).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

/-- Pullback of an arbitrary quotient diagram is forced by its integral scalar
square and the integral diagram's pullback comparison. The tensor formula fixes
the maps also at ramified levels outside the ell-power cofinal subsystem.

Source: blueprint latest, sec-six-functors-basics/sk-prop-diagonal-tower/
sk-prop-diagonal-tower-coefficients.proof.md, paragraph (3c), final coefficient
comparison. (blueprint: lem-diagonal-quotient-base-change).

Proof: Tensor the integral root comparison with the quotient coefficient map.
The extension unit coequalizes the two balancing maps; the tensor universal
property gives the maps mP and mW and exactly the QuotientPullMap equations.
Integral root limits are torsion-free over O_E: a uniformizer-torsion
compatible root tuple is zero, by shifting its projections. Hence these lines
are flat, so derived quotient extension has these ordinary endpoints. The
closed supported source has the same property by closed-support scalar
comparison. Paste the integral pullback square with
the two given scalar squares. Functoriality of the scalar/pullback compositor
and its adjunction-unit normalization identify the pasted class square with
the required quotient class square. Uniqueness of mates and compatibility of
coefficient extension with geometric pullback identify the three pasted trace
squares with modelExchange. The quotient has a two-term regular-element
resolution over O_E. Tensoring its triangle and using the derived direct image
shows
that the scalar/direct-image comparisons on these lines are invertible. Pasting
with the integral base-change comparison proves invertibility of the quotient
base-change mate on each shifted line. This uses only the integral pullback
comparison and the two specified scalar
compatibilities; no completed reference or choice of a Cartier arrow is needed. -/
theorem diagonalCoefficient_quotientBaseChange
    (l : ℕ) [Fact l.Prime] {Y Y' : Scheme.{u}} (g : Y' ⟶ Y)
    [IsNoetherian Y] [IsNoetherian Y']
    (family : Family l Y) (family' : Family l Y')
    (E : PadicAlgCl.FiniteIntermediateField l)
    (integral : PullbackCompatibility (Profinite.padicIntegersRingObj.{u} l E.1) g
      (fun X ↦ spIntegralTwist X l E) (family.integral E) (family'.integral E)
      (spIntegralComparison (baseP g) l E) (spIntegralComparison (baseW g) l E))
    (π : PadicAlgCl.integers l E)
    (_hπ : Ideal.span {π} = IsLocalRing.maximalIdeal (PadicAlgCl.integers l E)) (n : ℕ)
    (d : Diagram (Profinite.continuousMapRingObj.{u} (completedResidue l E π n))
      Y (quotientLine l E π n))
    (d' : Diagram (Profinite.continuousMapRingObj.{u} (completedResidue l E π n))
      Y' (quotientLine l E π n)) :
    ScalarCompatibility (quotientMap l E π n) Y
      (fun X ↦ spIntegralTwist X l E) (quotientLine l E π n)
      (quotientLineMap l E π n) (family.integral E) d →
    ScalarCompatibility (quotientMap l E π n) Y'
      (fun X ↦ spIntegralTwist X l E) (quotientLine l E π n)
      (quotientLineMap l E π n) (family'.integral E) d' →
    ∃ (mP : (upperStar Ab.{u + 1} (baseP g)).obj
        (quotientLine l E π n (ProjectiveLine Y)).X ⟶
          (quotientLine l E π n (ProjectiveLine Y')).X)
      (mW : (upperStar Ab.{u + 1} (baseW g)).obj
        (quotientLine l E π n (diagonalSurface Y)).X ⟶
          (quotientLine l E π n (diagonalSurface Y')).X),
      QuotientPullMap l E π n (baseP g) mP ∧ QuotientPullMap l E π n (baseW g) mW ∧
        Nonempty (PullbackCompatibility
          (Profinite.continuousMapRingObj.{u} (completedResidue l E π n)) g
          (quotientLine l E π n) d d' mP mW) := by
  intro scalar scalar'
  obtain ⟨mP, mW, hP, hW, ⟨s⟩⟩ :=
    diagonalQuotient_sourcePullback l g E π n integral.sourceData
  have hdelta := diagonalQuotient_classPullback l g E π n
    (family.integral E) (family'.integral E) integral d d' scalar scalar' mP mW hP hW s
  have htrace := diagonalQuotient_tracePullback l g E π n
    (family.integral E) (family'.integral E) integral d d' scalar scalar' mP mW hP hW s
  exact ⟨mP, mW, hP, hW, ⟨{
    sourceData := s
    delta := hdelta.comm
    traceq := htrace.q
    trace₁ := htrace.p₁
    trace₂ := htrace.p₂ }⟩⟩

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
