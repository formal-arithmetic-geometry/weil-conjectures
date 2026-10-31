/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IdentityCoefficientTransportData

/-! # Completed and scalar identity composition normalization

The completed left-adjoint calculation and its coefficient transport, before
conjugating any adjunction or specializing to a duality unit.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme Opposite
namespace WeilConjectures

/-- Identity composition and the canonical coefficient-change squares, without any
assertion about exceptional adjoints or their counits.
Source: steps 1--4 of lem-sf-identification-coefficient-transport; the explicit
semilinear comparison formula of lem-sf-integral-compactification-comparison-bridge
(blueprint: lem-sf-higher-identity-composition-normalization).

Proof: at the point the identity-open reduction theorem identifies completed
identity support with L R and gives the invertible reconstruction unit u. Its
inverse is a natural identity comparison vI, normalized by the actual Roos
projections. Write a = p j and use the direct strict-tower identification
C : L N ≅ Ra_! K. The comparison bridge for outer identity expresses the specified
compositor as C L(e_N) L R(C inverse): the ambient proper/open identity-pasting law
makes the system comparison the identity. Naturality of u followed by the
adjunction triangle L(e_N) u_(L N) = 1 gives alpha u = 1 and hence alpha = u inverse.
For arbitrary bounded constructible integral inputs, choose a common finite
cohomological interval and use the finite Tor bounds over the coefficient DVR;
the realization and compatible-origin hypotheses follow from the datum's
specified reduction tower and its projection comparisons. Those same projection
comparisons give each displayed reduction square for vI.
Apply raw scalar localization to vI and its inverse; the datum's rational operation
comparisons identify the resulting natural isomorphism with a vR for the rational
identity support. On a fraction, naturality is naturality on its numerator divided
by the same scalar denominator. Composition compatibility transports alpha = vI F
to alpha = vR F, and gives the displayed rationalization square. Repeat this
construction at every finite coefficient field in the closure. For common-stage
coefficients choose representatives for objects and arrows over one common finite
field; the datum's transition and composition comparisons carry the rational
identity equality to their classes. Enlarging that field preserves the equality
and both inverse identities, so this defines a natural vQ independent of the
representative. The same class calculation gives every common-stage comparison
square, while the previously constructed integral and rational comparisons give
all finite-field reduction squares. Zero objects and identity compactifications
use the same unit and triangle equations. -/
theorem higherIdentityCompositionNormalization
    (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] (n : ℕ) (hn : 1 ≤ n)
    (S : SixFunctorDatum D C E n hn) :
    (∃ vI : S.higher.integral.support (𝟙 (sixFunctorPoint D))
        (sfPointIdentityCompactification D) ≅ 𝟭 _,
      SfIdentityCompositionLaw.{u, u+2, u+2} S.higher.integral vI ∧
    ∃ vR : S.higher.rational.support (𝟙 (sixFunctorPoint D))
        (sfPointIdentityCompactification D) ≅ 𝟭 _,
      SfIdentityCompositionLaw.{u, u+2, u+2} S.higher.rational vR ∧
      SfIdentityChange S.higher.rationalization vI vR ∧
      (∀ m : ℕ, @SfIdentityChange.{u, u+2, u+2, u+2, u+2} D
        (fun X ↦ sfIntegralConstructibleCategory C.l E X.obj.left)
        (fun X ↦ inferInstanceAs (Category.{u+2}
          (sfIntegralConstructibleCategory C.l E X.obj.left)))
        (sixFunctorFiniteCategory D C E (m+1) (Nat.succ_le_succ (Nat.zero_le m)))
        (fun X ↦ inferInstanceAs (Category.{u+2}
          (sixFunctorFiniteCategory D C E (m+1) (Nat.succ_le_succ (Nat.zero_le m)) X)))
        _ _ _ (S.integralNormalization.reduction m) vI
        (sfFiniteIdentityComparison D C E (m+1) (Nat.succ_le_succ (Nat.zero_le m))
          (S.integralNormalization.finiteLevels m))) ∧
    ∃ vQ : S.closure.commonStage.support (𝟙 (sixFunctorPoint D))
        (sfPointIdentityCompactification D) ≅ 𝟭 _,
      SfIdentityCompositionLaw.{u, u+2, u+2} S.closure.commonStage vQ ∧
    ∀ L : Padic.FiniteCoefficientFields C.l C.Qbar,
      ∃ vLI : (S.closure.coefficientStages L).integral.support
          (𝟙 (sixFunctorPoint D)) (sfPointIdentityCompactification D) ≅ 𝟭 _,
      ∃ vLR : (S.closure.coefficientStages L).rational.support
          (𝟙 (sixFunctorPoint D)) (sfPointIdentityCompactification D) ≅ 𝟭 _,
      SfIdentityCompositionLaw.{u, u+2, u+2} (S.closure.coefficientStages L).integral vLI ∧
      SfIdentityCompositionLaw.{u, u+2, u+2} (S.closure.coefficientStages L).rational vLR ∧
      SfIdentityChange (S.closure.coefficientStages L).rationalization vLI vLR ∧
      SfIdentityChange (S.closure.commonStageComparison L) vLR vQ ∧
      ∀ m : ℕ, @SfIdentityChange.{u, u+2, u+2, u+2, u+2} D
        (fun X ↦ sfIntegralConstructibleCategory C.l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} C.l C.Qbar L) X.obj.left)
        (fun X ↦ inferInstanceAs (Category.{u+2} (sfIntegralConstructibleCategory C.l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} C.l C.Qbar L) X.obj.left)))
        (sixFunctorFiniteCategory D C
          (AlgebraicallyClosedCoefficients.Coefficient.{u} C.l C.Qbar L)
          (m+1) (Nat.succ_le_succ (Nat.zero_le m)))
        (fun X ↦ inferInstanceAs (Category.{u+2} (sixFunctorFiniteCategory D C
          (AlgebraicallyClosedCoefficients.Coefficient.{u} C.l C.Qbar L)
          (m+1) (Nat.succ_le_succ (Nat.zero_le m)) X)))
        _ _ _ ((S.coefficientIntegralNormalization L).reduction m) vLI
        (sfFiniteIdentityComparison D C
          (AlgebraicallyClosedCoefficients.Coefficient.{u} C.l C.Qbar L)
          (m+1) (Nat.succ_le_succ (Nat.zero_le m))
          ((S.coefficientIntegralNormalization L).finiteLevels m))) := by
  sorry

end WeilConjectures
