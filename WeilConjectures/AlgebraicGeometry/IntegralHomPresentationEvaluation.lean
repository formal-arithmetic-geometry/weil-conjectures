/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteCoefficientHomChange
public import WeilConjectures.AlgebraicGeometry.IntegralHomReductionModels

/-! # Joint normalized integral Hom presentations

Source: current blueprint, fix-prop-coherence.proof.md, evaluation sentence;
lem-sf-general-hom-comparison-cocycles, proof step 4.
(blueprint: lem-sf-integral-hom-presentation-evaluation).
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u})

/-- The integral presentation's transpose uncurries to the fixed reduced evaluation.
Only this normalization is asserted; invertibility is a separate existing theorem.

Source: current blueprint fix-prop-coherence.proof.md, general Hom sentence;
lem-sf-general-hom-comparison-cocycles, step 4; Stacks 07A4, 08J9, 06YY.
(blueprint: lem-sf-integral-hom-presentation-evaluation).

Proof:
1. Use the fixed natural tensor-Hom adjunction of scalarIntegralClosed on the entire
ambient derived category. Transport its tensor by Koszul symmetry to the order
K tensor Hom(K,M) of IntegralHom.TensorPresentation. Use the transported adjunction
on every ambient input; choosing only its restrictions on K-flat pairs would not
specify the adjunction on a non-K-flat input.
2. The fixed total-tensor and Hom-complex models identify this transported counit
with signed sectionwise evaluation. They supply TensorPresentation.representative
and its evaluation field, with the same source presentation for every exponent.
3. Over each finite quotient repeat this construction from finiteIntrinsicClosed.
Use the fixed finiteTensor comparison, conjugated by its preserved Koszul symmetry,
as the reduction presentation's mu. Its pure-tensor equation is the normalized
ordinary scalar unit followed by multiplication of the coefficient factors. The
fixed derived counit square supplies ReductionPresentation.normalization.
4. Uncurry IntegralHom.comparison in the original Hom tensor K convention. Its
definition, the two transported adjunctions and the same symmetry identify it
with finiteTensor inverse followed by reduction of the original evaluation.
This equality holds on all ambient inputs by the chosen adjunctions, not by an
inference of arbitrary-adjunction equality from K-flat normalizations. The argument
includes unbounded inputs, n=0, zero inputs and identity quotient cases. -/
theorem integralHom_presentation_evaluation (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p) :
    ∃ a : IntegralHom.TensorPresentation.{u, u} X
        (completedIntegralCommRingSheaf l E X D hl),
      ∀ n : ℕ, ∃ m : IntegralHom.ReductionPresentation l E X D hl a n,
        ∀ K M : completedIntegralDerivedCategory l E X D hl,
          ((finiteIntrinsicClosed l E X n).transpose _
            ((coefficientFiniteDerivedExtension l E X n).obj K)
            ((coefficientFiniteDerivedExtension l E X n).obj M)).symm
              (IntegralHom.comparison l E X D hl m K M) =
            ((coefficientDerivedSystemEvaluationCalculus l E X).choose.finiteTensor n).inv.app
                ((coefficientIntegralInternalHom l E X).obj (op K, M), K) ≫
              (coefficientFiniteDerivedExtension l E X n).map
                ((scalarIntegralClosed l E X).evaluation K M) := by sorry

end WeilConjectures
