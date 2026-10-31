/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.CoefTowerEvaluationPairingData

/-! # Descent of a supplied pairing frame to finite coefficients

Source: prop-coef-integral-dualizing, second proof paragraph; Stacks 07A6 and 0941.
(blueprint: lem-coef-pairing-finite-frame-descent).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- Descend the supplied proper tensor isomorphism, together with its adjunction,
to one ambient finite frame. The tensor evaluation isomorphisms are supplied
explicitly. No sections-left evaluation or projection mate occurs in the conclusion.

Source: prop-coef-integral-dualizing, paragraph 2; Stacks 07A6, 0B56 and 0941.
(blueprint: lem-coef-pairing-finite-frame-descent).

Proof: use fully faithful quotient-scalar restriction to identify the ordinary
proper functor with the native varying-ring direct image. Its derived comparison,
the native evaluation square and adjoint uniqueness give the finite proper
pullback and the two adjoint comparisons. The mate formula gives the displayed
unit and counit identities. Construct the other finite-frame adjunctions from the
actual open restriction and constant sheaf functors after derived extension from
the completed scalar ring to the quotient. Their strong tensor comparisons come
from the supplied finite K-flat tensor models. Open extension has its sheafified
extension-by-zero tensor isomorphism, whose adjunct is the tensor of the open unit;
composition of constant inverse images gives the source adjunction.
To construct the proper tensor use evaluation as a localization: its exact
coinduction has restriction of quotient scalars above q and zero below q, and its
counit is the identity at q. Consequently precomposition with evaluation, also on
the product category, is fully faithful on functor categories. Conjugate evaluation
of the supplied properTensor by the two tensor comparisons and the pullback
comparison. This is an isomorphism between functors factoring through evaluation
in both variables. Full faithfulness descends it to the required finite strong
tensor isomorphism, and the factorization identity is precisely the last square.
This step descends the supplied isomorphism; it does not identify an arbitrary
supplied isomorphism with the canonical one. All constructions are uniform in the
two inputs, including zero objects and q = 0. -/
theorem coefPairing_finite_frame_descent
    {X Y : Scheme.{u}} {a : X ⟶ Y} (c : Compactification a)
    (S : CoefficientDerivedSystemCalculus l E X) (G : CoefPairingSystem l E c S)
    (q : ℕ)
    (σ : G.baseTensors.systemClosed.tensor ⋙ coefficientSequenceDerivedEvaluation l E Y q ≅
      (coefficientSequenceDerivedEvaluation l E Y q).prod
        (coefficientSequenceDerivedEvaluation l E Y q) ⋙ (G.baseTensors.finiteClosed q).tensor)
    (τ : G.compactTensors.systemClosed.tensor ⋙
        coefficientSequenceDerivedEvaluation l E c.Z q ≅
      (coefficientSequenceDerivedEvaluation l E c.Z q).prod
        (coefficientSequenceDerivedEvaluation l E c.Z q) ⋙
          (G.compactTensors.finiteClosed q).tensor) :
    ∃ (F : CoefPairingFiniteFrame l E c S G q)
      (e : G.frame.pstar ⋙ coefficientSequenceDerivedEvaluation l E c.Z q ≅
        coefficientSequenceDerivedEvaluation l E Y q ⋙ F.pstar)
      (r : G.properModules.rightDerivedFunctor ⋙ coefficientSequenceDerivedEvaluation l E Y q ≅
        coefficientSequenceDerivedEvaluation l E c.Z q ⋙
          proEtaleConstantDerivedDirectImage c.g
            (Padic.coefficientExtensionRing l E (q + 1))),
      (∀ H, (coefficientSequenceDerivedEvaluation l E Y q).map
          (G.frame.properAdjunction.unit.app H) ≫ r.hom.app (G.frame.pstar.obj H) ≫
        (proEtaleConstantDerivedDirectImage c.g
          (Padic.coefficientExtensionRing l E (q + 1))).map (e.hom.app H) =
        F.properAdjunction.unit.app ((coefficientSequenceDerivedEvaluation l E Y q).obj H)) ∧
      (∀ M, e.hom.app (G.properModules.rightDerivedFunctor.obj M) ≫
        F.pstar.map (r.hom.app M) ≫ F.properAdjunction.counit.app
          ((coefficientSequenceDerivedEvaluation l E c.Z q).obj M) =
        (coefficientSequenceDerivedEvaluation l E c.Z q).map
          (G.frame.properAdjunction.counit.app M)) ∧
      (∀ H K, (coefficientSequenceDerivedEvaluation l E c.Z q).map
          (G.frame.properTensor.hom.app (H, K)) ≫
        τ.hom.app (G.frame.pstar.obj H, G.frame.pstar.obj K) ≫
        (G.compactTensors.finiteClosed q).tensor.map
          (Prod.mkHom (e.hom.app H) (e.hom.app K)) =
        e.hom.app (G.baseTensors.systemClosed.tensor.obj (H, K)) ≫
          F.pstar.map (σ.hom.app (H, K)) ≫ F.properTensor.hom.app
            ((coefficientSequenceDerivedEvaluation l E Y q).obj H,
              (coefficientSequenceDerivedEvaluation l E Y q).obj K)) := by sorry

end WeilConjectures
