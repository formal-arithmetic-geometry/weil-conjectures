/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N2
-/
module

public import Sheaf.Paper.IntegralPullbackComposition
public import Sheaf.Paper.IntegralPullbackComparisonRealization

/-! # Finite reductions of the whole-system completed pullback compositor

Source: latest blueprint lem-fix-weil-operations.proof.md, first paragraph.
(blueprint: lem-pod-integral-comparison-composition-reduction). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

/-- The counit-normalized completed compositor has the prescribed finite reductions.
Source: Stacks 099N(5), 0D6D and 0941; latest blueprint
lem-fix-weil-operations.proof.md, first paragraph, composition of pullbacks
(blueprint: lem-pod-integral-comparison-composition-reduction).

Proof: choose one flat-term K-flat representative of K and a simultaneous strict
presentation of its quotient reduction diagram. The normalization of S.pullback
identifies its realization map with the defining Roos pullback comparison on this
presentation. Its adjoint is therefore the actual reduction comparison, whose
finite evaluation is integralPullbackReductionIso; this holds for every allowed
representative by naturality of the localization comparison. Substitute these
counit maps in integralComparisonEta and integralComparisonComposition. The
adjunction triangle cancels the reconstruction unit and counit on the whole
system. Thus the realized compositor reduces to the derived system compositor.
Evaluate at n: the generator-normalized system compositor is the published
finite pullback compositor, and both single-pullback counits evaluate to the
specified rho maps. This gives the displayed equation. The argument proves an
equality before evaluation and does not require faithfulness of finite reductions. -/
theorem integralComparisonComposition_reduction
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (S : IntegralComparisonSystem.{u} l) :
    ∀ {V W Z : Scheme.{u}}
        [∀ v : V, Invertible (l : V.residueField v)]
        [∀ w : W, Invertible (l : W.residueField w)]
        [∀ z : Z, Invertible (l : Z.residueField z)]
        (h : Z ⟶ W) (k : W ⟶ V) (K : sfIntegralConstructibleCategory l E V)
        (P : (integralOperationsGoodComplex l E V).FullSubcategory)
        (e : DerivedCategory.Q.obj P.obj ≅ K.obj)
        (Q : (integralOperationsGoodComplex l E W).FullSubcategory)
        (d : DerivedCategory.Q.obj Q.obj ≅ ((constructibleIntegralPullback l E k).obj K).obj)
        (n : ℕ),
        (scalarReductionDerivedExtension l E Z n).map
            (integralComparisonComposition l E S h k K).hom ≫
            (integralPullbackReductionIso l E h
              ((constructibleIntegralPullback l E k).obj K) Q d n).hom ≫
            (proEtaleConstantRingDerivedPullback
              (Padic.coefficientExtensionRing l E (n + 1)) h).map
                (integralPullbackReductionIso l E k K P e n).hom =
          (integralPullbackReductionIso l E (h ≫ k) K P e n).hom ≫
            (integralFiniteCanonicalPullbackComposition l E h k n).hom.app
              ((scalarReductionDerivedExtension l E V n).obj K.obj) := by
  sorry

end WeilConjectures
