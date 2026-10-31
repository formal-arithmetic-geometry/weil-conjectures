/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.CoefTowerEvaluationPairingData
public import WeilConjectures.SixFunctors.CoefPairingFiniteNormalization

/-! # Comparison of native projection words with compactification frames

Source: blueprint prop-coef-integral-dualizing, proof paragraph 2,
compact-support and finite projection word
(blueprint: lem-coef-pairing-native-frame-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
attribute [local instance 1] WeilConjectures.coefHomFinitePointHasDerived
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
variable (D : FiniteFieldDatum.{u}) (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]

/-- Compare the two already specified projection words, before using the finite
normalization theorem. The first equation compares the system word with the native
system word; the second compares their finite words. Neither asserts that finite
evaluation of the system word equals the finite word.

Source: blueprint prop-coef-integral-dualizing, proof paragraph 2, compact-support
realization and the comparison of adjunction mates; Stacks 07A6, 0B56 and 0941.
(blueprint: lem-coef-pairing-native-frame-comparison).

Proof: first use uniqueness of localization to compare the standard derived
category at the integral point with its Grothendieck-small model; V is the
canonical equivalence induced by their localization functors. Identify the native
scalar specialization with the coherent reduction
calculus using uniqueness of left adjoints to the fixed total-limit functor. Its
unit equations identify the finite reductions and their actual quotient maps.
Transport the native system adjunctions across the normalized point-sections and
scalar-restriction comparisons. Compose the point and scalar adjunctions to obtain
the sections adjunction of G; pullback composition gives its source adjunction.
Transport the canonical strong pullback tensor comparisons and the sheafified open
chain comparison. The open adjunct equation is preserved by this transport. The
ordinary open and proper scalar squares, exact restriction and separately derived
proper image give G.compactSections. Repeat this construction on each finite slice
to obtain F. Tensor localization compares the two integral point tensors, and exact
point evaluation gives evaluationTensor. The full-system scalar-Hom comparison,
its finite Hom transpose and the finite sections comparison give eH. The actual
compact-support point square gives eB and eQcompact. Its quotient naturality gives
hB, including equal levels. The same point tensor and Hom/support comparisons give
a; the finite sections and intrinsic-support comparisons give c. Expand G.beta and
ScalarSpecialization.transported. Move comparison maps past each projection mate
using their unit/counit equations; the adjacent inverse pairs cancel. This proves
the first equation. Apply exactly the same mate transport at the finite point,
including scalar balancing and the signed symmetry, to prove the second equation.
These are comparisons of words on each presentation separately: no finite
normalization equation or dualizing-object identification is used. -/
theorem coefPairingNativeFrameComparison
    (m : CoefProjectionEvaluation.Model l E (finiteDualizingCompactification D X))
    (s : CoefProjectionEvaluation.ScalarSpecialization l E m)
    (e : ∀ n : ℕ, CoefProjectionEvaluation.FiniteEvaluation l E m s n)
    (Q : CochainComplex (coefficientSequenceModules.{u, u} l E X) ℤ) :
    ∃ (V : @DerivedCategory (ModuleCat.{u + 1} (coefTraceRing l E)) _ _
        (HasDerivedCategory.standard _) ≌
      DerivedCategory (ModuleCat.{u + 1} (coefTraceRing l E)))
      (S : CoefficientDerivedSystemCalculus l E X)
      (G : CoefPairingSystem l E (finiteDualizingCompactification D X) S)
      (F : ∀ n : ℕ,
        CoefPairingFiniteFrame l E (finiteDualizingCompactification D X) S G n)
      (evaluationTensor : ∀ n : ℕ,
        coefPairingTensor l E ⋙ coefTraceEvaluation l E n ≅
          (coefTraceEvaluation l E n).prod (coefTraceEvaluation l E n) ⋙
            MonoidalCategory.tensor
              (DerivedCategory (ModuleCat.{u + 1} (coefTraceRing l E))))
      (eH : ∀ n : ℕ,
        coefPairingHom l E X S Q ⋙ coefTraceEvaluation l E n ≅
          coefPairingFiniteHom l E X n ((coefficientSequenceDerivedEvaluation.{u, u} l E X n).obj
            (coefTraceInput l E X Q)))
      (eB : ∀ n : ℕ,
        coefPairingSupport l E D X S ⋙ coefTraceEvaluation l E n ≅
          coefPairingFiniteC l E D X n)
      (eQcompact : ∀ n : ℕ,
        (coefTraceEvaluation l E n).obj (coefTraceDualizingTower l E D X Q) ≅
          (coefPairingFiniteSupport l E (finiteDualizingCompactification D X) n).obj
            ((coefficientSequenceDerivedEvaluation.{u, u} l E X n).obj
            (coefTraceInput l E X Q)))
      (a : ∀ (K : DerivedCategory (scalarReductionSource.{u, u} l E X)) (n : ℕ),
        (coefTraceEvaluation l E n).obj
          ((coefPairingTensor l E).obj
            ((coefPairingHom l E X S Q).obj (op K),
              (coefPairingSupport l E D X S).obj K)) ≅
        V.functor.obj ((coefHomPointEvaluation l E n).obj (m.point.rTensor.obj
          ((coefHomTower l E X).obj (op K, coefTraceInput l E X Q), s.supportTower K))))
      (c : ∀ n : ℕ,
        V.functor.obj ((CoefProjectionEvaluation.finiteDerivedRestriction l E n).obj
          ((e n).finite.b
            ((coefficientSequenceDerivedEvaluation.{u, u} l E X n).obj
              (coefTraceInput l E X Q)))) ≅
        (coefPairingFiniteSupport l E (finiteDualizingCompactification D X) n).obj
          ((coefficientSequenceDerivedEvaluation.{u, u} l E X n).obj
            (coefTraceInput l E X Q))),
      (∀ (K : DerivedCategory (scalarReductionSource.{u, u} l E X))
        {m n : ℕ} (h : n ≤ m),
        (coefTraceTransition l E h).app ((coefPairingSupport l E D X S).obj K) ≫
          (eB n).hom.app K =
        (eB m).hom.app K ≫
          (coefPairingIntegralSections l E (Spec (.of D.k))).map
            (compactSupportRestrictedTransition l E (finiteDualizingCompactification D X)
              m n h K)) ∧
      (∀ (K : DerivedCategory (scalarReductionSource.{u, u} l E X)) (n : ℕ),
        (coefTraceEvaluation l E n).map
            (G.beta l E (S.reduction.obj K) (coefTraceInput l E X Q)) ≫
          (eQcompact n).hom =
        (a K n).hom ≫ V.functor.map ((coefHomPointEvaluation l E n).map
            (s.transported K (coefTraceInput l E X Q)) ≫
          ((e n).support (coefTraceInput l E X Q)).hom) ≫ (c n).hom) ∧
      (∀ (K : DerivedCategory (scalarReductionSource.{u, u} l E X)) (n : ℕ),
        (evaluationTensor n).hom.app
            ((coefPairingHom l E X S Q).obj (op K), (coefPairingSupport l E D X S).obj K) ≫
          ((eH n).hom.app (op K) ⊗ₘ (eB n).hom.app K) ≫
            coefPairingFiniteBeta l E (finiteDualizingCompactification D X) S G n (F n)
              ((scalarReductionDerivedExtension l E X n).obj K)
              ((coefficientSequenceDerivedEvaluation.{u, u} l E X n).obj
                (coefTraceInput l E X Q)) =
        (a K n).hom ≫ V.functor.map ((letI := coefHomFinitePointHasDerived.{u, u} l E
          (e n).integral.derived).hom.app
            ((coefHomTower l E X).obj (op K, coefTraceInput l E X Q), s.supportTower K) ≫
          (e n).finite.integralTensor.map
            (Prod.mkHom ((e n).homComparison K (coefTraceInput l E X Q)).hom
              ((e n).reducedSupport K).hom) ≫
          (e n).finite.beta ((coefficientFiniteDerivedExtension l E X n).obj K)
            ((coefficientSequenceDerivedEvaluation.{u, u} l E X n).obj
              (coefTraceInput l E X Q))) ≫ (c n).hom) := by sorry

end WeilConjectures
