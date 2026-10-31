/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.CoefTowerEvaluationPairingData
import WeilConjectures.SixFunctors.CoefPairingFrameNaturality
import WeilConjectures.SixFunctors.CoefPairingHomRepresentativeComparison
import WeilConjectures.SixFunctors.CoefPairingCompactificationModels

/-! # Tower evaluation pairing: assembly of its normalized models. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
variable (D : FiniteFieldDatum.{u}) (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]

/-- Simultaneous existence, finite evaluation and dinaturality of the tower evaluation
pairing. All implementation witnesses are conclusions, not additional assumptions.

Source: blueprint prop-coef-integral-dualizing, proof paragraph 2, expanded node proof
steps 1--10 (blueprint: lem-coef-tower-evaluation-pairing).

Proof:
1. Use the quotient sequence sites and the same separately derived compact-support
composite as coefTowerTraceRectification. Restriction is exact on underlying sheaves.
2. Resolve K by a flat-term K-flat P, and Res Q by a simultaneous K-injective tower I.
Hom(const P,I) is K-injective; its slices are Hom(P,I_n). Evaluation preserves
K-injectives for constant-ring towers. Scalar adjunction therefore identifies the
resulting R-linear Hom tower with coefPairingHom, including its contravariant maps.
3. Closed tensor transposition and the scalar adjunction identify the full system
Hom, not merely its evaluated objects. The comparison carries evaluation counits.
4. The strict quotient system P tensor A_n computes S.reduction. Exact open extension,
separately derived proper image and sections identify its compact support with the
specified reduction tower, naturally for all quotient maps.
5. Construct the open tensor comparison on module complexes, by the local formula
m tensor l maps to m tensor l restricted to X. The same formula commutes with every
quotient restriction. A K-flat replacement of l gives the derived open comparison.
6. Use pullback composition and the source-sections counit, followed by the recorded
closed evaluation, to obtain the system evaluation morphism.
7. Apply the counit-defined proper projection mate and the open tensor comparison.
8. Apply the sections projection mate with the scalar restriction included in its
left adjoint. This is exactly scalar balancing followed by the system pairing.
This yields G.beta in the derived category of strict R-module towers, with target
coefTraceDualizingTower. No invertibility of a projection mate has been used.
9. Evaluate normalized resolution models. Direct-image composition, coefficient
restriction and evaluation tensor comparisons carry units, counits and the open
chain map to their finite counterparts. Hence the evaluated map is precisely
coefPairingFiniteBeta: balancing, ambient compact-support projection, evaluation.
The same comparisons give eH, eB and eQcompact; the supplied eQ identifies Q_n with
omega_n, with its actual counit-defined transitions. No inverse limit or trace is used.
10. For f:K to K', naturality of closed evaluation and the source counit gives the
identity before compact support. Naturality of both projection mates and of the
open tensor comparison carries it to the displayed dinaturality in the derived
tower category. This does not invoke fullness of finite evaluation. -/
theorem coefTowerEvaluationPairing (hl : l ≠ D.p)
    (Q : CochainComplex (coefficientSequenceModules.{u, u} l E X) ℤ)
    (eQ : ∀ n : ℕ,
      (coefficientSequenceDerivedEvaluation.{u, u} l E X n).obj (coefTraceInput l E X Q) ≅
        integralDualizingFiniteTerm l E D X n)
    (_hQ : ∀ {m n : ℕ} (h : n ≤ m),
      (coefficientSequenceDerivedTransition.{u, u} l E X h).app (coefTraceInput l E X Q) ≫
          (normalizedDVRRes.{u, u} l E X h).map (eQ n).hom =
        (eQ m).hom ≫ integralDualizingExceptionalTransition l E D X hl h) :
    ∃ (S : CoefficientDerivedSystemCalculus l E X)
      (G : CoefPairingSystem l E (finiteDualizingCompactification D X) S)
      (F : ∀ n : ℕ,
        CoefPairingFiniteFrame l E (finiteDualizingCompactification D X) S G n)
      (evaluationTensor : ∀ n : ℕ,
        coefPairingTensor l E ⋙ coefTraceEvaluation l E n ≅
          (coefTraceEvaluation l E n).prod (coefTraceEvaluation l E n) ⋙
            MonoidalCategory.tensor
              (DerivedCategory (ModuleCat.{u + 1} (coefTraceRing l E))))
      (eIntegralHom : ∀ n : ℕ,
        coefPairingHom l E X S Q ⋙ coefTraceEvaluation l E n ≅
          coefPairingIntegralHom l E X n (integralDualizingFiniteTerm l E D X n))
      (eH : ∀ n : ℕ,
        coefPairingHom l E X S Q ⋙ coefTraceEvaluation l E n ≅
          coefPairingFiniteHom l E X n (integralDualizingFiniteTerm l E D X n))
      (eB : ∀ n : ℕ,
        coefPairingSupport l E D X S ⋙ coefTraceEvaluation l E n ≅
          coefPairingFiniteC l E D X n)
      (eQcompact : ∀ n : ℕ,
        (coefTraceEvaluation l E n).obj (coefTraceDualizingTower l E D X Q) ≅
          (coefPairingFiniteSupport l E (finiteDualizingCompactification D X) n).obj
            (integralDualizingFiniteTerm l E D X n)),
      (∀ (K : DerivedCategory (scalarReductionSource.{u, u} l E X))
        (P : CochainComplex (scalarReductionSource.{u, u} l E X) ℤ)
        (_eP : DerivedCategory.Q.obj P ≅ K)
        (I : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource.{u, u} l E X) ℤ)
        (_hI : I.IsKInjective)
        (_eI : DerivedCategory.Q.obj I ≅
          (coefficientSequenceDerivedRestriction.{u, u} l E X).obj (coefTraceInput l E X Q)),
        Nonempty ((coefPairingHom l E X S Q).obj (op K) ≅
          DerivedCategory.Q.obj (coefPairingHomComplex l E X P I))) ∧
      (∀ n : ℕ, ∃ scalarIso :
        coefPairingIntegralHom l E X n (integralDualizingFiniteTerm l E D X n) ≅
          coefPairingFiniteHom l E X n (integralDualizingFiniteTerm l E D X n),
        (eIntegralHom n).hom ≫ scalarIso.hom = (eH n).hom) ∧
      (∀ (K : DerivedCategory (scalarReductionSource.{u, u} l E X))
        {m n : ℕ} (h : n ≤ m),
        (coefTraceTransition l E h).app ((coefPairingSupport l E D X S).obj K) ≫
          (eB n).hom.app K =
        (eB m).hom.app K ≫
          (coefPairingIntegralSections l E (Spec (.of D.k))).map
            (compactSupportRestrictedTransition l E (finiteDualizingCompactification D X)
              m n h K)) ∧
      (∀ (K : DerivedCategory (scalarReductionSource.{u, u} l E X)),
        finiteTorConstructibleIntegral l E X K → ∀ n : ℕ,
        (coefTraceEvaluation l E n).map
            (G.beta l E (S.reduction.obj K) (coefTraceInput l E X Q)) ≫
          (eQcompact n).hom =
        (evaluationTensor n).hom.app
            ((coefPairingHom l E X S Q).obj (op K), (coefPairingSupport l E D X S).obj K) ≫
          ((eH n).hom.app (op K) ⊗ₘ (eB n).hom.app K) ≫
            coefPairingFiniteBeta l E (finiteDualizingCompactification D X) S G n (F n)
              ((scalarReductionDerivedExtension l E X n).obj K)
              (integralDualizingFiniteTerm l E D X n)) ∧
      (∀ (K K' : DerivedCategory (scalarReductionSource.{u, u} l E X)),
        finiteTorConstructibleIntegral l E X K → finiteTorConstructibleIntegral l E X K' →
          ∀ f : K ⟶ K',
          (coefPairingTensor l E).map
              (Prod.mkHom ((coefPairingHom l E X S Q).map f.op) (𝟙 _)) ≫
            G.beta l E (S.reduction.obj K) (coefTraceInput l E X Q) =
          (coefPairingTensor l E).map
              (Prod.mkHom (𝟙 _) ((coefPairingSupport l E D X S).map f)) ≫
            G.beta l E (S.reduction.obj K') (coefTraceInput l E X Q)) := by
  classical
  obtain ⟨S, G, F, evaluationTensor, eH, eB, eQcompact, hB, hfinite⟩ :=
    coefPairingCompactificationModels l E D X hl Q eQ
  obtain ⟨hrep, hint⟩ := coefPairingHomRepresentativeComparison l E X S Q
  let targetIso (n : ℕ) :=
    (scalarReductionDerivedRestriction l E X n).mapIso (eQ n)
  let homIso (n : ℕ) :
      coefPairingIntegralHom l E X n
          ((coefficientSequenceDerivedEvaluation.{u, u} l E X n).obj
            (coefTraceInput l E X Q)) ≅
        coefPairingIntegralHom l E X n (integralDualizingFiniteTerm l E D X n) :=
    Functor.isoWhiskerRight
      ((Functor.curryObj (coefficientIntegralInternalHom l E X)).flip.mapIso (targetIso n))
      (coefPairingIntegralSections l E X)
  let eIntegralHom := fun n ↦ (hint n).some ≪≫ homIso n
  refine ⟨S, G, F, evaluationTensor, eIntegralHom, eH, eB, eQcompact, hrep, ?_,
    hB, hfinite, ?_⟩
  · intro n
    refine ⟨(eIntegralHom n).symm ≪≫ eH n, ?_⟩
    simp
  · intro K K' _ _ f
    exact coefPairingSystem_dinaturality l E G
      (S.reduction.obj K) (S.reduction.obj K') (coefTraceInput l E X Q)
      (S.reduction.map f)

end WeilConjectures
