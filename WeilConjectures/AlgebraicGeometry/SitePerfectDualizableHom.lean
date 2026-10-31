/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SixFunctorDatum
public import WeilConjectures.AlgebraicGeometry.DerivedPullbackTensorHom
public import WeilConjectures.AlgebraicGeometry.SitePerfectComplex
import WeilConjectures.CategoryTheory.RingedSitePerfectDualityForModel
import WeilConjectures.AlgebraicGeometry.ClosedEmbeddingPerfectEvaluation
import WeilConjectures.AlgebraicGeometry.RationalEvaluationCover
import WeilConjectures.AlgebraicGeometry.RationalCoverReflectsIso
import WeilConjectures.AlgebraicGeometry.CommonStagePerfectEvaluationDescent
public import WeilConjectures.AlgebraicGeometry.LegacySitePerfectComplex

/-! # Internal Hom through the coefficient dual

Source: Weil conjectures blueprint main-20261015, sec-six-functors,
sk-prop-sf-dualizable-biduality/prop-sf-dualizable-hom
(blueprint: prop-sf-dualizable-hom).
The four conjuncts are the finite, completed integral, rational, and common-stage
coefficient choices. Their comparison is the evaluation transpose with the signed
symmetry, using the actual closed domains of the fixed six-functor datum.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures

/-- A site-perfect finite-Tor constructible complex has canonical evaluation
`K^∨ ⊗ M → RHom(K,M)` invertible for every finite-Tor constructible M, at each
of the four coefficient stages. The n-th index means exponent n+1.
Source: blueprint main-20261015, prop-sf-dualizable-hom; Stacks Tag 08JJ
(blueprint: prop-sf-dualizable-hom).

Proof: apply the proved ringed-site perfect-duality theorem in the specified
finite and integral ambient presentations. Reflect its evaluation isomorphisms
through the fully faithful normalized closed embeddings. At rational coefficients,
use the local bounded-complex evaluation calculation and detect invertibility
from its ambient slice restrictions. Apply that same rational argument to every
finite coefficient field supplied by the datum, and descend the resulting
isomorphisms to the common-stage pair category.
-/
theorem sixFunctor_sitePerfect_dualEvaluation_isIso
    (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] (n : ℕ)
    (S : SixFunctorDatum D C E (n + 1) (Nat.succ_pos n))
    (X : SixFunctorSpace D) [IsSeparated X.obj.hom] :
    (∀ K M : (S.toSixFunctorOperationDatum.finiteTorDomain X).FullSubcategory,
      IsFiniteCoefficientSitePerfect C.l E X.obj.left n K.obj.obj →
      IsIso (ringedSiteDualEvaluationLeft (S.finiteClosed X).closed
        (S.finiteClosed X).symmetric (S.finiteClosed X).closed.monoidal.tensorUnit
        (Iso.refl _) K M)) ∧
    (∀ K M : (S.toSixFunctorOperationDatum.integralFiniteTorDomain X).FullSubcategory,
      IsIntegralCoefficientSitePerfect C.l E X.obj.left K.obj.obj →
      IsIso (ringedSiteDualEvaluationLeft (S.integralClosed X).closed
        (S.integralClosed X).symmetric (S.integralClosed X).closed.monoidal.tensorUnit
        (Iso.refl _) K M)) ∧
    (∀ K M : (⊤ : ObjectProperty
        (sfRationalConstructibleCategory C.l E X.obj.left)).FullSubcategory,
      IsSfRationalCoefficientSitePerfect C.l E X.obj.left K.obj →
      IsIso (ringedSiteDualEvaluationLeft (S.rationalClosed X).closed
        (S.rationalClosed X).symmetric (S.rationalClosed X).closed.monoidal.tensorUnit
        (Iso.refl _) K M)) ∧
    (∀ K M : (⊤ : ObjectProperty
        (generalAlgebraicallyClosedConstructibleCategory C.l C.Qbar X.obj.left)).FullSubcategory,
      IsGeneralAlgebraicallyClosedCoefficientSitePerfect C.l C.Qbar X.obj.left K.obj →
      IsIso (ringedSiteDualEvaluationLeft (S.commonClosed X).closed
        (S.commonClosed X).symmetric (S.commonClosed X).closed.monoidal.tensorUnit
        (Iso.refl _) K M)) := by
  let := integralCoefficientAbSheafify.{u, u} X.obj.left
  let := integralCoefficientAbLocallyBijective.{u, u} X.obj.left
  let (U : X.obj.left.ProEt) := sitePerfectOverAbSheafify.{u, u} X.obj.left U
  let (U : X.obj.left.ProEt) := sitePerfectOverAbLocallyBijective.{u, u} X.obj.left U
  have rational (L : Type u) [Field L] [Algebra (Padic C.l) L]
      [FiniteDimensional (Padic C.l) L]
      (A : SixFunctorCoefficientClosedModels C.l L X.obj.left)
      (K M : (⊤ : ObjectProperty
        (sfRationalConstructibleCategory C.l L X.obj.left)).FullSubcategory)
      (hK : IsSfRationalCoefficientSitePerfect C.l L X.obj.left K.obj) :
      IsIso (ringedSiteDualEvaluationLeft A.rational.closed A.rational.symmetric
        A.rational.closed.monoidal.tensorUnit (Iso.refl _) K M) := by
    have h := rationalCover_reflectsIso D C L X _
      (rationalEvaluation_cover D C L X A K M hK)
    let := h
    exact (⊤ : ObjectProperty
      (sfRationalConstructibleCategory C.l L X.obj.left)).fullyFaithfulι.isIso_of_isIso_map _
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro K M hK
    have h := ringedSitePerfectDualityForModel.{u+1,u,u,u+2}
      (Scheme.ProEt.topology X.obj.left) _ K.obj.obj hK (S.finiteModel X)
    exact closedEmbedding_perfectEvaluation (S.finiteClosed X) (S.finiteModel X).closed
      (S.finiteModel X).symmetric _ (S.finiteModelComparison X) _
      (S.finiteModel X).unitIso K M (fun T ↦ by
        let := h
        exact inferInstanceAs (IsIso
          ((ringedSiteDualEvaluationLeftNatTrans _ _ _ _ K.obj.obj).app T)))
  · intro K M hK
    have h := ringedSitePerfectDualityForModel.{u+1,u,u,u+2}
      (Scheme.ProEt.topology X.obj.left) _ K.obj.obj hK (S.integralModel X)
    exact closedEmbedding_perfectEvaluation (S.integralClosed X) (S.integralModel X).closed
      (S.integralModel X).symmetric _ (S.integralModelComparison X) _
      (S.integralModel X).unitIso K M (fun T ↦ by
        let := h
        exact inferInstanceAs (IsIso
          ((ringedSiteDualEvaluationLeftNatTrans _ _ _ _ K.obj.obj).app T)))
  · exact rational E ⟨S.integralClosed X, S.integralModel X,
      S.integralModelComparison X, S.rationalClosed X, S.rationalClosedComparison X⟩
  · exact commonStage_perfectEvaluation_descent D C E n S X
      (fun E₀ ↦ rational _ (S.coefficientClosedModels E₀ X))

end WeilConjectures
