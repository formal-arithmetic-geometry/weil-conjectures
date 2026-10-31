/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SixFunctorDatum
public import WeilConjectures.AlgebraicGeometry.SitePerfectComplex
public import WeilConjectures.AlgebraicGeometry.LegacySitePerfectComplex

/-! # Descent of perfect evaluation from finite coefficient fields -/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures

/-- Finite-stage perfect evaluation propagates to the actual common-stage category.
Source: blueprint prop-sf-dualizable-hom, step 14
(blueprint: lem-sf-common-stage-perfect-evaluation-descent).

Proof: descend K and its perfect model to the finite field in hK. Represent M
at its own finite coefficient field and pass to a common upper field. Exact
coefficient extension preserves the bounded local complex and its rational
finite-free retractions, hence preserves site-perfectness. Apply hstage at
that common field. The datum's coefficient and common-stage closed comparisons
identify the image of this evaluation with the specified common-stage arrow:
transpose the evaluation square, then use its symmetry equation. Their tensor
and Hom comparisons are invertible. The stage inverse therefore represents
an inverse in the filtered pair category. Finally transport in K along the
isomorphism in hK using naturality of evaluation. This uses actual finite
stages and imposes no Karoubi completion or uniform global choice of stage. -/
theorem commonStage_perfectEvaluation_descent
    (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] (n : ℕ)
    (S : SixFunctorDatum D C E (n + 1) (Nat.succ_pos n)) (X : SixFunctorSpace D)
    (hstage : ∀ (E₀ : Padic.FiniteCoefficientFields C.l C.Qbar)
      (K M : (⊤ : ObjectProperty (sfRationalConstructibleCategory C.l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} C.l C.Qbar E₀)
        X.obj.left)).FullSubcategory),
      IsSfRationalCoefficientSitePerfect C.l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} C.l C.Qbar E₀) X.obj.left K.obj →
      IsIso (ringedSiteDualEvaluationLeft (S.coefficientClosedModels E₀ X).rational.closed
        (S.coefficientClosedModels E₀ X).rational.symmetric
        (S.coefficientClosedModels E₀ X).rational.closed.monoidal.tensorUnit
        (Iso.refl _) K M))
    (K M : (⊤ : ObjectProperty (generalAlgebraicallyClosedConstructibleCategory
      C.l C.Qbar X.obj.left)).FullSubcategory)
    (hK : IsGeneralAlgebraicallyClosedCoefficientSitePerfect C.l C.Qbar X.obj.left K.obj) :
    IsIso (ringedSiteDualEvaluationLeft (S.commonClosed X).closed
      (S.commonClosed X).symmetric (S.commonClosed X).closed.monoidal.tensorUnit
      (Iso.refl _) K M) := by sorry

end WeilConjectures
