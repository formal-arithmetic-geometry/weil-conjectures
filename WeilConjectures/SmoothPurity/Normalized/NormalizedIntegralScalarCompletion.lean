/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.IntegralScalarOperations.IntegralOperationsScalarExtension

import all WeilConjectures.TraceFormula.Supporting.FiniteFreeCompletedScalarComparison
import all WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarExtensionConstructible
import WeilConjectures.SmoothPurity.Sf.SfDerivedCompleteLegacyComparison
public import WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarExtensionConstructibleIntrinsic

/-! # The normalized integral scalar-completion comparison

Source: Bhatt--Scholze, Proposition 3.5.1 and Lemma 6.8.2(1)
(blueprint: lem-weil-normalized-scalar-completion).

The ordinary coefficient model and its universal derived counit transport the existing
finite-free comparison to the specified quotient-completion chain map.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace WeilConjectures

attribute [local irreducible] HasDerivedCategory.standard
  integralOrdinaryScalar completedIntegralCoefficientSheafUnrestricted
  completedIntegralCommRingSheafUnrestricted
attribute [-instance] scalarReductionSourceDerived scalarReductionTargetDerived
attribute [-instance] integralOperationsSiteSmall
attribute [local instance 3000] integralTowerHasDerivedCategory
attribute [local instance 50000] hasSheafCompose_of_preservesLimitsOfSize

private local instance (W : AlgebraicGeometry.Scheme.{u}) :
    EssentiallySmall.{u+1} W.ProEt := essentiallySmallSelf.{0, u, u+1} _

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall
  GrothendieckTopology.hasSheafify_proEtTopology
  PrincipalKoszulStrictReplacement.abSheafify
  PrincipalKoszulStrictReplacement.abLocallyBijective
  PrincipalKoszulStrictReplacement.siteSmall
  integralOperationsAbSheafify integralOperationsAbLocallyBijective
  integralOperationsCommHasDerivedCategory
  SheafOfModules.cochainModulesMonoidal SheafOfModules.cochainModulesSymmetric
  SheafOfModules.cochainModulesPreadditive

private local instance (W : AlgebraicGeometry.Scheme.{u}) :
    HasSheafify (AlgebraicGeometry.Scheme.ProEt.topology W) AddCommGrpCat.{u+1} :=
  integralCoefficientAbSheafify.{u, u} W

private local instance (W : AlgebraicGeometry.Scheme.{u}) :
    (AlgebraicGeometry.Scheme.ProEt.topology W).WEqualsLocallyBijective
      AddCommGrpCat.{u+1} := integralCoefficientAbLocallyBijective.{u, u} W

/-- The unique scalar-completion transformation with the specified counit square,
isomorphic on every derived-complete input.
Source: Bhatt--Scholze, Proposition 3.5.1 and Lemma 6.8.2(1)
(blueprint: lem-weil-normalized-scalar-completion).
Proof: identify the two ordinary sheafified scalar models by their completed coefficient
maps and lift this isomorphism to complexes. The universal left-derived comparison gives
a natural isomorphism of their derived functors and preserves the counits. Compose with
the existing normalized completed-scalar comparison. Its counit equation and the strict
chain transport identify the resulting square with the required quotient-completion
normalization, including the zero shifted coordinate. Intrinsic derived completeness
agrees with the legacy augmented-tower predicate; choose an auxiliary finite field in a
prime characteristic different from l to apply the finite-free comparison, which makes
this specified component invertible. Finally, good complexes localize to the derived
category. The normalization forces equality on every good representative by cancellation
of its representative comparison, and localization forces equality on all objects. -/
theorem normalizedIntegralScalarCompletion (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L) (W : AlgebraicGeometry.Scheme.{u}) :
    ∃! χ : integralOrdinaryDerivedScalar l E L ι W ⟶ integralScalarExtension l E L ι W,
      (∀ P : (integralOperationsGoodComplex l E W).FullSubcategory,
        χ.app (DerivedCategory.Q.obj P.obj) ≫
            (integralScalarExtensionComparison l E L ι W).hom.app P =
          (integralOrdinaryScalar l E L ι W).mapDerivedCategoryFactors.hom.app P.obj ≫
            DerivedCategory.Q.map ((integralScalarCompletionChain l E L ι W).app P.obj)) ∧
      (∀ K, IsSfDerivedComplete l E W K → IsIso (χ.app K)) := by
  exact archivedIntegralScalarCompletion l E L ι W

end WeilConjectures
