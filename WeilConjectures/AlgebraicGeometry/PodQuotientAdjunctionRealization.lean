/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PodCompletionScalarFormulas

/-! # Normalized principal quotient and adjunction realization -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology
attribute [-instance] WeilConjectures.integralOperationsCommHasDerivedCategory
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.integralOperationsAbLocallyBijective
attribute [-instance] WeilConjectures.integralOperationsAbSheafify
attribute [-instance] WeilConjectures.PrincipalKoszulStrictReplacement.abSheafify
attribute [-instance] WeilConjectures.PrincipalKoszulStrictReplacement.abLocallyBijective
attribute [-instance] WeilConjectures.PrincipalKoszulStrictReplacement.siteSmall

attribute [local irreducible] HasDerivedCategory.standard
attribute [local instance 5000] WeilConjectures.integralTowerHasDerivedCategory
attribute [local irreducible] CategoryTheory.PrincipalQuotientCompletion.quotientTower
  CategoryTheory.roosF SheafOfModules.monoidalCategory

universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open CategoryTheory.PrincipalQuotientCompletion
namespace WeilConjectures.PodCompletionScalar

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L) (W : Scheme.{t})

/-- A strict principal quotient model has a realization by the actual simultaneous
reduction and inverse-limit adjunction, with the entire unit normalization.
Source: Bhatt--Scholze Definitions 3.5.2--3.5.3; the coefficient/unit comparison in
step 2 of lem-pod-completion-unit-scalar-intertwining.
(blueprint: lem-pod-quotient-adjunction-realization).

Proof: take the normalized ordinary and derived models from the completion-unit
strict-quotient theorem. At level n identify the sheaf cokernel of multiplication
by the (n+1)-st uniformizer power with the residue sheaf through its projection.
Tensor with a flat-term K-flat P. The cokernel equations show that these maps
commute with all quotient transitions and carry the quotient augmentation to
M.augmentation. Apply the strict signed Roos functor, preserving both coordinates.
Its counit on K-flat complexes computes the universal completion. Localization on
flat-term K-flat representatives therefore gives alpha naturally. Its counit
normalization is the last displayed equation. Applying that equation to the
augmentation, whose shifted coordinate is zero, gives the actual adjunction unit
as a whole morphism; descent gives the equation on every derived object. -/
theorem quotientAdjunctionRealization
    [∀ x : W, Invertible (l : W.residueField x)]
    (CR : @Model.{t + 1, t, max u (t + 1), max u (t + 1) + 1}
    W.ProEt inferInstance (essentiallySmallSelf.{u} _)
    (Scheme.ProEt.topology W) inferInstance
    (integralCoefficientAbSheafify.{t, u} W)
    (integralCoefficientAbLocallyBijective.{t, u} W)
    (completedIntegralCommRingSheafUnrestricted l E W)
    (integralTowerHasDerivedCategory l E W)
    (PrincipalKoszulStrictReplacement.uniformizer l E W)) :
    ∃ (A : CoefficientDerivedSystemCalculus l E W)
      (M : CompletionUnit.OrdinaryModel l E W)
      (N : CompletionUnit.DerivedModel l E W A M)
      (α : CR.completion ≅ A.reduction ⋙ coefficientSequenceLimit l E W),
      ModelData.QuotientRealization l E W A M N CR α := by sorry

end WeilConjectures.PodCompletionScalar
