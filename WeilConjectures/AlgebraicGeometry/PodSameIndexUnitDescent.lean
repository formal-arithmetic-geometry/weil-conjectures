/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PodCompletionScalarFormulas

/-! # Same-index quotient maps and descent of their unit equation -/

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

/-- The balanced same-index quotient map descends with its entire unit equation.
Source: Bhatt--Scholze Definitions 3.5.2--3.5.3 and Lemma 6.8.2(1);
steps 5--7 of lem-pod-completion-unit-scalar-intertwining.
(blueprint: lem-pod-same-index-unit-descent).

Proof: form d_n by the balanced residue map (p tensor a) tensor z mapped to
p tensor iota_n(a) residue_n(z). The completed coefficient projection equations
prove balancing and compatibility with adjacent quotient maps. The canonical
map from tensor of a product to product of tensors followed by d_n gives c.
Compatibility with transitions gives c(1-shift)=(1-shift)c, hence applying c
to both signed cone coordinates gives delta and a natural cochain map. Finite
freeness makes ordinary extension exact and tensor commute with countable products;
this can be checked in any finite basis, while the specified maps use only product
projections and are independent of that basis. The K-flat resolving localization
and strict Roos invariance descend the map to b with exactly the counit equation
below. Before descent, the composite with the source augmentation has coordinates
(0,(p tensor residue(z))_n). These are both coordinates of the target augmentation,
so localization gives the entire unit equation for every K. No completeness or
boundedness is used in the construction or this equation. -/
theorem sameIndexUnitDescent
    (F : @SheafOfModules.DerivedChangeOfRingsCochainModel.{t + 1, t, max u (t + 1),
    max u (t + 1) + 1, max u (t + 1) + 1}
    W.ProEt inferInstance (essentiallySmallSelf.{u} _)
    (Scheme.ProEt.topology W) inferInstance
    (integralCoefficientAbLocallyBijective.{t, u} W)
    (integralCoefficientAbSheafify.{t, u} W)
    (completedIntegralCommRingSheafUnrestricted l E W)
    (completedIntegralCommRingSheafUnrestricted l L W)
    (completedCoefficientMap l E L ι W)
    (integralTowerHasDerivedCategory l E W)
    (integralTowerHasDerivedCategory l L W))
    (hE : F.E = completedOrdinaryScalarExtension l E L ι W)
    (CR : @Model.{t + 1, t, max u (t + 1), max u (t + 1) + 1}
    W.ProEt inferInstance (essentiallySmallSelf.{u} _)
    (Scheme.ProEt.topology W) inferInstance
    (integralCoefficientAbSheafify.{t, u} W)
    (integralCoefficientAbLocallyBijective.{t, u} W)
    (completedIntegralCommRingSheafUnrestricted l E W)
    (integralTowerHasDerivedCategory l E W)
    (PrincipalKoszulStrictReplacement.uniformizer l E W))
    (CS : @Model.{t + 1, t, max u (t + 1), max u (t + 1) + 1}
    W.ProEt inferInstance (essentiallySmallSelf.{u} _)
    (Scheme.ProEt.topology W) inferInstance
    (integralCoefficientAbSheafify.{t, u} W)
    (integralCoefficientAbLocallyBijective.{t, u} W)
    (completedIntegralCommRingSheafUnrestricted l L W)
    (integralTowerHasDerivedCategory l L W)
    (PrincipalKoszulStrictReplacement.uniformizer l L W)) :
    ∃ b : CR.completion ⋙ F.T ⟶ F.T ⋙ CS.completion,
      (∀ P : (integralOperationsGoodComplex l E W).FullSubcategory,
        ModelData.SameIndexFormula l E L ι W F CR CS b P.obj) ∧
      ∀ K : DerivedCategory (integralTowerModules l E W),
        F.T.map (CR.unit.app K) ≫ b.app K = CS.unit.app (F.T.obj K) := by sorry

end WeilConjectures.PodCompletionScalar
