/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PodCompletionScalarFormulas

/-! # Multiplication normalization of the completed scalar tower -/

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

/-- Multiplication realizes the completed scalar tower and its specified comparison.
Source: Bhatt--Scholze Lemma 6.8.2(1), Definitions 3.5.2--3.5.3;
step 3 of lem-pod-completion-unit-scalar-intertwining.
(blueprint: lem-pod-scalar-multiplication-realization).

Proof: identify the target quotient tensor at level n with the specified scalar
quotient tensor by multiplication (p tensor a) tensor b mapped to p tensor ab.
Its inverse sends p tensor b to (p tensor 1) tensor b. Balancing, the completed
projection equations, and the quotient universal property prove these are inverse
sheaf maps and commute with every differential and quotient transition. Apply the
same product maps to both signed Roos coordinates to get m. Change of rings
preserves K-flatness and flat terms, so both sides compute their derived functors
on these representatives. Descend the comparison to c, with the displayed counit
equation. The strict comparison from ordinary scalar extension to the specified
scalar tower has unshifted coordinates p tensor residue(a) and zero shifted
coordinate. Multiplication identifies it with CS.unit. Uniqueness in the resolving
localization then gives the displayed equality for completedScalarComparison.
All constructions are natural; finite quotients of exponent one and zero complexes
use the same multiplication and unit formulas. -/
theorem scalarMultiplicationRealization
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
    (σ : F.T ≅ completedDerivedScalarExtension l E L ι W)
    (hσ : ∀ P : CochainComplex (integralTowerModules l E W) ℤ,
      σ.hom.app (DerivedCategory.Q.obj P) ≫ completedScalarCounit l E L ι W P =
        F.ε.app P ≫ DerivedCategory.Q.map
          ((NatIso.mapHomologicalComplex (eqToIso hE) (.up ℤ)).hom.app P))
    (CS : @Model.{t + 1, t, max u (t + 1), max u (t + 1) + 1}
    W.ProEt inferInstance (essentiallySmallSelf.{u} _)
    (Scheme.ProEt.topology W) inferInstance
    (integralCoefficientAbSheafify.{t, u} W)
    (integralCoefficientAbLocallyBijective.{t, u} W)
    (completedIntegralCommRingSheafUnrestricted l L W)
    (integralTowerHasDerivedCategory l L W)
    (PrincipalKoszulStrictReplacement.uniformizer l L W)) :
    ∃ c : F.T ⋙ CS.completion ≅ integralScalarExtensionOfUniverses l E L ι W,
      (∀ P : (integralOperationsGoodComplex l E W).FullSubcategory,
        ModelData.MultiplicationFormula l E L ι W F hE CS c P) ∧
      ∀ K : DerivedCategory (integralTowerModules l E W),
        (completedScalarComparison l E L ι W).app K =
          σ.inv.app K ≫ CS.unit.app (F.T.obj K) ≫ c.hom.app K := by sorry

end WeilConjectures.PodCompletionScalar
