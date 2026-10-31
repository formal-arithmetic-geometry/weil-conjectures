/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteFreeCompletedScalarComparison
import WeilConjectures.AlgebraicGeometry.IntegralScalarOrdinaryModelComparison
import all WeilConjectures.AlgebraicGeometry.FiniteFreeCompletedScalarComparison

/-! # The exact model of ordinary completed integral scalar extension

The ordinary scalar functor is exact, and its chosen derived model is identified
with the exact derived functor by the prescribed universal counit.
(blueprint: lem-fd-exact-completed-ordinary-scalar-model).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option Elab.async false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
section ExactModelConstruction
variable (l : ℕ) [Fact l.Prime] (T : Scheme.{u})

attribute [-instance] integralOperationsAbLocallyBijective integralOperationsAbSheafify
  integralOperationsSiteSmall integralOperationsCommHasDerivedCategory
  scalarReductionSourceDerived scalarReductionTargetDerived
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology
  PrincipalKoszulStrictReplacement.abSheafify
  PrincipalKoszulStrictReplacement.abLocallyBijective
  PrincipalKoszulStrictReplacement.siteSmall
  SheafOfModules.cochainModulesMonoidal SheafOfModules.cochainModulesSymmetric
  SheafOfModules.cochainModulesPreadditive
attribute [local irreducible] HasDerivedCategory.standard completedScalarChangeData
  integralOrdinaryScalar
attribute [local instance 5000] integralTowerHasDerivedCategory
private local instance : EssentiallySmall.{u+1} T.ProEt :=
  essentiallySmallSelf.{0, u, u+1} _
private local instance : HasSheafify (ProEt.topology T) AddCommGrpCat.{u+1} :=
  integralCoefficientAbSheafify.{u, u} T
private local instance :
    (ProEt.topology T).WEqualsLocallyBijective AddCommGrpCat.{u+1} :=
  integralCoefficientAbLocallyBijective.{u, u} T

private theorem ordinaryExact
    (E L : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L) :
    PreservesFiniteLimits (completedOrdinaryScalarExtension.{u, u} l E L ι T) ∧
      PreservesFiniteColimits (completedOrdinaryScalarExtension.{u, u} l E L ι T) := by
  obtain ⟨t, _, _, _, _⟩ := integralScalarOrdinaryModelComparison l E L ι T
  exact ⟨preservesFiniteLimits_of_natIso t, preservesFiniteColimits_of_natIso t⟩

private def ordinaryExactModel
    (E L : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L)
    [PreservesFiniteLimits (completedOrdinaryScalarExtension.{u, u} l E L ι T)]
    [PreservesFiniteColimits (completedOrdinaryScalarExtension.{u, u} l E L ι T)] :
    completedDerivedScalarExtension.{u, u} l E L ι T ≅
      (completedOrdinaryScalarExtension.{u, u} l E L ι T).mapDerivedCategory := by
  let D := completedScalarCochainModel.{u, u} l E L ι T
  let q := HomologicalComplex.quasiIso (integralTowerModules l E T) (.up ℤ)
  let C := completedDerivedScalarExtension.{u, u} l E L ι T
  let S := completedOrdinaryScalarExtension.{u, u} l E L ι T
  let ε : DerivedCategory.Q ⋙ C ⟶
      completedOrdinaryScalarComplex.{u, u} l E L ι T ⋙ DerivedCategory.Q := D.ε
  have hC : C.IsLeftDerivedFunctor ε q := D.universal
  have hS : S.mapDerivedCategory.IsLeftDerivedFunctor S.mapDerivedCategoryFactors.hom q :=
    Functor.isLeftDerivedFunctor_of_inverts q _ S.mapDerivedCategoryFactors
  exact Functor.leftDerivedNatIso C S.mapDerivedCategory ε S.mapDerivedCategoryFactors.hom q
    (Iso.refl _)

private theorem ordinaryExactModel_counit
    (E L : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L)
    [PreservesFiniteLimits (completedOrdinaryScalarExtension.{u, u} l E L ι T)]
    [PreservesFiniteColimits (completedOrdinaryScalarExtension.{u, u} l E L ι T)]
    (P : CochainComplex (integralTowerModules l E T) ℤ) :
    (ordinaryExactModel l T E L ι).hom.app (DerivedCategory.Q.obj P) ≫
      (completedOrdinaryScalarExtension.{u, u} l E L ι T).mapDerivedCategoryFactors.hom.app P =
        completedScalarCounit.{u, u} l E L ι T P := by
  let D := completedScalarCochainModel.{u, u} l E L ι T
  let q := HomologicalComplex.quasiIso (integralTowerModules l E T) (.up ℤ)
  let C := completedDerivedScalarExtension.{u, u} l E L ι T
  let S := completedOrdinaryScalarExtension.{u, u} l E L ι T
  let ε : DerivedCategory.Q ⋙ C ⟶
      completedOrdinaryScalarComplex.{u, u} l E L ι T ⋙ DerivedCategory.Q := D.ε
  have hC : C.IsLeftDerivedFunctor ε q := D.universal
  have hS : S.mapDerivedCategory.IsLeftDerivedFunctor S.mapDerivedCategoryFactors.hom q :=
    Functor.isLeftDerivedFunctor_of_inverts q _ S.mapDerivedCategoryFactors
  change (Functor.leftDerivedNatTrans C S.mapDerivedCategory ε
    S.mapDerivedCategoryFactors.hom q (𝟙 _)).app (DerivedCategory.Q.obj P) ≫ _ = _
  exact (Functor.leftDerivedNatTrans_app C S.mapDerivedCategory ε
    S.mapDerivedCategoryFactors.hom q (𝟙 _) P).trans
      ((Category.comp_id _).trans (completedScalarCochainModel_counit l E L ι T P))

attribute [local irreducible] ordinaryExactModel completedScalarCochainModel

/-- Exactness and the counit-normalized exact derived model of ordinary scalar extension.
Source: Stacks Tag 06YY, as realized by the finite-free completed scalar comparison;
ordinary integral coefficient model comparison.
(blueprint: lem-fd-exact-completed-ordinary-scalar-model).

Proof: the ordinary integral scalar model comparison identifies the chosen ordinary
functor with the finite-free exact tensor functor, so finite limits and colimits
are preserved. Its map on the derived category therefore has an invertible
factorization counit and is a left derived functor of the ordinary cochain functor.
The chosen scalar cochain model is another left derived functor of that same
functor. Apply uniqueness of left derived functors to the identity transformation.
The defining component equation for the induced derived transformation identifies
its composite with the exact factorization counit with the prescribed scalar
counit. This argument includes identity coefficient extensions and zero complexes.
-/
theorem exactCompletedOrdinaryScalarModel
    (E L : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L) :
    ∃ hlim : PreservesFiniteLimits (completedOrdinaryScalarExtension.{u, u} l E L ι T),
      ∃ hcolim : PreservesFiniteColimits (completedOrdinaryScalarExtension.{u, u} l E L ι T),
        letI := hlim
        letI := hcolim
        ∃ e : completedDerivedScalarExtension.{u, u} l E L ι T ≅
            (completedOrdinaryScalarExtension.{u, u} l E L ι T).mapDerivedCategory,
          ∀ P : CochainComplex (integralTowerModules l E T) ℤ,
            e.hom.app (DerivedCategory.Q.obj P) ≫
              (completedOrdinaryScalarExtension.{u, u} l E L ι T).mapDerivedCategoryFactors.hom.app
                P = completedScalarCounit.{u, u} l E L ι T P := by
  obtain ⟨hlim, hcolim⟩ := ordinaryExact l T E L ι
  let := hlim
  let := hcolim
  refine ⟨hlim, hcolim, ordinaryExactModel l T E L ι, ?_⟩
  intro P
  exact ordinaryExactModel_counit l T E L ι P

end ExactModelConstruction
end WeilConjectures
