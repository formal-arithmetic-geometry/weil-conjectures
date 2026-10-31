/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.PodCompletedReflection.PodReindexingCompletedEvaluationReflection
public import WeilConjectures.AlgebraicGeometry.CoefficientHomRepresentativeEvaluation
public import WeilConjectures.Algebra.Homology.DerivedInternalHomOfUniverses
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import WeilConjectures.SixFunctors.Etale.Derived.Hom
public import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Generator.Basic
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMapOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplex
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import WeilConjectures.Algebra.Homology.HomComplexSectionsQuasiIsoOfUniverses
public import WeilConjectures.CategoryTheory.R.RGammaDerivedLimitSupplement
public import Mathlib.Algebra.Category.Grp.Abelian
public import WeilConjectures.Algebra.Homology.HomComplexSectionsDerivedNaturalityOfUniverses
public import WeilConjectures.Algebra.Homology.RhomIntoKInjectiveLocal
public import WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalizedOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import WeilConjectures.Algebra.Homology.LocalizedRestrictionAdjunctionOfUniverses
public import WeilConjectures.Algebra.Homology.LocalizedRestrictionExtensionExistsOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import WeilConjectures.Algebra.Homology.HomComplexSectionsHomotopyNaturalityOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplexProjections
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCanonicalComparisonOfUniverses
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsCommOfUniverses
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
public import Mathlib.Algebra.Category.Grp.EpiMono
public import WeilConjectures.Algebra.Homology.LocalizedModuleRestrictionQuasiIsoOfUniverses
public import Mathlib.Algebra.Homology.QuasiIso
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import WeilConjectures.Algebra.Homology.QuasiIsoOfSectionsOfUniverses
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.Algebra.Homology.Functor
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import WeilConjectures.Algebra.Homology.HomComplexComponents
public import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMap
public import WeilConjectures.Algebra.Homology.HomTensorDegreewiseEquation
public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorIso
public import WeilConjectures.PoincareDuality.Pod.PodCompletionReindexCoefficientTransition
public import WeilConjectures.CategoryTheory.Scalar.ScalarInternalHomAdjunction
public import WeilConjectures.CategoryTheory.Ringed.Finite.RingedFiniteFreeHomBaseChangeCoordinates
public import WeilConjectures.PoincareDuality.Pod.PodCommonStageObjectNormalizations
import WeilConjectures.PoincareDuality.PodCoefficientDescent.PodFiniteScalarTensorNormalization
import WeilConjectures.Algebra.Homology.PoincareDuality.ExactScalarDerivedPair

/-! # Realizing the normalized finite-scalar coordinate interface

Source: blueprint dual-Tate compatibility, Step 5; Stacks 08J9 and 08JA.
This complete, already proved specialization is compiled separately from its caller
for the single-file runtime limit. No unfinished statement is introduced.
-/

@[expose] public noncomputable section
set_option linter.privateModule false
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option Elab.async false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u v
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TensorProduct
open AlgebraicGeometry.Scheme
namespace WeilConjectures.PodCoefficientDescent

attribute [local irreducible] AlgebraicGeometry.Scheme.residueField
  HasDerivedCategory.standard completedIntegralCoefficientSheafUnrestricted
  scalarReductionExistence scalarReductionDerivedExistence

attribute [local irreducible] Linear.homModule

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

section FiniteScalar
variable (L : Type u) [Field L] [Algebra ℚ_[l] L]
  [FiniteDimensional ℚ_[l] L] (ι : E →ₐ[ℚ_[l]] L)

attribute [local irreducible] scalarIntegralClosed scalarClosedTensor scalarHomOrdinary

set_option maxHeartbeats 600000 in
-- Bound elaboration of the normalized scalar model and its two adjunctions.
/-- Finite-biproduct coordinates under the normalized derived scalar adjunction.
The basis maps are fixed on every K-flat representative, before gamma is inverted.
Source: blueprint Step 5; Stacks 08J9, 08JA
(blueprint: lem-pod-finite-scalar-coordinates-realization).
Proof (node Step 2): construct the two basis maps by multiplying by the actual
basis sections on K-flat representatives. The normalized scalar adjunction and
restricted S-evaluation give beta. Uncurry each inclusion: scalar unit inserts 1
and the tensor comparison multiplies it by the chosen basis section. Its transpose
is Hom(M,basis inclusion into N). This proves the displayed equation for every
basis vector. The finite-biproduct universal property identifies the whole map.
Rank zero has no inclusions; no bound, completeness or perfection is used. -/
theorem finiteScalarCoordinatesRealization (W : Scheme.{u})
    (d : ℕ)
    (e : (SheafOfModules.scalarRestriction (integralCompletedScalarMap l E L ι W)).obj
      (SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l L W)) ≅
      SheafOfModules.free (R := completedIntegralCoefficientSheafUnrestricted l E W)
        (ULift.{u + 1} (Fin d))) :
    ∃ D : SheafOfModules.ScalarDerivedPair.{u + 1,u,u + 1,u + 2}
      (integralCompletedScalarMap l E L ι W),
      D.extension = integralOrdinaryScalar l E L ι W ∧
      D.derived = integralOrdinaryDerivedScalar l E L ι W ∧
      ∃ δ : integralOrdinaryDerivedScalar l E L ι W ⊣
        SheafOfModules.scalarDerivedRestriction (integralCompletedScalarMap l E L ι W),
        HEq δ D.adjunction ∧
        ∀ M N : DerivedCategory (integralTowerModules l E W),
        ∃ (aH : (⨁ fun _ : Fin d ↦
            (integralDerivedInternalHom l E W).obj (op M, N)) ≅
          (SheafOfModules.scalarDerivedRestriction (integralCompletedScalarMap l E L ι W)).obj
            ((integralOrdinaryDerivedScalar l E L ι W).obj
              ((integralDerivedInternalHom l E W).obj (op M, N))))
          (aN : (⨁ fun _ : Fin d ↦ N) ≅
            (SheafOfModules.scalarDerivedRestriction (integralCompletedScalarMap l E L ι W)).obj
              ((integralOrdinaryDerivedScalar l E L ι W).obj N))
          (β : (SheafOfModules.scalarDerivedRestriction
              (integralCompletedScalarMap l E L ι W)).obj
            ((integralDerivedInternalHom l L W).obj
              (op ((integralOrdinaryDerivedScalar l E L ι W).obj M),
                (integralOrdinaryDerivedScalar l E L ι W).obj N)) ≅
            (integralDerivedInternalHom l E W).obj
              (op M, (SheafOfModules.scalarDerivedRestriction
                (integralCompletedScalarMap l E L ι W)).obj
                  ((integralOrdinaryDerivedScalar l E L ι W).obj N))),
          RingedFiniteFreeBasisCoordinates.{u + 1,u,u,u + 2} (ProEt.topology W)
            (integralCompletedScalarMap l E L ι W) d e (integralOrdinaryScalar l E L ι W)
            (integralOrdinaryScalarWitness l E L ι W).choose_spec.choose
            (integralOrdinaryDerivedScalar l E L ι W)
            (integralOrdinaryScalar l E L ι W).mapDerivedCategoryFactors.hom
            ((integralDerivedInternalHom l E W).obj (op M, N)) aH ∧
          RingedFiniteFreeBasisCoordinates.{u + 1,u,u,u + 2} (ProEt.topology W)
            (integralCompletedScalarMap l E L ι W) d e (integralOrdinaryScalar l E L ι W)
            (integralOrdinaryScalarWitness l E L ι W).choose_spec.choose
            (integralOrdinaryDerivedScalar l E L ι W)
            (integralOrdinaryScalar l E L ι W).mapDerivedCategoryFactors.hom N aN ∧
          ((scalarIntegralClosed l E W).transpose _ M
            ((SheafOfModules.scalarDerivedRestriction
              (integralCompletedScalarMap l E L ι W)).obj
                ((integralOrdinaryDerivedScalar l E L ι W).obj N))).symm β.hom =
            (scalarIntegralClosed l E W).tensor.map (Prod.mkHom (𝟙 _) (δ.unit.app M)) ≫
            δ.unit.app _ ≫
            (SheafOfModules.scalarDerivedRestriction (integralCompletedScalarMap l E L ι W)).map
              ((scalarClosedTensor l E L ι W).hom.app _ ≫
                (scalarIntegralClosed l L W).tensor.map
                  (Prod.mkHom (δ.counit.app _) (δ.counit.app _))) ≫
            (SheafOfModules.scalarDerivedRestriction (integralCompletedScalarMap l E L ι W)).map
              ((scalarIntegralClosed l L W).evaluation
                ((integralOrdinaryDerivedScalar l E L ι W).obj M)
                ((integralOrdinaryDerivedScalar l E L ι W).obj N)) ∧
          ∀ i : Fin d,
            biproduct.ι _ i ≫ aH.hom ≫
              (SheafOfModules.scalarDerivedRestriction
                (integralCompletedScalarMap l E L ι W)).map
                  (scalarHomOrdinary l E L ι W M N) ≫ β.hom =
              (integralDerivedInternalHom l E W).map
                (Prod.mkHom (𝟙 (op M)) (biproduct.ι _ i ≫ aN.hom)) := by
  classical
  let J : GrothendieckTopology W.ProEt := AlgebraicGeometry.Scheme.ProEt.topology W
  let R : Sheaf J CommRingCat.{u + 1} := completedIntegralCommRingSheafUnrestricted l E W
  let S : Sheaf J CommRingCat.{u + 1} := completedIntegralCommRingSheafUnrestricted l L W
  let φ : R ⟶ S := integralCompletedScalarMap l E L ι W
  let F := integralOrdinaryScalar l E L ι W
  have hobj : ∀ A, F.obj A = SheafOfModules.changeOfRings.{u, u + 1, u + 1} φ A :=
    (integralOrdinaryScalarWitness l E L ι W).choose_spec.choose
  have hmap : ∀ {A B} (f : A ⟶ B), F.map f = eqToHom (hobj A) ≫
      SheafOfModules.changeOfRingsHom.{u, u + 1, u + 1} φ A f ≫ eqToHom (hobj B).symm := by
    intro A B f
    exact (integralOrdinaryScalarWitness l E L ι W).choose_spec.choose_spec.choose f
  have hs (A : integralTowerModules l E W) (U : W.ProEtᵒᵖ)
      (x : A.val.obj U) :
      ringedFiniteFreeScalarSection.{u + 1, u, u} J φ F hobj A U 1 x =
        integralOrdinaryTensorSection l E L ι W A U 1 x := by
    unfold ringedFiniteFreeScalarSection integralOrdinaryTensorSection
    have hη :=
      PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app.{u + 1, u,
        u + 1, u + 1} (J := J)
        (𝟙 (SheafOfModules.derivedChangeRingIndependentCoefficients J S).obj)
        (SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} φ A)
    with_unfolding_all exact (congrArg ((eqToHom (hobj A).symm).val.app U)
      (ConcreteCategory.congr_hom (congr_app hη U) _))
  obtain ⟨adj, δ, hu, hn, hcoords⟩ :=
    ringedFiniteFreeHomBaseChange_coordinates.{u + 1, u, u, u + 2}
      J φ d e F hobj hmap F.mapDerivedCategory F.mapDerivedCategoryFactors.hom
      (Functor.isLeftDerivedFunctor_of_inverts _ _ F.mapDerivedCategoryFactors)
      (scalarIntegralClosed l E W) (scalarIntegralClosed l L W)
      (scalarIntegralModels l E W) (scalarIntegralModels l L W)
      (scalarOrdinaryTensorChain l E L ι W) (scalarClosedTensor l E L ι W) (by
        intro P Q p q U x y
        simpa only [hs, scalarOrdinaryTensorChain] using
          (scalarOrdinaryTensorChain_existsUnique l E L ι W).exists.choose_spec
            P Q p q U x y) (by
        intro P Q hP hQ
        obtain ⟨hEP, hEQ, heq⟩ := scalarClosedTensor_allKFlat l E L ι W P Q hP hQ
        exact ⟨hEP, hEQ, (F.mapDerivedCategoryFactors.app P).isIso_hom,
          (F.mapDerivedCategoryFactors.app Q).isIso_hom, heq⟩)
  obtain ⟨pair, hpair, hderived, hadj⟩ :=
    SheafOfModules.exactScalarDerivedPair J φ F hobj hmap adj (by
      intro M V x
      rw [hu M V x]
      unfold ringedFiniteFreeScalarSection
      change ((eqToHom (hobj M).symm ≫ eqToHom (hobj M)).val.app V) _ = _
      rw [eqToHom_trans]
      rfl) δ hn
  refine ⟨pair, hpair, hderived, δ, hadj, ?_⟩
  intro M N
  obtain ⟨a, aN, β, ha, haN, hβ, hι⟩ := hcoords M N
  refine ⟨a, aN, β, ha, haN, ?_, ?_⟩
  · convert hβ using 1 <;> rfl
  · intro i
    have hi := hι i
    unfold scalarHomOrdinary coefficientBaseChangeHom
    convert hi using 1 <;> rfl


end FiniteScalar
end WeilConjectures.PodCoefficientDescent
