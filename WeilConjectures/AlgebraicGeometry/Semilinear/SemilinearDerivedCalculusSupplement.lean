/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SemilinearSystemModels
public import WeilConjectures.SixFunctors.Coefficient.CoefficientRingedSequenceSiteSupplement
public import WeilConjectures.SixFunctors.CoefficientClosedStructure.CoefficientRingedTensorHomModelSupplement
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import WeilConjectures.AlgebraicGeometry.CoefficientHomRepresentativeEvaluation
public import WeilConjectures.Algebra.Homology.DerivedInternalHomOfUniverses
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import WeilConjectures.SixFunctors.Etale.Derived.Hom
public import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Generator.Basic
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMapOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplex
public import WeilConjectures.Algebra.Homology.HomComplexSectionsQuasiIsoOfUniverses
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimit
public import Mathlib.Algebra.Category.Grp.Abelian
public import WeilConjectures.Algebra.Homology.HomComplexSectionsDerivedNaturalityOfUniverses
public import WeilConjectures.Algebra.Homology.RhomIntoKInjectiveLocal
public import WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalizedOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import WeilConjectures.Algebra.Homology.LocalizedRestrictionAdjunctionOfUniverses
public import WeilConjectures.Algebra.Homology.LocalizedRestrictionExtensionExistsOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
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
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import WeilConjectures.Algebra.Homology.QuasiIsoOfSectionsOfUniverses
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.Algebra.Homology.Functor
public import WeilConjectures.Algebra.Homology.HomComplexComponents
public import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMap
public import WeilConjectures.Algebra.Homology.HomTensorDegreewiseEquation
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
public import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import Mathlib.CategoryTheory.Limits.Final
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.CategoryTheory.Sites.CoverPreserving
public import WeilConjectures.CategoryTheory.AlgebraicInverseImage
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Sites.Whiskering
public import WeilConjectures.CategoryTheory.LocalizedModuleExactForSystems
public import WeilConjectures.Algebra.Homology.SmoothPurity.LocalizedModuleExactIndependent
public import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
public import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.CategoryTheory.Sites.CoverLifting
import Mathlib.CategoryTheory.Sites.PreservesLocallyBijective
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.PushforwardZeroMonoidal
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification

public import WeilConjectures.AlgebraicGeometry.SemilinearDerivedCalculus

/-! # Ordinary derived semilinear sections

Source: Zheng, Six Operations and Lefschetz--Verdier, Construction 4.1, Lemma 4.10 and Proposition
  4.17;
Stacks Project, Tags 0941, 079P, 06YS, 06YY, 07A4, 07A6 and 08J7--08JB
(blueprint: def-coef-semilinear-derived-calculus).

The categories below are module sheaves on the actual vertical sequence site and their
ordinary unbounded derived categories. All comparisons have specified sources, targets
and equations; there are no free proposition-valued parameters.

## Main definitions and statements

- `Systems`, `DS`: strict semilinear systems and their ordinary derived category.
- `Data`, `Geometry`, `OpenSystems`: the coefficient, geometric and localized calculus.
- `TensorComparisonModel`, `InverseTensorPure`: representative and pure-tensor normalization.
- `semilinearDerivedSections`: existence of the complete ordinary-derived calculus.
- `evaluation_mate`: compatibility of specified adjunction transposes with evaluation.
-/

@[expose] public noncomputable section
set_option autoImplicit false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe c v r c₂ v₂ k

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.MonoidalCategory
open scoped ChangeOfRings

@[irreducible] private def restrictionSheafificationMap
    {D : Type c} [Category.{v} D] {E : Type c₂} [Category.{v₂} E]
    {K : GrothendieckTopology D} {L : GrothendieckTopology E}
    [HasSheafify K AddCommGrpCat.{r}] [K.WEqualsLocallyBijective AddCommGrpCat.{r}]
    [HasSheafify L AddCommGrpCat.{r}] [L.WEqualsLocallyBijective AddCommGrpCat.{r}]
    {F : D ⥤ E} [F.IsContinuous K L]
    {S : Sheaf K RingCat.{r}} {R : Sheaf L RingCat.{r}}
    (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{r} K L).obj R)
    (P : PresheafOfModules.{r} R.obj) :
    (PresheafOfModules.sheafification.{r} (R := S) (𝟙 _)).obj
      ((PresheafOfModules.pushforward φ.hom).obj P) ⟶
        (SheafOfModules.pushforward.{r} φ).obj
          ((PresheafOfModules.sheafification.{r} (R := R) (𝟙 _)).obj P) :=
  (PresheafOfModules.sheafificationHomEquiv.{r} (𝟙 _)).symm
    ((PresheafOfModules.pushforward φ.hom).map
      ((PresheafOfModules.sheafificationAdjunction.{r} (R := R) (𝟙 _)).unit.app P))

namespace WeilConjectures.SemilinearSections

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [ambientSmall : EssentiallySmall.{max c v r} C]
  (B : ℕ → Sheaf J CommRingCat.{max c v r})
  (τ : ∀ n : ℕ, B (n + 1) ⟶ B n)

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
@[irreducible] private def restrictionTensorPresheafIso
    {D : Type c} [Category.{v} D] {E : Type c₂} [Category.{v₂} E]
    {F : D ⥤ E} {R : Eᵒᵖ ⥤ CommRingCat.{r}} {S : Dᵒᵖ ⥤ CommRingCat.{r}}
    (φ : S ⋙ forget₂ CommRingCat RingCat ⟶ (F.op ⋙ R) ⋙ forget₂ CommRingCat RingCat)
    (hφ : ∀ U, IsIso (φ.app U))
    (M N : PresheafOfModules.{r} (R ⋙ forget₂ CommRingCat RingCat)) :
    let G := PresheafOfModules.pushforward (F := F)
      (R := R ⋙ forget₂ CommRingCat RingCat)
      (S := S ⋙ forget₂ CommRingCat RingCat) φ
    PresheafOfModules.Monoidal.tensorObj (R := S) (G.obj M) (G.obj N) ≅
      G.obj (PresheafOfModules.Monoidal.tensorObj (R := R) M N) := by
  let G := PresheafOfModules.pushforward (F := F)
    (R := R ⋙ forget₂ CommRingCat RingCat)
    (S := S ⋙ forget₂ CommRingCat RingCat) φ
  letI : G.LaxMonoidal := PresheafOfModules.pushforwardLaxMonoidal φ
  let f := Functor.LaxMonoidal.μ G M N
  have h (U : Dᵒᵖ) : IsIso (f.app U) := by
    dsimp only [f, G]
    erw [PresheafOfModules.pushforward_μ_app φ M N U]
    apply restrictScalars_mu_isIso
    have := hφ U
    exact ConcreteCategory.bijective_of_isIso (φ.app U)
  exact PresheafOfModules.isoMk (fun U ↦ @asIso _ _ _ _ (f.app U) (h U))
    (fun {_ _} i ↦ f.naturality i)

attribute [local irreducible] systemRing ringPresheaf rings
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
@[irreducible] private def evaluationTensorPresheafIso (n : ℕ)
    (M N : Systems.{c, v, max c v r} J B τ) :
    PresheafOfModules.Monoidal.tensorObj (R := (B n).obj)
      ((evaluation.{c, v, max c v r} J B τ n).obj M).val
      ((evaluation.{c, v, max c v r} J B τ n).obj N).val ≅
      (PresheafOfModules.pushforward
        (eqToHom (evaluation_ring.{c, v, max c v r} J B τ n).symm).hom).obj
          (PresheafOfModules.Monoidal.tensorObj
            (R := (systemRing.{c, v, max c v r} J B τ).obj) M.val N.val) := by
  dsimp only [evaluation, SheafOfModules.pushforward]
  exact restrictionTensorPresheafIso
    (F := Prod.sectR n C) (R := (systemRing.{c, v, max c v r} J B τ).obj)
    (S := (B n).obj) (eqToHom (evaluation_ring.{c, v, max c v r} J B τ n).symm).hom
    (fun U ↦ by
      let φ := eqToHom (evaluation_ring.{c, v, max c v r} J B τ n).symm
      have : IsIso φ.hom := inferInstance
      exact NatIso.isIso_app_of_isIso φ.hom U) M.val N.val

@[irreducible] private def evaluationTensorComparison (n : ℕ)
    (M N : Systems.{c, v, max c v r} J B τ) :
    ordinaryTensor.{c, v, r} J (B n) ((evaluation.{c, v, max c v r} J B τ n).obj M)
        ((evaluation.{c, v, max c v r} J B τ n).obj N) ⟶
      (evaluation.{c, v, max c v r} J B τ n).obj
        (ordinaryTensor.{c, v, r} (coefficientSequenceTopology J)
          (systemRing.{c, v, max c v r} J B τ) M N) := by
  let R := systemRing.{c, v, max c v r} J B τ
  let φ := eqToHom (evaluation_ring.{c, v, max c v r} J B τ n).symm
  let P := PresheafOfModules.Monoidal.tensorObj (R := R.obj) M.val N.val
  letI := SheafOfModules.isMonoidal_W_independentCoefficients.{c, v, max c v r} (B n)
  letI := SheafOfModules.isMonoidal_W_independentCoefficients.{c, v, max c v r} R
  exact (SheafOfModules.tensorObjIsoSheafification.{v, c, max c v r}
      ((evaluation.{c, v, max c v r} J B τ n).obj M)
      ((evaluation.{c, v, max c v r} J B τ n).obj N)).hom ≫
    (PresheafOfModules.sheafification.{max c v r} (R := ring.{c, v, max c v r} J (B n))
      (𝟙 _)).map (evaluationTensorPresheafIso.{c, v, r} J B τ n M N).hom ≫
    restrictionSheafificationMap.{c, v, max c v r, c, v} φ P ≫
    (evaluation.{c, v, max c v r} J B τ n).map
      (SheafOfModules.tensorObjIsoSheafification.{v, c, max c v r} M N).inv

@[irreducible] private def evaluationTensorIso (n : ℕ)
    (M N : Systems.{c, v, max c v r} J B τ) :
    (evaluation.{c, v, max c v r} J B τ n).obj
        (ordinaryTensor.{c, v, r} (coefficientSequenceTopology J)
          (systemRing.{c, v, max c v r} J B τ) M N) ≅
      ordinaryTensor.{c, v, r} J (B n)
        ((evaluation.{c, v, max c v r} J B τ n).obj M)
        ((evaluation.{c, v, max c v r} J B τ n).obj N) :=
  (@asIso _ _ _ _ (evaluationTensorComparison.{c, v, r} J B τ n M N)
    (evaluationTensorComparison_isIso.{c, v, r} J B τ n M N)).symm

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

attribute [local irreducible] ordinaryEvaluationTensor

namespace Data

variable (A : Data.{c, v, r} J B τ)

end Data

section ScalarSystems

variable (F : ℕ → Sheaf J CommRingCat.{max c v r})
  (σ : ∀ n : ℕ, F (n + 1) ⟶ F n) (α : ∀ n : ℕ, B n ⟶ F n)
  (hα : ∀ n : ℕ, α (n + 1) ≫ σ n = τ n ≫ α n)

end ScalarSystems

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local semireducible] systemRing ringPresheaf rings

section OpenLocalization

variable (U : C)

attribute [instance] openSite_continuous

attribute [instance] OpenSystems.extensionAdditive OpenSystems.extensionLimits
  OpenSystems.extensionColimits

end OpenLocalization

end WeilConjectures.SemilinearSections
