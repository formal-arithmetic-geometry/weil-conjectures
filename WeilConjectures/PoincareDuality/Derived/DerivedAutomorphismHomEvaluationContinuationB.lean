/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.SmoothPurity.Completed.CompletedPullbackTensorComparison
public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorIso
public import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearDerivedSections
public import WeilConjectures.AlgebraicGeometry.Iso.IsoSectionwiseInverseImage

import Mathlib.CategoryTheory.Adjunction.Additive
import all WeilConjectures.SmoothPurity.Supporting.IsomorphismReductionTower
import WeilConjectures.AlgebraicGeometry.Pur.PurInverseImageTensorHom
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
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.CategoryTheory.Sites.Equivalence
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
import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMap
import WeilConjectures.CategoryTheory.RingedDerivedComparisons.RingedDerivedMonoidalComparisons
public import WeilConjectures.SixFunctors.CoefficientClosedStructure.CoefficientRingedTensorHomModelSupplement
public import WeilConjectures.AlgebraicGeometry.CoefficientHomRepresentativeEvaluation
public import WeilConjectures.Algebra.Homology.HomComplexComponents
public import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMap
public import WeilConjectures.Algebra.Homology.HomTensorDegreewiseEquation
import WeilConjectures.TraceFormula.Supporting.FiniteFreeCompletedScalarComparison
import WeilConjectures.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
import WeilConjectures.CategoryTheory.Ringed.RingedStrictTowerHomotopyLimitOfUniverses
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import WeilConjectures.Algebra.Homology.KInjectiveProductsTermwise
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Products
import WeilConjectures.Algebra.Homology.TowerEvaluationKInjective
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.CategoryTheory.Sites.Equivalence
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
import Mathlib.CategoryTheory.Adjunction.Evaluation
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
import Mathlib.Algebra.BigOperators.Ring.Finset
public import WeilConjectures.SmoothPurity.Supporting.CoefDerivedSystemEvaluationCalculus
public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom
import WeilConjectures.PoincareDuality.PodCoefficientDescent.PodReindexingHomCoefficientDescent
import WeilConjectures.SmoothPurity.CompletedOperations.CompletedOperationTowerSubstitution
import WeilConjectures.SixFunctors.Supporting.ConstantCompletionEquivalence
import WeilConjectures.AlgebraicGeometry.Weil.WeilCompletedTensorReflector
public import WeilConjectures.SmoothPurity.Sf.SfRationalizationKaroubi
public import WeilConjectures.SmoothPurity.GeneralAlgebraicallyClosedCoefficients.GeneralAlgebraicallyClosedCoefficients
import WeilConjectures.SmoothPurity.Pur.PurNormalizedReconstructionAdjunctionCalculus
import WeilConjectures.SmoothPurity.Sf.SfDerivedCompleteLegacyComparison

import all WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorIso
import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorIso
import all WeilConjectures.PoincareDuality.PodReindexingCoherence.PodReindexingEvaluationShiftComposition
import all WeilConjectures.AlgebraicGeometry.Integral.IntegralInverseImageComparisonComposition

public import WeilConjectures.PoincareDuality.Pod.PodHomComplexShiftRepresentatives
public import WeilConjectures.SixFunctors.Supporting.DerivedAutomorphismHomEvaluationContinuationA

/-! # Internal Hom and evaluation under coefficient-site isomorphisms

This file records the composition comparison for completed inverse image along isomorphisms
of schemes: for isomorphisms `h : Z ⟶ X` and `g : X ⟶ Y`, completed inverse image along
`h ≫ g` agrees with the composite of the completed inverse images, both on modules and on
derived categories.

## Main definitions

* `podCompletedModuleComp`: the identity-on-sections composition comparison for modules.
* `podCompletedDerivedComp`: the induced comparison on derived categories.

## Main statements

* `podCompletedModuleComp_existsUnique`: the composition comparison exists and is unique.

## Implementation details

Completed inverse image is constructed from all coefficient projections, so two completed
coefficient transports agree as soon as their finite projections agree.

## References

* [Stacks Project, Tag 0GMX], [Stacks Project, Tag 00WX]
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v a b c d
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures

attribute [local irreducible] AlgebraicGeometry.Scheme.residueField
  HasDerivedCategory.standard
attribute [-instance] isoReductionAbSheafify isoReductionAbBijective isoReductionSiteSmall

section SignedShifts
attribute [local irreducible] homComplexFunctor
universe r s t w
variable {C : Type s} [Category.{t} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max s t r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max s t r}]
  (A : Sheaf J CommRingCat.{max s t r})
  [HasDerivedCategory.{w} (PodModules.{r, s, t} J A)]

end SignedShifts

section FiniteCoherence
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {X Y Z : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
  [∀ x : X, Invertible (l : X.residueField x)]
  [∀ y : Y, Invertible (l : Y.residueField y)]

omit [IsIso g] in
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
attribute [local irreducible] finiteIntrinsicClosed podFiniteHomComparison

end FiniteCoherence

section IntegralShiftCoherence
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
  [∀ x : X, Invertible (l : X.residueField x)]
  [∀ y : Y, Invertible (l : Y.residueField y)]

end IntegralShiftCoherence

section IntegralComposition
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {X Y Z : Scheme.{u}} (g : X ⟶ Y) [IsIso g] (h : Z ⟶ X) [IsIso h]

omit [IsIso g] [IsIso h] in
/-- A restriction along an `eqToHom` arrow is the identity, up to `HEq`. -/
private theorem presheafOfModules_map_heq_of_eq {C : Type*} [Category C]
    {R : Cᵒᵖ ⥤ RingCat.{u + 1}} (M : PresheafOfModules.{u + 1} R) {A B : Cᵒᵖ}
    (f : A ⟶ B) (hf : ∃ p : A = B, f = eqToHom p) (x : M.obj A) :
    HEq (M.map f x) x := by
  obtain ⟨rfl, rfl⟩ := hf
  simp

omit [IsIso g] [IsIso h] in
/-- The completed coefficient transport is the published completed coefficient map. -/
private theorem podCompletedRingMap_eq_inverseImage {V W : Scheme.{u}} (k : V ⟶ W) [IsIso k] :
    podCompletedRingMap l E k = ProEtale.inverseImageCompletedCoefficientMap l E k := by
  apply limit.hom_ext
  intro n
  rw [podCompletedRingMap, limit.lift_π, ProEtale.inverseImageCompletedCoefficientMap,
    limit.lift_π]
  rfl

/-- There is a unique isomorphism between completed inverse image along `h ≫ g` and the
composite of completed inverse images along `g` and `h` which is the identity on all local
sections. -/
theorem podCompletedModuleComp_existsUnique :
    ∃! e : podCompletedModuleInverseImage l E (h ≫ g) ≅
        podCompletedModuleInverseImage l E g ⋙ podCompletedModuleInverseImage l E h,
      ∀ (M : integralTowerModules l E Y) (U : Z.ProEt)
        (x : ((podCompletedModuleInverseImage l E (h ≫ g)).obj M).val.obj (op U)),
        HEq (((e.hom.app M).val.app (op U)) x) x := by
  let d : proEtaleIsoPostcompose (h ≫ g) ≅
      proEtaleIsoPostcompose h ⋙ proEtaleIsoPostcompose g :=
    MorphismProperty.Over.mapComp (Q := ⊤)
      (inferInstance : WeaklyEtale h) (inferInstance : WeaklyEtale g)
  let : (proEtaleIsoPostcompose h ⋙ proEtaleIsoPostcompose g).IsContinuous
      (ProEt.topology Z) (ProEt.topology Y) :=
    Functor.isContinuous_comp _ _ (ProEt.topology Z) (ProEt.topology X) (ProEt.topology Y)
  let R := completedIntegralCoefficientSheafUnrestricted l E Y
  let T := Functor.sheafPushforwardContinuousIso d RingCat.{u + 1}
    (ProEt.topology Z) (ProEt.topology Y)
  have hc := ProEtale.completedComposition l E h g
  rw [← podCompletedRingMap_eq_inverseImage l E g, ← podCompletedRingMap_eq_inverseImage l E h,
    ← podCompletedRingMap_eq_inverseImage l E (h ≫ g)] at hc
  have hring : inv (podCompletedRingMap l E (h ≫ g)) ≫ T.hom.app R =
      inv (podCompletedRingMap l E h) ≫
        (isoSectionwiseInverseImage h RingCat.{u + 1}).map
          (inv (podCompletedRingMap l E g)) := by
    rw [← cancel_mono ((isoSectionwiseInverseImage h RingCat.{u + 1}).map
      (podCompletedRingMap l E g) ≫ podCompletedRingMap l E h), Category.assoc,
      Category.assoc, ← Functor.map_comp_assoc, IsIso.inv_hom_id,
      CategoryTheory.Functor.map_id, Category.id_comp, IsIso.inv_hom_id]
    erw [hc]
    rw [← Category.assoc (T.hom.app R)]
    erw [T.hom_inv_id_app]
    rw [Category.id_comp, IsIso.inv_hom_id]
  have hd (U : Z.ProEt) : ∃ p, (d.inv.app U).op = eqToHom p := by
    refine ⟨congrArg op (Functor.congr_obj (MorphismProperty.Over.map_comp (Q := ⊤)
      (inferInstance : WeaklyEtale h) (inferInstance : WeaklyEtale g)) U), ?_⟩
    apply Quiver.Hom.unop_inj
    rw [Quiver.Hom.unop_op, eqToHom_unop]
    apply MorphismProperty.Over.Hom.ext
    simp [d]
    rfl
  let e := SheafOfModules.pushforwardNatIso (inv (podCompletedRingMap l E (h ≫ g))) d.symm ≪≫
    SheafOfModules.pushforwardCongr hring ≪≫
    (SheafOfModules.pushforwardComp (inv (podCompletedRingMap l E h))
      (inv (podCompletedRingMap l E g))).symm
  refine ⟨e, fun M U x ↦ ?_, fun e' he' ↦ ?_⟩
  · exact presheafOfModules_map_heq_of_eq M.val (d.inv.app U).op (hd U) x
  · apply Iso.ext
    ext M U x
    exact eq_of_heq ((he' M U.unop x).trans
      (presheafOfModules_map_heq_of_eq M.val (d.inv.app U.unop).op (hd U.unop) x).symm)

/-- The unique identity-on-sections completed composition comparison. -/
def podCompletedModuleComp := (podCompletedModuleComp_existsUnique l E g h).exists.choose

/-- The composition comparison for derived completed inverse image, obtained by deriving
`podCompletedModuleComp`. -/
def podCompletedDerivedComp : podCompletedDerivedInverseImage l E (h ≫ g) ≅
    podCompletedDerivedInverseImage l E g ⋙ podCompletedDerivedInverseImage l E h :=
  letI := podCompletedModuleAdditive l E g
  letI := podCompletedModuleAdditive l E h
  letI := podCompletedModuleAdditive l E (h ≫ g)
  letI := podCompletedModuleLimits l E g
  letI := podCompletedModuleLimits l E h
  letI := podCompletedModuleLimits l E (h ≫ g)
  letI := podCompletedModuleColimits l E g
  letI := podCompletedModuleColimits l E h
  letI := podCompletedModuleColimits l E (h ≫ g)
  Functor.mapDerivedCategoryNatIso (podCompletedModuleComp l E g h) ≪≫
    (Functor.mapDerivedCategoryCompIso (podCompletedModuleInverseImage l E g)
      (podCompletedModuleInverseImage l E h)).symm

end IntegralComposition

section SystemFibers
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]

variable [∀ x : X, Invertible (l : X.residueField x)]
  [∀ y : Y, Invertible (l : Y.residueField y)]

end SystemFibers

section ArgumentFirstStages
attribute [local irreducible] pullbackTensorBraiding canonicalFinitePullbackTensor
  finiteIntrinsicClosed finiteIntrinsicTensorModels podFiniteHomComparison
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
  [∀ x : X, Invertible (l : X.residueField x)]
  [∀ y : Y, Invertible (l : Y.residueField y)]

end ArgumentFirstStages

section ArgumentFirstCommon
variable (l : ℕ) [Fact l.Prime] (Ω : Type v) [Field Ω]
  [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
  {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
  [∀ x : X, Invertible (l : X.residueField x)]
  [∀ y : Y, Invertible (l : Y.residueField y)]

end ArgumentFirstCommon

section FieldComposition
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {X Y Z : Scheme.{u}} (g : X ⟶ Y) [IsIso g] (h : Z ⟶ X) [IsIso h]
  [∀ x : X, Invertible (l : X.residueField x)]
  [∀ y : Y, Invertible (l : Y.residueField y)]
  [∀ z : Z, Invertible (l : Z.residueField z)]

end FieldComposition

section CommonComposition
variable (l : ℕ) [Fact l.Prime] (Ω : Type v) [Field Ω]
  [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
  {X Y Z : Scheme.{u}} (g : X ⟶ Y) [IsIso g] (h : Z ⟶ X) [IsIso h]
  [∀ x : X, Invertible (l : X.residueField x)]
  [∀ y : Y, Invertible (l : Y.residueField y)]
  [∀ z : Z, Invertible (l : Z.residueField z)]

end CommonComposition

section RestrictedShiftMaps
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
  [∀ x : X, Invertible (l : X.residueField x)]
  [∀ y : Y, Invertible (l : Y.residueField y)]

end RestrictedShiftMaps

section CommonShiftImages
open GeneralAlgebraicallyClosedCoefficients AlgebraicallyClosedCoefficients
variable (l : ℕ) [Fact l.Prime] (Ω : Type v) [Field Ω]
  [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
  {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
  [∀ x : X, Invertible (l : X.residueField x)]
  [∀ y : Y, Invertible (l : Y.residueField y)]

end CommonShiftImages

end WeilConjectures
