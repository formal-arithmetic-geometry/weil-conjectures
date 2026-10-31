/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FreeParameterEvaluation.FreeParameterEvaluationData
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import WeilConjectures.CategoryTheory.ModuleObjects.SixFunctors.ScalarExtensionMonoidal
public import WeilConjectures.CategoryTheory.ModuleObjects.SixFunctors.ScalarTensorCancellation
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MonoidalStructure
import WeilConjectures.AlgebraicGeometry.FreeParameterEvaluation.FreeParameterDegreeZeroData
import WeilConjectures.AlgebraicGeometry.QuotientChange.InternalPullNormalizationExistence
import all WeilConjectures.AlgebraicGeometry.QuotientChange.InternalScalarRestrictionMateNormalization
import WeilConjectures.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.CategoryTheory.SiteCoveringAxioms
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.CategoryTheory.Yoneda
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.CategoryTheory.Generator.Basic
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimit
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates

/-! # Canonical free-parameter evaluation data and coherence.
Source: Stacks 08J7, 07A6, 07A7 (blueprint: def-sfb-free-parameter-scalar-maps). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.FreeParameterEvaluation
attribute [local irreducible] Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  Functor.mapDerivedCategory Mod.monoidalCategory Mod.monoidalCategoryStruct
  Mod.monoidalClosed CategoryTheory.Sheaf.monoidalCategory
  AlgebraicGeometry.ProEtale.upperStarFromPoint
attribute [local instance 20000]
  GrothendieckTopology.monoidalCategory_sheaf_of_essentiallySmall
  GrothendieckTopology.braidedCategory_sheaf_of_essentiallySmall
  AlgebraicGeometry.ProEtale.sheafMonoidalCategory
  AlgebraicGeometry.ProEtale.sheafBraidedCategory

section CachedInstances
variable (A : Profinite.CondensedRing.{u}) [IsCommMonObj A.X]
variable (T : Scheme.{u})
private theorem schemeFour : ∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ (Modules A T)),
    GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄ := inferInstance
private theorem schemeGood12 : ∀ (X₁ X₂ X₃ : GradedObject ℤ (Modules A T)),
    GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃ := inferInstance
private theorem schemeGood23 : ∀ (X₁ X₂ X₃ : GradedObject ℤ (Modules A T)),
    GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃ := inferInstance
private theorem schemeLeft : ∀ (X : Modules A T),
    PreservesColimitsOfShape ℤ ((curriedTensor (Modules A T)).obj X) := inferInstance
private theorem schemeRight : ∀ (X : Modules A T),
    PreservesColimitsOfShape ℤ ((curriedTensor (Modules A T)).flip.obj X) := inferInstance
end CachedInstances
attribute [local instance] pointFour pointGood12 pointGood23 pointLeft pointRight
  schemeFour schemeGood12 schemeGood23 schemeLeft schemeRight

variable (R : Profinite.CondensedRing.{u}) [IsCommMonObj R.X]

section Scalars
variable (S : Profinite.CondensedRing.{u}) [IsCommMonObj S.X]
  (φ : R.X ⟶ S.X) [IsMonHom φ]

/-- Exact coefficient restriction at the condensed point.
Source: Stacks 03D2 (blueprint: def-sfb-free-parameter-scalar-maps). -/
abbrev restrictPoint : PointModules S ⥤ PointModules R := Mod.comap φ

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- Exact coefficient restriction on the small pro-etale site.
Source: Stacks 03D2 (blueprint: def-sfb-free-parameter-scalar-maps). -/
abbrev restrictScheme (X : Scheme.{u}) : Modules S X ⥤ Modules R X :=
  Mod.comap (coefficientMap φ X)

/-- The action identification for point pullback and restriction of scalars.
Source: Stacks 03D2 (blueprint: def-sfb-free-parameter-scalar-maps). -/
def restrictPointPullD (X : Scheme.{u}) :
    (restrictPoint R S φ).mapDerivedCategory ⋙ pointPullD R X ≅
      pointPullD S X ⋙ (restrictScheme R S φ X).mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso ((upperStarFromPoint X).mapModComapIso φ) ≪≫
    Functor.mapDerivedCategoryCompIso _ _

/-- K-flat derived extension of scalars, with its recorded scalar adjunction.
Source: Stacks 07A6 (blueprint: def-sfb-free-parameter-scalar-maps). -/
abbrev extendPoint := (Mod.extendScalars φ).leftDerivedFunctor

/-- The derived tensorator of scalar extension, normalized by scalar units at the
ordinary level. This uses preservation of flat objects, never exact scalar extension.
Source: Stacks 07A4 (blueprint: def-sfb-free-parameter-scalar-maps). -/
def scalarTensor (K L : DerivedCategory (PointModules R)) :
    (extendPoint R S φ).obj K ⊗ (extendPoint R S φ).obj L ≅
      (extendPoint R S φ).obj (K ⊗ L) :=
  letI := (Mod.exists_extendScalarsMonoidal φ).choose
  letI := Mod.extendScalars_preservesFlat φ
  letI := (Mod.extendRestrictAdjunction φ).isLeftAdjoint
  letI := (Mod.extendScalars φ).leftDerivedFunctorMonoidal
  Functor.Monoidal.μIso (extendPoint R S φ) K L

attribute [local irreducible] freeScalarMap freeGeneratorScalar

omit [IsCommMonObj S.X] in
set_option backward.defeqAttrib.useBackward false
attribute [local irreducible] DerivedCategory instCategoryDerivedCategory
  DerivedCategory.singleFunctors Profinite.CondensedAction.InternalBar.free
  Mod.comap Mod.extendScalars Mod.derivedExtendMapDerivedCategoryAdjunction
  CondensedRing.upperStar CondensedRing.derivedComapUpperStarIso
  CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory

attribute [local irreducible] scalarTensor restrictPointPullD projectionAdjunction

/-- Canonical scalar/pullback comparison: transpose pullback of the scalar unit
through the action identification. This definition precedes its isomorphism claim.
Source: Stacks 07A6 and 0D6D (blueprint: def-sfb-free-parameter-scalar-maps). -/
def scalarPullComparison {Y X : Scheme.{u}} (f : Y ⟶ X)
    (M : DerivedCategory (Modules R X)) :
    (Mod.extendScalars (coefficientMap φ Y)).leftDerivedFunctor.obj
      ((CondensedRing.upperStar R.X f).mapDerivedCategory.obj M) ⟶
    (CondensedRing.upperStar S.X f).mapDerivedCategory.obj
      ((Mod.extendScalars (coefficientMap φ X)).leftDerivedFunctor.obj M) :=
  ((mateEquiv
      (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap φ X))
      (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap φ Y))).symm
    (TwoSquare.mk _ _ _ _ (CondensedRing.derivedComapUpperStarIso φ f).inv)).natTrans.app M

attribute [local irreducible] scalarPullComparison

/-- Scalar extension commutes with exact geometric inverse image in this normalized form.
Source: Stacks 07A4 and 0D6D, node proof step 9
(blueprint: def-sfb-free-parameter-scalar-maps).
Proof: choose a K-flat resolution of M. Geometric inverse image is exact, strong
monoidal and preserves flat objects, so its termwise image computes the pulled
K-flat tensor. The balanced scalar tensor comparison is an isomorphism on each
term, normalized by x ↦ 1 tensor x. It commutes with differentials and descends to
the derived isomorphism. Scalar transposition identifies it with the displayed
scalar-unit formula, so the specified map itself is invertible without flatness
of the coefficient map. -/
@[instance] theorem scalarPullComparison_isIso {Y X : Scheme.{u}} (f : Y ⟶ X)
    (M : DerivedCategory (Modules R X)) : IsIso (scalarPullComparison R S φ f M) := by
  -- Keep the auxiliary ringed-site localization instance local to this call.
  obtain ⟨b, hb⟩ : ∃ b : QuotientChange.D φ X ⋙ QuotientChange.L S.X f ≅
      QuotientChange.L R.X f ⋙ QuotientChange.D φ Y,
      QuotientChange.PullNormalized φ f b := by
    let (A : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
        [MonObj A] [IsCommMonObj A] (T : Scheme.{u}) :
        HasDerivedCategory.{u + 1} (ModuleRingedComparison.modules A T) :=
      @HasDerivedCategory.ofIsGrothendieckAbelian _ _ _
        (SheafOfModules.isGrothendieckAbelianOfUniverses.{u + 1, u, u + 1, 0}
          (Scheme.ProEt.topology T) _)
    exact QuotientChange.internal_pull_normalization_exists φ f
  let eR : QuotientChange.L R.X f ≅
      (CondensedRing.upperStar R.X f).mapDerivedCategory := by
    unfold QuotientChange.L CondensedRing.moduleObjectDerivedPullback
    exact CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory R.X f
  let eS : (CondensedRing.upperStar S.X f).mapDerivedCategory ≅
      QuotientChange.L S.X f := by
    unfold QuotientChange.L CondensedRing.moduleObjectDerivedPullback
    exact (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory S.X f).symm
  let a := (mateEquiv (QuotientChange.scalarAdj φ X)
    (QuotientChange.scalarAdj φ Y)).symm
      (TwoSquare.mk _ _ _ _ (CondensedRing.derivedComapUpperStarIso φ f).inv)
  -- Transport between exact termwise and left-derived geometric pullback.
  have he : (a.whiskerTop eR.hom).whiskerBottom eS.hom =
      (mateEquiv (QuotientChange.scalarAdj φ X)
        (QuotientChange.scalarAdj φ Y)).symm
        (TwoSquare.mk _ _ _ _ (QuotientChange.normalizationRestrictionPull φ f).inv) := by
    apply (mateEquiv (QuotientChange.scalarAdj φ X)
      (QuotientChange.scalarAdj φ Y)).injective
    simp only [a, mateEquiv_whiskerTop_whiskerBottom, Equiv.apply_symm_apply]
    ext M
    delta QuotientChange.normalizationRestrictionPull
    dsimp only [eR, eS, id, TwoSquare.whiskerRight, TwoSquare.whiskerLeft]
    delta QuotientChange.L CondensedRing.moduleObjectDerivedPullback
    dsimp only [TwoSquare.mk, TwoSquare.natTrans, QuotientChange.V, QuotientChange.V₀]
    simp only [Iso.trans_inv, Functor.isoWhiskerRight_inv, Functor.isoWhiskerLeft_inv,
      Iso.symm_inv, Iso.symm_hom, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app, Category.assoc]
  have hi : IsIso (((a.whiskerTop eR.hom).whiskerBottom eS.hom).natTrans.app M) := by
    rw [he, ← QuotientChange.normalized_inverse φ f b hb]
    infer_instance
  simp only [TwoSquare.whiskerTop, TwoSquare.whiskerBottom,
    NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Category.assoc] at hi
  have : IsIso (a.natTrans.app M) := by
    have := IsIso.of_isIso_comp_left
      ((QuotientChange.D φ Y).map (eR.hom.app M))
      (a.natTrans.app M ≫
        eS.hom.app ((QuotientChange.D φ X).obj M))
    exact IsIso.of_isIso_comp_right _
      (eS.hom.app ((QuotientChange.D φ X).obj M))
  dsimp only [a] at this
  delta QuotientChange.scalarAdj QuotientChange.D at this
  dsimp only [id] at this
  unfold scalarPullComparison
  exact this

end Scalars

end AlgebraicGeometry.ProEtale.FreeParameterEvaluation
