/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleTensorComparison.ProEtaleInverseImageTensorComparisonSupplement
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.Ringed.ProEtaleRingedOpenClosed
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Submission.WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
public import Submission.WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import Submission.WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import Submission.WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits

import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleAbelianClosedCounit
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleModuleInverseImageUnitComparison
import Submission.WeilConjectures.Algebra.Homology.SixFunctors.LocalizedSiteTensorRestrictionSupplement
import all Submission.WeilConjectures.AlgebraicGeometry.ProEtaleModuleInverseImageCanonicalUnit
import all Submission.WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
import all Submission.WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import all Submission.WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import all Mathlib.AlgebraicGeometry.Sites.Proetale
import all Mathlib.CategoryTheory.Sites.ConstantSheaf
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all Submission.WeilConjectures.CategoryTheory.RingedSiteModules
import all Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import all Mathlib.CategoryTheory.Sites.Equivalence
import all Submission.WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
import all Submission.WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Category.ModuleCat.AB
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import all Mathlib.Algebra.Homology.ShortComplex.ShortExact
import all Mathlib.CategoryTheory.Sites.Sheafification
import all Submission.WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
import all Mathlib.CategoryTheory.Monoidal.CommGrp_
import all Mathlib.CategoryTheory.Monoidal.Ring
import all Mathlib.CategoryTheory.Adjunction.Limits
import all Submission.WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
import all Submission.WeilConjectures.AlgebraicGeometry.ProEtaleModelRingPresentation
import all Submission.WeilConjectures.CategoryTheory.SheafPullbackUnitPresentation
import all Mathlib.CategoryTheory.Sites.Pullback
import all Mathlib.CategoryTheory.Sites.CartesianMonoidal
import all Submission.WeilConjectures.CategoryTheory.SheafPullbackForgetComparison
import all Submission.WeilConjectures.CategoryTheory.ModuleInverseImageAdjunction
import all Submission.WeilConjectures.CategoryTheory.ModuleInverseImageAction
import all Mathlib.Algebra.Category.Ring.Limits
import all Submission.WeilConjectures.CategoryTheory.ModuleInverseImageActionOfPresentations
import all Submission.WeilConjectures.AlgebraicGeometry.EtaleInverseImageModuleAdjunction
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-!
# Underived projection for a closed pro-etale immersion

Source: Stacks Project, proetale.tex, Tags 09AA and 09AH, and sites-modules.tex,
Section 03EK and Tag 03EL. The projection consequence is agent-formulated.
(blueprint: lem-weil-pbc-proetale-closed-underived-projection).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtaleTensorComparison

namespace AlgebraicGeometry.ProEtaleClosedProjection

/-- The ring sheaf B regarded as an R-module through the given ring morphism.
Source: Stacks, Section 03EK; the coefficient clause
(blueprint: lem-weil-pbc-proetale-closed-underived-projection). -/
noncomputable abbrev coefficientModule {X : Scheme.{u}} {R B : Rings X} (a : R ⟶ B) :
    Modules R :=
  (restrict a).obj (SheafOfModules.unit (proEtaleModuleCoefficients B))

private noncomputable def regularInverseIso {X Z : Scheme.{u}} (i : Z ⟶ X)
    (B : Rings X) : (inverse i B).obj (SheafOfModules.unit (proEtaleModuleCoefficients B)) ≅
      SheafOfModules.unit (proEtaleModuleCoefficients (inverseRing i B)) := by
  let : (AsSmall.down : proEtaleSiteModel X ⥤ X.ProEt).IsEquivalence :=
    inferInstanceAs (AsSmall.equiv.{u, u + 1, u + 1} (C := X.ProEt)).inverse.IsEquivalence
  let : (AsSmall.up : Z.ProEt ⥤ proEtaleSiteModel Z).IsEquivalence :=
    inferInstanceAs (AsSmall.equiv.{u, u + 1, u + 1} (C := Z.ProEt)).functor.IsEquivalence
  have : PreservesFiniteLimits (proEtaleModelBaseChange i) := by
    dsimp only [proEtaleModelBaseChange]
    infer_instance
  have : (proEtaleModelBaseChange i).Final := inferInstance
  exact (proEtaleModuleFromModel _).mapIso
    (asIso (SheafOfModules.pullbackObjUnitToUnit (proEtaleModelRingUnit i B)))

attribute [local irreducible] regularInverseIso proEtaleModuleInverseImage
  inverseSection scalarIdentification

private noncomputable def coefficientInverseIso {X Z : Scheme.{u}} (i : Z ⟶ X)
    {R B : Rings X} (a : R ⟶ B) :
    (inverse i R).obj (coefficientModule a) ≅
      (restrict (inverseRingMap i a)).obj
        (SheafOfModules.unit (proEtaleModuleCoefficients (inverseRing i B))) :=
  scalarIdentification i a (SheafOfModules.unit (proEtaleModuleCoefficients B)) ≪≫
    (restrict (inverseRingMap i a)).mapIso (regularInverseIso i B)

attribute [local irreducible] coefficientInverseIso

private noncomputable abbrev coefficientMap {X : Scheme.{u}} {R B : Rings X}
    (a : R ⟶ B) : proEtaleModuleCoefficients R ⟶ proEtaleModuleCoefficients B :=
  (sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map a

section
universe s h
variable {C : Type s} [Category.{h} C] {J : GrothendieckTopology C}
  [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
  [HasWeakSheafify J AddCommGrpCat.{u + 1}]
  {R₀ B₀ : Sheaf J RingCat.{u + 1}}

end

private theorem tensorSecond_id {X : Scheme.{u}} {R : Rings X} (M N : Modules R) :
    SheafOfModules.siteSheafTensorSecondMap M (𝟙 N) = 𝟙 (tensor M N) := by
  let S := PresheafOfModules.sheafification.{u + 1} (𝟙 (proEtaleModuleCoefficients R).obj)
  change S.map _ = 𝟙 _
  rw [← S.map_id]
  congr 1
  apply PresheafOfModules.hom_ext
  intro V
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro x y
  rfl

private theorem tensorSecond_comp {X : Scheme.{u}} {R : Rings X}
    (M : Modules R) {N N' N'' : Modules R} (b : N ⟶ N') (c : N' ⟶ N'') :
    SheafOfModules.siteSheafTensorSecondMap M (b ≫ c) =
      SheafOfModules.siteSheafTensorSecondMap M b ≫
        SheafOfModules.siteSheafTensorSecondMap M c := by
  let S := PresheafOfModules.sheafification.{u + 1} (𝟙 (proEtaleModuleCoefficients R).obj)
  change S.map _ = S.map _ ≫ S.map _
  rw [← S.map_comp]
  congr 1
  apply PresheafOfModules.hom_ext
  intro V
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro x y
  rfl

private theorem tensorMap_id {X : Scheme.{u}} {R : Rings X} (M N : Modules R) :
    tensorMap (𝟙 M) (𝟙 N) = 𝟙 (tensor M N) := by
  unfold tensorMap
  rw [tensorSecond_id, Category.comp_id]
  exact (SheafOfModules.siteSheafTensorRight N).map_id M

private theorem tensorMap_comp {X : Scheme.{u}} {R : Rings X}
    {M M' M'' N N' N'' : Modules R}
    (a : M ⟶ M') (a' : M' ⟶ M'') (b : N ⟶ N') (b' : N' ⟶ N'') :
    tensorMap (a ≫ a') (b ≫ b') = tensorMap a b ≫ tensorMap a' b' := by
  simp only [tensorMap, Functor.map_comp, tensorSecond_comp, Category.assoc]
  rw [← Category.assoc (SheafOfModules.siteSheafTensorSecondMap M' b)]
  rw [← SheafOfModules.siteSheafTensorSecondMap_naturality a' b]
  simp only [Category.assoc]

private noncomputable def tensorIso {X : Scheme.{u}} {R : Rings X}
    {M M' N N' : Modules R} (e : M ≅ M') (f : N ≅ N') :
    tensor M N ≅ tensor M' N' where
  hom := tensorMap e.hom f.hom
  inv := tensorMap e.inv f.inv
  hom_inv_id := by rw [← tensorMap_comp, e.hom_inv_id, f.hom_inv_id, tensorMap_id]
  inv_hom_id := by rw [← tensorMap_comp, e.inv_hom_id, f.inv_hom_id, tensorMap_id]

end AlgebraicGeometry.ProEtaleClosedProjection
