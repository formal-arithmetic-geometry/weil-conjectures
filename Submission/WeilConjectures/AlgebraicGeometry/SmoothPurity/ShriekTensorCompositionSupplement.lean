/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Submission.WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjection
public import Submission.WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import Submission.WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
public import Submission.WeilConjectures.SixFunctors.Etale.Derived.Tensor
public import Mathlib.AlgebraicGeometry.Scheme
public import Submission.WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
public import Submission.WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedEtaleCompactSupportComparisonsSupplement
public import Submission.WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Submission.WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategoryBraided
public import Submission.WeilConjectures.AlgebraicGeometry.EtaleDerivedTensorSymmetry
public import Submission.WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Submission.WeilConjectures.AlgebraicGeometry.EtaleInverseImageAlgebraicStructures
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Submission.WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheaf
import Submission.WeilConjectures.AlgebraicGeometry.EtaleInverseImageModuleConstruction
import Submission.WeilConjectures.AlgebraicGeometry.EtaleInverseImageModuleLinearCriterion
import Submission.WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients
import Submission.WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import Mathlib.AlgebraicGeometry.Sites.AffineEtale
public import Submission.WeilConjectures.CategoryTheory.RingedSliceExtensionTensor
public import Submission.WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
public import Submission.WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Submission.WeilConjectures.CategoryTheory.RingedSliceExtensionTensorHomData
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import Submission.WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange
import Submission.WeilConjectures.AlgebraicGeometry.CompactificationProjectionComposition
import Submission.WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjection
import Submission.WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition
import Submission.WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
import Submission.WeilConjectures.AlgebraicGeometry.DerivedCategories
import Submission.WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange
import Submission.WeilConjectures.AlgebraicGeometry.OpenImmersionProjectionComposition
import Submission.WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekProjection
import Submission.WeilConjectures.CategoryTheory.Adjunction.ProjectionMapCompat
import Submission.WeilConjectures.SixFunctors.Etale.Derived.UpperStarCompCoherence
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import Submission.WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarAdjunctionCompat
import Submission.WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjectionComp
import Submission.WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekProjectionBaseChange

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-! # Tensor projection maps and compact-support composition

Source: Stacks Project, `more-etale.tex`, Tags 0F7B and 0F7J, and
`sites-cohomology.tex`, Tag 0E48 (blueprint: lem-amb-shriek-tensor-composition).

The projection map is the existing proper/open compactification construction with both
factors exchanged by the canonical signed derived tensor symmetry. Exact termwise inverse
image is identified with left derived inverse image by its canonical comparison.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 4096

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

private theorem inverse_square
    {C : Type*} [Category C] {W X Y Z : C}
    (a : W ≅ X) (b : Y ≅ Z) (p : W ⟶ Y) (q : X ⟶ Z)
    (h : p ≫ b.hom = a.hom ≫ q) : q ≫ b.inv = a.inv ≫ p := by
  apply (cancel_mono b.hom).1
  simp only [Category.assoc, b.inv_hom_id, Category.comp_id, h, a.inv_hom_id_assoc]

namespace AlgebraicGeometry.Etale

section ProjectionProof
local instance essentiallySmall_etale_shriekTensorMain (X : Scheme.{u}) :
    EssentiallySmall.{u + 1} X.Etale :=
  have : LocallySmall.{u + 1} X.Etale :=
    @locallySmall_of_univLE X.Etale _ (@univLE_of_max.{u, u + 1} UnivLE.self)
  essentiallySmall_of_small_of_locallySmall _
set_option backward.defeqAttrib.useBackward true
attribute [local instance high] SymmetricCategory.toBraidedCategory
attribute [local instance 20000] Etale.sheafBraidedCategory
attribute [-instance] CategoryTheory.sheafToPresheaf_isRightAdjoint
  ModuleCat.hasColimitsOfShape ModuleCat.hasColimitsOfSize

set_option backward.isDefEq.respectTransparency false

-- Keep the large compactification and localization constructions behind their APIs.
attribute [local implicit_reducible] derivedTensorRightDerivedLowerShriek
  rightDerivedLowerShriekDerivedTensorLeftDerivedUpperStar

attribute [local implicit_reducible] Compactification.restrict Compactification.ofIsPullback
  Compactification.comp Compactification.copy Compactification.postcomp

attribute [local irreducible] Functor.mapDerivedCategory Functor.leftDerivedFunctor
  Functor.rightDerivedFunctor unboundedEtaleLowerShriekCompIso
  rightDerivedLowerShriekOfCompactificationIso
  rightDerivedLowerShriekOfCompactificationCompIso
  projectionMapOfCompactification derivedTensorSymmetry derivedTensor

-- The kernel checks the three specified compactification compositors.
end ProjectionProof

section TensorConventionProof
attribute [local instance high] SymmetricCategory.toBraidedCategory
attribute [local instance 20000] Etale.sheafBraidedCategory
attribute [-instance] CategoryTheory.sheafToPresheaf_isRightAdjoint
  ModuleCat.hasColimitsOfShape ModuleCat.hasColimitsOfSize
local instance essentiallySmall_etale_tensorConvention (X : Scheme.{u}) :
    EssentiallySmall.{u + 1} X.Etale :=
  have : LocallySmall.{u + 1} X.Etale :=
    @locallySmall_of_univLE X.Etale _ (@univLE_of_max.{u, u + 1} UnivLE.self)
  essentiallySmall_of_small_of_locallySmall _
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Functor.mapDerivedCategory Functor.leftDerivedFunctor
  Functor.rightDerivedFunctor derivedTensorSymmetry derivedTensor
  unboundedEtaleLowerShriekCompIso projectionMapOfCompactification
attribute [local implicit_reducible] derivedTensorRightDerivedLowerShriek
  rightDerivedLowerShriekDerivedTensorLeftDerivedUpperStar

-- Normalize the two tensor conventions without unfolding the derived functors.
end TensorConventionProof

set_option backward.isDefEq.respectTransparency false

end AlgebraicGeometry.Etale
