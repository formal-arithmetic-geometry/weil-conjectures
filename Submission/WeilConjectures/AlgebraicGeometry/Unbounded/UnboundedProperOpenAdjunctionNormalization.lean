/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Submission.WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Submission.WeilConjectures.CategoryTheory.K.KInjectiveTotalDerived
public import Submission.WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import Submission.WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriek
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Submission.WeilConjectures.AlgebraicGeometry.ExactUnboundedExchange
public import Submission.WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
public import Submission.WeilConjectures.SixFunctors.BaseChange.Square

import Submission.WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.Algebra.Homology.Localization
import Submission.WeilConjectures.AlgebraicGeometry.EtaleInverseImageAlgebraicStructures
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Submission.WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheaf
import Submission.WeilConjectures.AlgebraicGeometry.EtaleInverseImageModuleConstruction
import Submission.WeilConjectures.AlgebraicGeometry.EtaleInverseImageModuleLinearCriterion
import Submission.WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients
import Submission.WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import Mathlib.AlgebraicGeometry.Sites.AffineEtale
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
import Mathlib.CategoryTheory.Adjunction.Mates
import Submission.WeilConjectures.CategoryTheory.DerivedExactMate
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-!
# Unbounded proper/open AdjunctionNormalization

Source: Stacks Project, Tags 0F7B.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private lemma comparison_naturality
    {C E : Type*} [Category C] [Category E] [Abelian C] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory E] [Abelian.HasKInjectiveResolutions C]
    (F : C ⥤ E) [F.Additive]
    {J I : CochainComplex C ℤ} [J.IsKInjective] [I.IsKInjective] (f : J ⟶ I) :
    F.rightDerivedFunctor.map (DerivedCategory.Q.map f) ≫
        (F.rightDerivedFunctorObjQIso I).hom =
      (F.rightDerivedFunctorObjQIso J).hom ≫
        DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map f) := by
  have h₁ := (DerivedCategory.quotientCompQhIso C).inv.naturality f
  have h₂ := F.rightDerivedFunctorUnit.naturality
    ((HomotopyCategory.quotient _ _).map f)
  have h₃ := (DerivedCategory.quotientCompQhIso E).hom.naturality
    ((F.mapHomologicalComplex _).map f)
  dsimp at h₁ h₂ h₃
  dsimp only [Functor.rightDerivedFunctorObjQIso, Iso.trans_hom, Iso.symm_hom, asIso_inv,
    CategoryTheory.Functor.mapIso_hom, Iso.app_hom, Iso.app_inv]
  rw [← F.rightDerivedFunctor.map_comp_assoc, h₁, F.rightDerivedFunctor.map_comp,
    Category.assoc, Category.assoc, cancel_epi, Category.assoc,
    IsIso.eq_inv_comp, ← reassoc_of% h₂]
  simp only [IsIso.hom_inv_id_assoc]
  exact h₃

private instance restriction_preserves_kinjective
    (A : Type (u + 1)) [CommRing A] {U V : Scheme.{u}}
    (k : U ⟶ V) [IsOpenImmersion k] :
    ((k)^*[ModuleCat.{u + 1} A]).PreservesKInjectiveComplexes :=
  (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) k)
    |>.preservesKInjectiveComplexes

end AlgebraicGeometry.Etale
