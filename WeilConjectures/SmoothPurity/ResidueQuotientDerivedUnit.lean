/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
import all WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModulesSupplement
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Data.ZMod.Basic
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Whiskering
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.DerivedBaseChange
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Reduction
import WeilConjectures.Algebra.Homology.DivisibleReduction.DivisibleExtensionDerivedReductionSupplement
import WeilConjectures.Mathlib.Algebra.Category.Grp.ZModuleEquivalence
import WeilConjectures.SixFunctors.BaseChange.DerivedForget
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Coinduce
import Mathlib.CategoryTheory.Abelian.ShortExact

/-!
# The quotient-normalized derived residue unit

The scalar unit is identified with the actual quotient morphism, and its universal
property is tested against every unbounded complex.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped ZeroObject
universe u₁ u₂ u₃ v₁ v₂ v₃ w₁ w₂ w₃ w₄ wAb wMod
attribute [local instance] HasDerivedCategory.standard
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
namespace CategoryTheory.Functor
variable {C : Type u₁} {D : Type u₂} {E : Type u₃}
  [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E]
  [Abelian C] [Abelian D] [Abelian E]
  [HasDerivedCategory.{w₁} C] [HasDerivedCategory.{w₂} D]
  [HasDerivedCategory.{w₃} E]
variable (F : C ⥤ D) (G : D ⥤ E)
  [F.Additive] [G.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
variable (H : C ⥤ D) [H.Additive] [PreservesFiniteLimits H] [PreservesFiniteColimits H]
omit [HasDerivedCategory C] [HasDerivedCategory D]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits H] [PreservesFiniteColimits H] in
end CategoryTheory.Functor


namespace CategoryTheory.Sheaf.ConstantResidue
variable {C : Type (u + 1)} [Category.{u} C]
variable (J : GrothendieckTopology C)
variable [HasSheafify J CommRingCat.{u + 1}]
variable [J.HasSheafCompose (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})]
variable [HasSheafify J AddCommGrpCat.{u + 1}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]

private abbrev coefficientRing (A : Type (u + 1)) [CommRing A] :=
  (sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
    ((constantSheaf J CommRingCat.{u + 1}).obj (CommRingCat.of A))

private def coefficientMap (A : Type (u + 1)) [CommRing A] :
    (Functor.const Cᵒᵖ).obj (RingCat.of A) ⟶ (coefficientRing J A).obj :=
  Functor.whiskerRight (toSheafify J
    ((Functor.const Cᵒᵖ).obj (CommRingCat.of A)))
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})

private instance (A : Type (u + 1)) [CommRing A] :
    Presheaf.IsLocallyInjective J (coefficientMap J A) := by
  apply (Presheaf.isLocallyInjective_forget_iff _ _).mp
  change Presheaf.IsLocallyInjective J (Functor.whiskerRight (toSheafify J
    ((Functor.const Cᵒᵖ).obj (CommRingCat.of A))) (forget CommRingCat.{u + 1}))
  infer_instance

private instance (A : Type (u + 1)) [CommRing A] :
    Presheaf.IsLocallySurjective J (coefficientMap J A) := by
  apply (Presheaf.isLocallySurjective_iff_whisker_forget _ _).mpr
  change Presheaf.IsLocallySurjective J (Functor.whiskerRight (toSheafify J
    ((Functor.const Cᵒᵖ).obj (CommRingCat.of A))) (forget CommRingCat.{u + 1}))
  infer_instance

private instance (A : Type (u + 1)) [CommRing A] : (realize J A).IsEquivalence :=
  AlgebraicGeometry.ProEtale.coefficientRealization_isEquivalence J A
    (coefficientRing J A) (coefficientMap J A)

set_option backward.isDefEq.respectTransparency false in
private instance : (forgetSheaf J (ULift.{u + 1} ℤ)).IsEquivalence := by
  let F := forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) AddCommGrpCat.{u + 1}
  have : (forgetSheaf J (ULift.{u + 1} ℤ)).Full :=
    (forgetSheafFullyFaithful J _).full
  have : (forgetSheaf J (ULift.{u + 1} ℤ)).Faithful :=
    (forgetSheafFullyFaithful J _).faithful
  have : (forgetSheaf J (ULift.{u + 1} ℤ)).EssSurj := by
    constructor
    intro G
    let ε := F.asEquivalence.counitIso
    refine ⟨(sheafCompose J F.inv).obj G, ⟨?_⟩⟩
    exact
      { hom := (sheafCompose_map J ε.hom).app G
        inv := (sheafCompose_map J ε.inv).app G
        hom_inv_id := by
          rw [← NatTrans.comp_app, ← sheafCompose_comp, ε.hom_inv_id]
          rfl
        inv_hom_id := by
          rw [← NatTrans.comp_app, ← sheafCompose_comp, ε.inv_hom_id]
          rfl }
  exact Functor.IsEquivalence.mk

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

private instance (A : Type (u + 1)) [CommRing A] : (realize J A).Additive :=
  Functor.additive_of_preserves_binary_products _

attribute [local irreducible] realize

open SheafOfModules.DivisibleReduction in
open SheafOfModules.DivisibleReduction in
end CategoryTheory.Sheaf.ConstantResidue
