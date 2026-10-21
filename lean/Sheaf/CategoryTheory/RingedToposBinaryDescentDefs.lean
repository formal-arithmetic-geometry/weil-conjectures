/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.Triangulated.Pretriangulated
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import WeilConjectures.Algebra.Homology.RhomIntoKInjectiveLocal

/-!
# Termwise restriction and adjunction mates for binary descent

Source: literature/stacks-project/cohomology.tex, Tags 08DG and 08BU (blueprint:
def-sp-ringed-topos-binary-descent-models).
-/

@[expose] public section

universe u v r w s

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

set_option autoImplicit false
set_option synthInstance.maxSize 4096

/-- Expose Mathlib's small-model abelian sheafification at the chosen site universe.
Source: Stacks 03CV (blueprint: def-sp-ringed-topos-binary-descent-models). -/
noncomputable instance binaryDescent_hasSheafify {C : Type u} [Category.{v} C]
    [EssentiallySmall.{s} C] (J : GrothendieckTopology C) :
    HasSheafify J AddCommGrpCat.{s} :=
  hasSheafifyEssentiallySmallSite J AddCommGrpCat.{s}

/-- Expose Mathlib's transport of the local criterion for abelian sheafification.
Source: Stacks 03CV (blueprint: def-sp-ringed-topos-binary-descent-models). -/
noncomputable instance binaryDescent_wEqualsLocallyBijective
    {C : Type u} [Category.{v} C] [EssentiallySmall.{s} C]
    (J : GrothendieckTopology C) :
    J.WEqualsLocallyBijective AddCommGrpCat.{s} :=
  letI : ∀ X : Cᵒᵖ,
      HasLimitsOfShape (StructuredArrow X (equivSmallModel.{s} C).inverse.op) AddCommGrpCat.{s} :=
    fun _ ↦ HasLimitsOfShape.of_small.{s, s} AddCommGrpCat.{s} _
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall J (A := AddCommGrpCat.{s})

/-- Termwise restriction to the localized site, using the recorded restriction functor.
Source: Stacks 03DH and 03DJ (blueprint: def-sp-ringed-topos-binary-descent-models). -/
noncomputable def moduleOverComplex {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} (R : Sheaf J RingCat.{r}) (U : C) :=
  letI := module_overFunctor_preservesZero.{u, v, max u v r, r} R U
  (SheafOfModules.overFunctor.{max u v r} R U).mapHomologicalComplex (.up ℤ)

/-- Termwise relocalization along a map of objects of the site.
Source: Stacks 03DH (blueprint: def-sp-ringed-topos-binary-descent-models). -/
noncomputable def moduleOverMapComplex {C : Type u} [Category.{v} C] [HasPullbacks C]
    {J : GrothendieckTopology C} (R : Sheaf J RingCat.{r}) {U V : C} (f : U ⟶ V) :=
  (SheafOfModules.overMap.{max u v r} R f).mapHomologicalComplex (.up ℤ)

/-- The sectionwise identity comparing restriction with iterated restriction on complexes.
Source: Stacks 03DH (blueprint: def-sp-ringed-topos-binary-descent-models). -/
noncomputable def moduleOverComplexComp {C : Type u} [Category.{v} C] [HasPullbacks C]
    {J : GrothendieckTopology C} (R : Sheaf J RingCat.{r}) {U V : C} (f : U ⟶ V) :
    moduleOverComplex R U ≅ moduleOverComplex R V ⋙ moduleOverMapComplex R f :=
  letI := module_overFunctor_preservesZero.{u, v, max u v r, r} R U
  letI := module_overFunctor_preservesZero.{u, v, max u v r, r} R V
  NatIso.mapHomologicalComplex (SheafOfModules.overFunctorMap R f).symm (.up ℤ)

/-- The direct-image restriction map is the adjoint of restriction of the counit.
Source: Stacks 08DG, cone construction (blueprint: def-sp-ringed-topos-binary-descent-models). -/
noncomputable def restrictionAdjunctionMap
    {D DU DW : Type*} [Category D] [Category DU] [Category DW]
    {rU : D ⥤ DU} {rW : D ⥤ DW} {rUW : DU ⥤ DW}
    {RU : DU ⥤ D} {RW : DW ⥤ D}
    (adjU : rU ⊣ RU) (adjW : rW ⊣ RW) (comp : rW ≅ rU ⋙ rUW) (A : DU) :
    RU.obj A ⟶ RW.obj (rUW.obj A) :=
  (adjW.homEquiv _ _) (comp.hom.app (RU.obj A) ≫ rUW.map (adjU.counit.app A))

end CategoryTheory
end
