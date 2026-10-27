/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q25
-/
module

public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.Ring.Limits
public import Sheaf.Paper.CoefficientHomRepresentativeEvaluation
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

/-! # Scalar-valued global sections on small ringed sites

Source: Stacks Project, Tag 0D6H (lemma-Leray-unbounded), Tag 08JA and Equation 0A8Z.
(blueprint: def-sfb-ringed-site-scalar-global-sections).

Sections are compatible families, with the prescribed pointwise scalar action.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048

universe u w

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.RingedSiteScalarGlobalSections

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{u}) (A : Type u) [CommRing A]

/-- The recorded module category on this site.
Source: Stacks 03D7 (blueprint: def-sfb-ringed-site-scalar-global-sections). -/
abbrev Modules := ringedSiteModules.{u}
  ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)

/-- Global scalars as compatible families, without requiring a final site object.
Source: Stacks 0D6H (blueprint: def-sfb-ringed-site-scalar-global-sections). -/
abbrev Scalars := RingCat.sectionsSubring
  ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R).obj

variable (s : A →+* Scalars R)

/-- Evaluation of the specified scalar action at a site object.
Source: Stacks 0D6H (blueprint: def-sfb-ringed-site-scalar-global-sections). -/
def scalarAt (U : Cᵒᵖ) : A →+* R.obj.obj U where
  toFun a := (s a).val U
  map_zero' := congrArg (fun x : Scalars R ↦ x.val U) s.map_zero
  map_one' := congrArg (fun x : Scalars R ↦ x.val U) s.map_one
  map_add' a b := congrArg (fun x : Scalars R ↦ x.val U) (s.map_add a b)
  map_mul' a b := congrArg (fun x : Scalars R ↦ x.val U) (s.map_mul a b)

/-- All families of module sections, with the specified pointwise scalar action.
Source: Stacks 0D6H (blueprint: def-sfb-ringed-site-scalar-global-sections). -/
abbrev Families (M : Modules R) :=
  ∀ U : Cᵒᵖ, (ModuleCat.restrictScalars (scalarAt R A s U)).obj (M.val.obj U)

/-- The submodule of compatible families is the scalar-valued global sections object.
Source: Stacks 0D6H (blueprint: def-sfb-ringed-site-scalar-global-sections). -/
def sectionSubmodule (M : Modules R) : Submodule A (Families R A s M) where
  carrier := {x | ∀ ⦃U V : Cᵒᵖ⦄ (i : U ⟶ V), M.val.map i (x U) = x V}
  zero_mem' := by intro U V i; exact (M.val.map i).hom.map_zero
  add_mem' := by
    intro x y hx hy U V i
    exact ((M.val.map i).hom.map_add (x U) (y U)).trans (congrArg₂ (· + ·) (hx i) (hy i))
  smul_mem' := by
    intro a x hx U V i
    change M.val.map i ((s a).val U • x U) = (s a).val V • x V
    rw [map_smulₛₗ, hx i]
    exact congrArg (fun b ↦ b • x V) ((s a).property i)

/-- Global sections restricted to the specified scalar ring, on objects and maps.
Source: Stacks 0D6H (blueprint: def-sfb-ringed-site-scalar-global-sections). -/
def sections : Modules R ⥤ ModuleCat.{u} A where
  obj M := ModuleCat.of A (sectionSubmodule R A s M)
  map {M N} f := ModuleCat.ofHom
    { toFun := fun x ↦ ⟨fun U ↦ f.val.app U (x.val U), fun U V i ↦ by
        change N.val.map i (f.val.app U (x.val U)) = f.val.app V (x.val V)
        rw [← PresheafOfModules.naturality_apply, x.property i]⟩
      map_add' := by intro x y; apply Subtype.ext; funext U; exact map_add _ _ _
      map_smul' := by
        intro a x
        apply Subtype.ext
        funext U
        exact (f.val.app U).hom.map_smul ((s a).val U) (x.val U) }
  map_id M := by ext x; rfl
  map_comp f g := by ext x; rfl

/-- Additivity of scalar-valued sections is pointwise additivity.
Source: Stacks 0D6H (blueprint: def-sfb-ringed-site-scalar-global-sections). -/
instance sectionsAdditive : (sections R A s).Additive where
  map_add := by intro M N f g; ext x; rfl

/-- The canonical Grothendieck structure on module sheaves on this small site.
Source: Stacks 079V (blueprint: def-sfb-ringed-site-scalar-global-sections). -/
instance modulesGrothendieck : IsGrothendieckAbelian.{u} (Modules R) :=
  (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{u, u, u}
    J R).1

variable [HasDerivedCategory.{w} (Modules R)]
  [HasDerivedCategory.{w} (ModuleCat.{u} A)]

/-- Derived global sections with the prescribed scalar action.
Source: Stacks 0D6H (blueprint: def-sfb-ringed-site-scalar-global-sections). -/
abbrev derivedSections := (sections R A s).rightDerivedFunctor

/-- A compatible family, as a constant generalized section on any sheaf of sets.
Source: Stacks 0D6H (blueprint: def-sfb-ringed-site-scalar-global-sections). -/
def sectionOn (M : Modules R) (x : (sections R A s).obj M)
    (T : Sheaf J (Type u)) : T ⟶
    (SheafOfModules.toSheaf _ ⋙ sheafCompose J (forget AddCommGrpCat)).obj M where
  hom :=
    { app := fun U ↦ ↾fun _ ↦ x.val U
      naturality := by intro U V i; ext t; exact (x.property i).symm }

/-- A scalar family, viewed as a generalized section of the structure sheaf.
Source: Stacks 0D6H (blueprint: def-sfb-ringed-site-scalar-global-sections). -/
def scalarOn (a : A) (T : Sheaf J (Type u)) : T ⟶
    (sheafCompose J (forget CommRingCat)).obj R where
  hom :=
    { app := fun U ↦ ↾fun _ ↦ (s a).val U
      naturality := by intro U V i; ext t; exact ((s a).property i).symm }

end CategoryTheory.RingedSiteScalarGlobalSections
