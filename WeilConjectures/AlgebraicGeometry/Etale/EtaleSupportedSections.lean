/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.Mathlib.CategoryTheory.Sites.GlobalSections
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Kernels
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusComp
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory

/-!
# Étale sections with closed support

Source: Stacks Project, Cohomology, Tag 0G6Y.

The complement `W` determines the closed support. The section functor is an actual kernel,
and its right derived functor uses the existing bounded below localization construction.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

/-- Sections supported on the closed complement of `W`, as the kernel of restriction.
Source: Stacks Tag 0G6Y. -/
noncomputable def supportedEtaleSections (R : Type (u + 1)) [CommRing R]
    (X : Scheme.{u}) (W : X.Opens) :
    Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R) ⥤ ModuleCat.{u + 1} R :=
  kernel (Sheaf.natTransΓRes X.smallEtaleTopology (ModuleCat.{u + 1} R)
    (op (Scheme.Etale.mk W.ι)))

/-- Inclusion of supported sections into global sections. -/
noncomputable def supportedEtaleSectionsι (R : Type (u + 1)) [CommRing R]
    (X : Scheme.{u}) (W : X.Opens) :
    supportedEtaleSections R X W ⟶ Sheaf.Γ X.smallEtaleTopology (ModuleCat.{u + 1} R) :=
  kernel.ι _

/-- The kernel section functor is additive.
Source: Stacks Tag 0G6Y. -/
@[instance]
theorem supportedEtaleSections_additive (R : Type (u + 1)) [CommRing R]
    (X : Scheme.{u}) (W : X.Opens) : (supportedEtaleSections R X W).Additive := by
  constructor
  intro M N f g
  have : Mono ((supportedEtaleSectionsι R X W).app N) := by
    dsimp [supportedEtaleSectionsι]
    infer_instance
  apply (cancel_mono ((supportedEtaleSectionsι R X W).app N)).1
  rw [Preadditive.add_comp, (supportedEtaleSectionsι R X W).naturality,
    (supportedEtaleSectionsι R X W).naturality,
    (supportedEtaleSectionsι R X W).naturality, Functor.map_add, Preadditive.comp_add]

end AlgebraicGeometry.Etale
