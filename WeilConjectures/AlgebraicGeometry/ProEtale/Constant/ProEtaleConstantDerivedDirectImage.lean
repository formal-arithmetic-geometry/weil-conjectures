/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsCanonicalAdjunctionSupplement
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import WeilConjectures.AlgebraicGeometry.ProEtale.Module.ProEtaleModuleDirectImageLeftExact

public import Mathlib.CategoryTheory.Limits.Preserves.Finite
/-!
# Canonical constant-coefficient derived direct image

Source: Weil conjectures blueprint, `prose-03-02`, order 1468;
Stacks Project, Cohomology on Sites, Section 07A5
(blueprint: prose-03-02).

The canonical constant-section structure map already defines module direct image.
Its right derived functor needs no separately supplied coefficient identification.
All the recorded identified-coefficient operations are reexported.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- Additivity of the canonical sectionwise direct image, from its recorded left-exactness
statement. Source: blueprint order 1468; Stacks Tag 03DA
(blueprint: prose-03-02). -/
noncomputable instance proEtaleConstantModuleDirectImage_additive {X Y : Scheme.{u}} (f : X ⟶ Y)
    (A : Type u) [CommRing A] : (proEtaleConstantModuleDirectImage f A).Additive :=
  (proEtaleConstantModuleDirectImage_additive_leftExact f A).1

/-- The ordinary uncompleted unbounded right derived direct image, constructed using
K-injective resolutions in all modules over the constant coefficient sheaf. The module
functor is the recorded sectionwise direct image through the constant-section map.
Source: blueprint `prose-03-02`, order 1468; Stacks Section 07A5
(blueprint: prose-03-02). -/
noncomputable abbrev proEtaleConstantDerivedDirectImage {X Y : Scheme.{u}} (f : X ⟶ Y)
    (A : Type u) [CommRing A] : proEtaleDerivedCategory X A ⥤ proEtaleDerivedCategory Y A :=
  (proEtaleConstantModuleDirectImage f A).rightDerivedFunctor

end AlgebraicGeometry.Scheme
