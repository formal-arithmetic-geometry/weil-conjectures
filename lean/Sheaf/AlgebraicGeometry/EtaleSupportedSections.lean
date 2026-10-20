/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q24
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

Source: the blueprint, sec-smooth-purity/sk-prop-a1-kummer,
lem-pur-support-restriction-triangle, definition of supported sections and proof step 1;
Stacks Project, Cohomology, Tag 0G6Y.
(blueprint: def-pur-etale-derived-supported-sections).

The complement `W` determines the closed support. The section functor is an actual kernel,
and its right derived functor uses the existing bounded below localization construction.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

/-- Sections supported on the closed complement of `W`, as the kernel of restriction.
Source: blueprint lem-pur-support-restriction-triangle, proof step 1; Stacks Tag 0G6Y.
(blueprint: def-pur-etale-derived-supported-sections). -/
noncomputable def supportedEtaleSections (R : Type (u + 1)) [CommRing R]
    (X : Scheme.{u}) (W : X.Opens) :
    Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R) ⥤ ModuleCat.{u + 1} R :=
  kernel (Sheaf.natTransΓRes X.smallEtaleTopology (ModuleCat.{u + 1} R)
    (op (Scheme.Etale.mk W.ι)))

/-- Inclusion of supported sections into global sections.
Source: blueprint lem-pur-support-restriction-triangle, proof step 1.
(blueprint: def-pur-etale-derived-supported-sections). -/
noncomputable def supportedEtaleSectionsι (R : Type (u + 1)) [CommRing R]
    (X : Scheme.{u}) (W : X.Opens) :
    supportedEtaleSections R X W ⟶ Sheaf.Γ X.smallEtaleTopology (ModuleCat.{u + 1} R) :=
  kernel.ι _

/-- The kernel section functor is additive.
Source: blueprint lem-pur-support-restriction-triangle, proof step 1; Stacks Tag 0G6Y.
(blueprint: def-pur-etale-derived-supported-sections).

Proof: the global section functor is additive. The kernel inclusion is a monomorphism
in the functor category and hence on every component. Compose the desired addition
identity with its component at the target sheaf. Naturality of the inclusion reduces
both sides to the addition identity for global sections. Cancel the monomorphism. -/
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

/-- Sections with closed support form a left exact functor.
Source: blueprint lem-pur-support-restriction-triangle, proof step 1; Stacks Tag 0G6Y.
(blueprint: def-pur-etale-derived-supported-sections).

Proof: global sections and evaluation of a sheaf on the etale object `W` preserve
finite limits. Evaluating the functor-category kernel is the kernel of the evaluated
restriction map. Finite limits commute with kernels, so this pointwise kernel of the
two finite-limit-preserving section functors preserves finite limits as well. -/
@[instance]
theorem supportedEtaleSections_preservesFiniteLimits (R : Type (u + 1)) [CommRing R]
    (X : Scheme.{u}) (W : X.Opens) :
    PreservesFiniteLimits (supportedEtaleSections R X W) := by
  let D := parallelPair
    (Sheaf.natTransΓRes X.smallEtaleTopology (ModuleCat.{u + 1} R)
      (op (Scheme.Etale.mk W.ι))) 0
  have : PreservesFiniteLimits D.flip := by
    apply preservesFiniteLimits_of_evaluation
    intro j
    cases j
    · change PreservesFiniteLimits (Sheaf.Γ X.smallEtaleTopology (ModuleCat.{u + 1} R))
      infer_instance
    · change PreservesFiniteLimits
        (sheafToPresheaf X.smallEtaleTopology (ModuleCat.{u + 1} R) ⋙
          (evaluation _ _).obj (op (Scheme.Etale.mk W.ι)))
      infer_instance
  exact preservesFiniteLimits_of_natIso (limitIsoFlipCompLim D).symm

/-- The bounded below derived functor of sections supported on the complement of `W`,
viewed in the full derived category of coefficient modules.
Source: blueprint lem-pur-support-restriction-triangle, statement and proof step 5.
(blueprint: def-pur-etale-derived-supported-sections). -/
noncomputable abbrev derivedSupportedEtaleSections (R : Type (u + 1)) [CommRing R]
    (X : Scheme.{u}) (W : X.Opens) :
    DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)) ⥤
      DerivedCategory (ModuleCat.{u + 1} R) :=
  (supportedEtaleSections R X W).rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι

end AlgebraicGeometry.Etale
