/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q35
-/
module

public import Sheaf.Algebra.Homology.FilteredComplexSubquotients
public import Sheaf.CategoryTheory.FiniteFiltrationInduction
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Quotient
public import Mathlib.CategoryTheory.Localization.Construction
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-!
# The homotopy category of finite filtered module complexes

Source: Stacks Project, Derived Categories, Tags 05S1 and 05S2, and More on Algebra,
Tag 0H7X, finite-interval specialization
(blueprint: def-kun-finite-filtered-module-homotopy).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex

variable (R : Type u) [CommRing R]

/-- Finite decreasing filtrations by subcomplexes; no bound on cochain degrees is imposed.
Source: Stacks, Tags 05S2 and 0H7X, finite-interval form
(blueprint: def-kun-finite-filtered-module-homotopy). -/
abbrev FiniteFilteredModuleComplex :=
  ObjectProperty.FullSubcategory
    (fun K : FilteredObject (CochainComplex (ModuleCat.{u} R) ℤ) ↦ K.filtration.IsFinite)

/-- Filtration-preserving chain homotopy: each component factors through the same target
filtration step. `Homotopy` supplies precisely the identity `f - g = dh + hd`.
Source: Stacks, Derived Categories, Section 13.13, before Tag 05S1
(blueprint: def-kun-finite-filtered-module-homotopy). -/
def finiteFilteredModuleHomotopyRel : HomRel (FiniteFilteredModuleComplex R) :=
  fun {K L} f g ↦ ∃ h : Homotopy f.hom.hom g.hom.hom,
    ∀ i n m : ℤ, ∃ lift :
      (K.obj.filtration.step i : CochainComplex (ModuleCat.{u} R) ℤ).X n ⟶
        (L.obj.filtration.step i : CochainComplex (ModuleCat.{u} R) ℤ).X m,
      lift ≫ (L.obj.filtration.step i).arrow.f m =
        (K.obj.filtration.step i).arrow.f n ≫ h.hom n m

/-- Finite filtered complexes with filtered chain maps modulo filtration-preserving homotopy.
Source: Stacks, Tag 05S2, with the uniform finite filtration of Tag 0H7X
(blueprint: def-kun-finite-filtered-module-homotopy). -/
abbrev FiniteFilteredModuleHomotopy :=
  CategoryTheory.Quotient (finiteFilteredModuleHomotopyRel R)

/-- The canonical functor taking a filtered chain map to its homotopy class.
Source: Stacks, Derived Categories, Section 13.13, Tag 05S2
(blueprint: def-kun-finite-filtered-module-homotopy). -/
noncomputable def finiteFilteredModuleHomotopyQuotient :
    FiniteFilteredModuleComplex R ⥤ FiniteFilteredModuleHomotopy R :=
  CategoryTheory.Quotient.functor (finiteFilteredModuleHomotopyRel R)

/-- Filtered quasi-isomorphisms in the homotopy category, expressed by a representative
whose canonical map on every associated graded complex is a quasi-isomorphism.
Source: Stacks, Tags 05S1 and 05S2
(blueprint: def-kun-finite-filtered-module-homotopy). -/
def finiteFilteredModuleQuasiIso : MorphismProperty (FiniteFilteredModuleHomotopy R) :=
  fun {K L} q ↦ ∃ f : K.as ⟶ L.as,
    (finiteFilteredModuleHomotopyQuotient R).map f = q ∧
      ∀ i : ℤ, QuasiIso (FilteredObject.gradedMapSteps f.hom i)

end CochainComplex
