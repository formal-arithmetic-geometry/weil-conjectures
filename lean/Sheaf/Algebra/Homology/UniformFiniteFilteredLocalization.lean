/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q49
-/
module

public import WeilConjectures.CategoryTheory.FiniteFiltrationInductionExtension
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.CochainComplexPlus
public import WeilConjectures.FromJoel.Algebra.Homology.CochainComplexMinus
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Localization.Construction
public import Mathlib.CategoryTheory.EssentialImage

/-!
# Uniformly finite filtered cochain localizations

Source: Stacks Project, Derived Categories, Tags 05S2, 05S4, 05S5 and 05S6,
restricted to uniformly finite filtrations, as in the trace-formula comparison
(blueprint: def-trf-uniform-finite-filtered-localization).

Filtrations are subobjects in the abelian category of cochain complexes. Thus their
finite bounds are uniform in cochain degree. `B = some (a,b)` fixes those bounds;
`B = none` allows them to depend on the complex. `P` specifies cochain boundedness.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe v u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Uniform finite filtration bounds, optional fixed interval, and cochain condition `P`.
Source: Stacks, Tags 05S2 and 05S4, restricted uniformly in cochain degree
(blueprint: def-trf-uniform-finite-filtered-localization). -/
def uniformFilteredProperty (B : Option (ℤ × ℤ))
    (P : ObjectProperty (CochainComplex C ℤ)) :
    ObjectProperty (FilteredObject (CochainComplex C ℤ)) := fun K ↦
  K.filtration.IsFinite ∧
    (∀ a b : ℤ, B = some (a, b) →
      K.filtration.F a = ⊤ ∧ K.filtration.F (b + 1) = ⊥) ∧ P K.obj

/-- Cochain-bounded uniformly finite filtered complexes and filtered chain maps.
Source: Stacks, Tags 05S2 and 05S4
(blueprint: def-trf-uniform-finite-filtered-localization). -/
abbrev UniformFilteredComplexes (C : Type u) [Category.{v} C] [Abelian C]
    (B : Option (ℤ × ℤ)) (P : ObjectProperty (CochainComplex C ℤ)) :=
  (uniformFilteredProperty B P).FullSubcategory

/-- The graded quasi-isomorphisms, using the existing canonical graded chain map.
Source: Stacks, Tag 05S2
(blueprint: def-trf-uniform-finite-filtered-localization). -/
def uniformFilteredQuasiIso (B : Option (ℤ × ℤ))
    (P : ObjectProperty (CochainComplex C ℤ)) :
    MorphismProperty (UniformFilteredComplexes C B P) := fun _ _ f ↦
  ∀ p : ℤ, QuasiIso (FilteredObject.gradedMapSteps f.hom p)

/-- The chain-map localization at graded quasi-isomorphisms.
Source: Stacks, Tags 05S2 and 05S4
(blueprint: def-trf-uniform-finite-filtered-localization). -/
abbrev UniformFilteredDerived (C : Type u) [Category.{v} C] [Abelian C]
    (B : Option (ℤ × ℤ)) (P : ObjectProperty (CochainComplex C ℤ)) :=
  (uniformFilteredQuasiIso B P).Localization

/-- The natural inclusion when the cochain condition is weakened.
Source: Stacks, Tag 05S6
(blueprint: def-trf-uniform-finite-filtered-localization). -/
def uniformFilteredInclusion (B : Option (ℤ × ℤ))
    {P R : ObjectProperty (CochainComplex C ℤ)} (h : P ≤ R) :
    UniformFilteredComplexes C B P ⥤ UniformFilteredComplexes C B R :=
  ObjectProperty.ιOfLE (fun _ hK ↦ ⟨hK.1, hK.2.1, h _ hK.2.2⟩)

/-- The canonical comparison of localizations, obtained by localizing the inclusion.
Source: Stacks, Tag 05S6
(blueprint: def-trf-uniform-finite-filtered-localization). -/
def uniformFilteredComparison (B : Option (ℤ × ℤ))
    {P R : ObjectProperty (CochainComplex C ℤ)} (h : P ≤ R) :
    UniformFilteredDerived C B P ⥤ UniformFilteredDerived C B R :=
  Localization.Construction.lift
    (uniformFilteredInclusion B h ⋙ (uniformFilteredQuasiIso B R).Q)
    (fun _ _ f hf ↦ (uniformFilteredQuasiIso B R).Q_inverts
      ((uniformFilteredInclusion B h).map f) hf)

/-- Graded cohomological support in a set of degrees. The same set bounds every grade.
Source: Stacks, Tag 05S5
(blueprint: def-trf-uniform-finite-filtered-localization). -/
def uniformGradedSupport (S : Set ℤ) (K : FilteredObject (CochainComplex C ℤ)) : Prop :=
  ∀ p n : ℤ, n ∉ S → IsZero ((K.filtration.gr p).homology n)

/-- Bounded cochain support, with the existing bounded-below and bounded-above
predicates `CochainComplex.plus` and `CochainComplex.minus`.
Source: Stacks, Tag 05S4
(blueprint: def-trf-uniform-finite-filtered-localization). -/
def uniformCochainBounded : ObjectProperty (CochainComplex C ℤ) :=
  fun K ↦ CochainComplex.plus C K ∧ CochainComplex.minus C K

/-- Cohomological support in the localization, expressed on a representative.
Every object of the constructed localization has such a representative; isomorphisms
preserve graded cohomology. Source: Stacks, Tags 05S4 and 05S5
(blueprint: def-trf-uniform-finite-filtered-localization). -/
def uniformLocalizedSupport (B : Option (ℤ × ℤ)) (S : Set ℤ)
    (X : UniformFilteredDerived C B (fun _ ↦ True)) : Prop :=
  ∃ K : UniformFilteredComplexes C B (fun _ ↦ True),
    Nonempty ((uniformFilteredQuasiIso B (fun _ ↦ True)).Q.obj K ≅ X) ∧
      uniformGradedSupport S K.obj

end CategoryTheory
