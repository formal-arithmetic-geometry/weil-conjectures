/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q132
-/
module

public import Sheaf.Algebra.Homology.FiniteFilteredLocalization
public import Mathlib.CategoryTheory.Triangulated.Subcategory
import Sheaf.Algebra.Homology.FilteredConeLocalization

/-!
# Uniformly finite filtered homotopy localizations

Source: Stacks Project, Derived Categories, Tags 05S5 and 05S6
(blueprint: def-trf-uniform-filtered-homotopy-localization).

We restrict the existing filtered homotopy category by a uniform filtration bound.
Its inherited cone triangles and their standard localizations specify the triangulations.
`B = none` permits an interval depending on the complex; `B = some (a,b)` fixes it.
The Boolean parameter `true` additionally imposes an upper cochain bound.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe v u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

variable (C : Type u) [Category.{v} C] [Abelian C]

/-- The uniform finite-filtration condition in the existing bounded-below filtered
homotopy category, optionally also bounded above. The bounds `a,b` are independent
of the cochain degree `n`. Morphisms and homotopies remain those in the filtered category.
Source: Stacks, Tags 05S4 and 05S6, uniform finite-filtration restriction
(blueprint: def-trf-uniform-filtered-homotopy-localization). -/
def uniformFilteredHomotopyProperty (B : Option (ℤ × ℤ)) (bounded : Bool) :
    ObjectProperty (FiniteFilteredHomotopyPlus C B false) := fun K ↦
  (∃ a b : ℤ, a ≤ b ∧ ∀ n : ℤ,
    (K.obj.as.X n).obj.filtration.step a = ⊤ ∧
      (K.obj.as.X n).obj.filtration.step (b + 1) = ⊥) ∧
    (bounded = true → ∃ d : ℤ, ∀ n : ℤ, d < n → IsZero ((K.obj.as.X n).obj.obj))

/-- Uniformly finite filtered complexes are closed under zero, shifts and cones,
both bounded and bounded below. The subcategory uses the inherited cone triangulation.
Source: Stacks, Tags 05RQ and 05S6.
Proof: zero has any filtration interval. Shifts retain the filtration bounds and translate
cochain bounds. A cone uses direct sums of adjacent terms: take the minimum lower and
maximum upper filtration bounds of its two inputs. Its cochain bounds are obtained in
exactly the same way. All constructions retain fixed bounds when imposed. Distinguished
triangles are isomorphic to cone triangles, giving closure up to isomorphism as required
by `ObjectProperty.IsTriangulated` (Step 1 of the node).
(blueprint: def-trf-uniform-filtered-homotopy-localization). -/
theorem uniformFilteredHomotopy_triangulated (B : Option (ℤ × ℤ)) (bounded : Bool) :
    (uniformFilteredHomotopyProperty C B bounded).IsTriangulated := by
  sorry

attribute [instance] uniformFilteredHomotopy_triangulated

/-- The bounded (`true`) or bounded-below (`false`) uniformly finite filtered homotopy
category, with filtered maps modulo filtered homotopies.
Source: Stacks, Tag 05S6
(blueprint: def-trf-uniform-filtered-homotopy-localization). -/
abbrev UniformFiniteFilteredHomotopy (B : Option (ℤ × ℤ)) (bounded : Bool) :=
  (uniformFilteredHomotopyProperty C B bounded).FullSubcategory

/-- The graded quasi-isomorphisms in the uniformly finite filtered homotopy category.
This is the restriction of the existing graded quasi-isomorphisms, not a new notion.
Source: Stacks, Tags 05S2 and 05S6
(blueprint: def-trf-uniform-filtered-homotopy-localization). -/
def uniformFilteredHomotopyQuasiIso (B : Option (ℤ × ℤ)) (bounded : Bool) :
    MorphismProperty (UniformFiniteFilteredHomotopy C B bounded) :=
  (finiteFilteredQuasiIso C B).inverseImage
    (uniformFilteredHomotopyProperty C B bounded).ι

/-- The restricted graded quasi-isomorphisms admit fractions.
Source: Stacks, Tags 05RG and 05S6.
Proof: in the inherited cone triangulation, graded-acyclic objects form a triangulated
subcategory: zero and shifts are acyclic, and the cone criterion gives closure under
triangles. Grading respects filtered homotopies, so acyclicity is invariant under
isomorphism. The cone class of this subcategory is precisely the stated class of graded
quasi-isomorphisms. The cone-system criterion gives both fraction calculi, in particular
the left calculus needed for the standard localization (Step 2 of the node).
(blueprint: def-trf-uniform-filtered-homotopy-localization). -/
theorem uniformFilteredHomotopyQuasiIso_fractions (B : Option (ℤ × ℤ)) (bounded : Bool) :
    (uniformFilteredHomotopyQuasiIso C B bounded).HasLeftCalculusOfFractions := by
  sorry

attribute [instance] uniformFilteredHomotopyQuasiIso_fractions

/-- The restricted graded quasi-isomorphisms are compatible with the cone triangulation.
Source: Stacks, Tags 05RG and 05S6.
Proof: use the same graded-acyclic triangulated subcategory as in Step 2. Its cone class
is the graded quasi-isomorphisms by the graded cone criterion; the triangulated-subcategory
cone-system theorem gives compatibility with shifts and completion of triangle morphisms.
This argument takes place internally, so it retains all bounds.
(blueprint: def-trf-uniform-filtered-homotopy-localization). -/
theorem uniformFilteredHomotopyQuasiIso_triangulation
    (B : Option (ℤ × ℤ)) (bounded : Bool) :
    (uniformFilteredHomotopyQuasiIso C B bounded).IsCompatibleWithTriangulation := by
  sorry

attribute [instance] uniformFilteredHomotopyQuasiIso_triangulation

/-- The actual localization of the uniform filtered homotopy category at its graded
quasi-isomorphisms. Its triangulation is the standard localization of the inherited one.
Source: Stacks, Tag 05S6
(blueprint: def-trf-uniform-filtered-homotopy-localization). -/
abbrev UniformFiniteFilteredHomotopyLocalization (B : Option (ℤ × ℤ)) (bounded : Bool) :=
  (uniformFilteredHomotopyQuasiIso C B bounded).Localization

end CategoryTheory
