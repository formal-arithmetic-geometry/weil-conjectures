/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q132
-/
module

public import Sheaf.Algebra.Homology.UniformFilteredHomotopyLocalization
public import Mathlib.CategoryTheory.Triangulated.Subcategory
import Sheaf.Algebra.Homology.FilteredConeLocalization
import Sheaf.Algebra.Homology.FilteredBoundedLocalizationComparison

/-!
# Bounded filtered localization embeds in bounded-below filtered localization

Source: Stacks Project, Derived Categories, Tags 05S5 and 05S6, parts (1) and (3)
(blueprint: lem-trf-bounded-filtered-localization-embedding).

The categories carry the inherited cone triangulations and their standard localizations.
`B = none` permits a uniform interval depending on the complex; `B = some (a,b)` fixes it.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe v u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

variable (C : Type u) [Category.{v} C] [Abelian C]

/-- The inclusion of bounded into bounded-below uniformly finite filtered complexes.
Source: Stacks, Tag 05S6
(blueprint: lem-trf-bounded-filtered-localization-embedding). -/
def boundedFilteredHomotopyInclusion (B : Option (ℤ × ℤ)) :
    UniformFiniteFilteredHomotopy C B true ⥤ UniformFiniteFilteredHomotopy C B false :=
  (uniformFilteredHomotopyProperty C B false).lift
    (uniformFilteredHomotopyProperty C B true).ι
    (fun K ↦ ⟨K.property.1, fun h ↦ Bool.noConfusion h⟩)

/-- The inclusion with its canonical shift comparison inherited from the ambient category.
Source: Stacks, Tags 014X and 05S6
(blueprint: lem-trf-bounded-filtered-localization-embedding). -/
instance boundedFilteredHomotopyInclusion_commShift (B : Option (ℤ × ℤ)) :
    (boundedFilteredHomotopyInclusion C B).CommShift ℤ :=
  inferInstanceAs (((uniformFilteredHomotopyProperty C B false).lift
    (uniformFilteredHomotopyProperty C B true).ι
    (fun K ↦ ⟨K.property.1, fun h ↦ Bool.noConfusion h⟩)).CommShift ℤ)

/-- Inclusion preserves the graded quasi-isomorphisms since all graded maps are unchanged.
Source: Stacks, Tag 05S6
(blueprint: lem-trf-bounded-filtered-localization-embedding). -/
def boundedFilteredHomotopyLocalizer (B : Option (ℤ × ℤ)) :
    LocalizerMorphism (uniformFilteredHomotopyQuasiIso C B true)
      (uniformFilteredHomotopyQuasiIso C B false) where
  functor := boundedFilteredHomotopyInclusion C B
  map _ _ _ hf := hf

/-- The localizer morphism uses the inclusion's canonical shift comparison.
Source: Stacks, Tags 014X and 05S6
(blueprint: lem-trf-bounded-filtered-localization-embedding). -/
instance boundedFilteredHomotopyLocalizer_commShift (B : Option (ℤ × ℤ)) :
    (boundedFilteredHomotopyLocalizer C B).functor.CommShift ℤ :=
  inferInstanceAs ((boundedFilteredHomotopyInclusion C B).CommShift ℤ)

/-- The canonical comparison obtained by localizing the actual inclusion.
Source: Stacks, Tag 05S6
(blueprint: lem-trf-bounded-filtered-localization-embedding). -/
def boundedFilteredLocalizationEmbedding (B : Option (ℤ × ℤ)) :
    UniformFiniteFilteredHomotopyLocalization C B true ⥤
      UniformFiniteFilteredHomotopyLocalization C B false :=
  (boundedFilteredHomotopyLocalizer C B).localizedFunctor
    (uniformFilteredHomotopyQuasiIso C B true).Q
    (uniformFilteredHomotopyQuasiIso C B false).Q

/-- The descended shift comparison is the localization of the inclusion's comparison.
Source: Stacks, Tags 05R7 and 05S6
(blueprint: lem-trf-bounded-filtered-localization-embedding). -/
instance boundedFilteredLocalizationEmbedding_commShift (B : Option (ℤ × ℤ)) :
    (boundedFilteredLocalizationEmbedding C B).CommShift ℤ :=
  inferInstanceAs (((boundedFilteredHomotopyLocalizer C B).localizedFunctor
    (uniformFilteredHomotopyQuasiIso C B true).Q
    (uniformFilteredHomotopyQuasiIso C B false).Q).CommShift ℤ)

/-- Bounded uniformly finite filtered localization embeds fully faithfully and exactly
in bounded-below uniformly finite filtered localization, for unrestricted finite intervals
and for every fixed interval. The triangulations and comparison are the canonical ones.
Source: Stacks, Tag 05S6(1),(3), using 05S5(2).
Proof (Steps 1--6 of the node).
1. The uniform homotopy subcategories inherit the cone triangulation: zero, shifts and
   cones retain uniform finite filtration bounds and the indicated cochain bounds.
2. Graded-acyclic objects form a triangulated subcategory. The graded cone criterion
   identifies its cone class with graded quasi-isomorphisms and supplies fractions.
3. Triangulated localization supplies both localization triangulations. The universal
   property descends the inclusion since it preserves graded quasi-isomorphisms.
4. For fullness, write an ambient morphism as a right roof X <- Z -> Y. Choose N above
   the cochain support of X and Y. The denominator forces graded cohomology of Z above
   N to vanish. The good upper truncation of 05S5(2), as stated in
   lem-trf-filtered-bounded-localization-comparison, gives a bounded T -> Z in W.
   Precompose both roof legs with it; the resulting bounded roof has the same image.
5. For faithfulness, use lem-pc-right-fraction-common-refinement on two equal ambient
   roofs. Their common denominator to bounded X transfers its upper cohomology bound
   to the refinement R. Truncate R above that bound. The resulting bounded refinement
   witnesses equality in the bounded localization. Homotopies are the same in the full
   subcategory. This proves injectivity of each Hom map.
6. The inclusion and localizations commute with shifts, so their comparison descends.
   Common denominators compute sums of roofs, proving additivity. Every distinguished
   localized triangle is isomorphic to the localization of a distinguished homotopy
   triangle. Inclusion preserves that triangle and localization preserves its image,
   proving exactness. Every construction retains a specified interval [a,b]; thus the
   same arguments prove the fixed-interval assertion as well as the unrestricted one.
(blueprint: lem-trf-bounded-filtered-localization-embedding). -/
theorem boundedFilteredLocalizationEmbedding_fullyFaithful_exact
    (B : Option (ℤ × ℤ)) (_hB : ∀ a b : ℤ, B = some (a, b) → a ≤ b) :
    Nonempty (boundedFilteredLocalizationEmbedding C B).FullyFaithful ∧
      (boundedFilteredLocalizationEmbedding C B).Additive ∧
      (boundedFilteredLocalizationEmbedding C B).IsTriangulated := by
  sorry

end CategoryTheory
