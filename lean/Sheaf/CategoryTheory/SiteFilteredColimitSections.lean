/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.CategoryTheory.Sites.Finite
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.CategoryTheory.Limits.Types.Colimits
import Mathlib.Algebra.Category.Grp.Colimits

/-!
# Sections of filtered colimits on sites with finite coverings

Source: Stacks Project, Sites, Lemma 0738(4), and Modules on Sites, Lemma 03CO
(blueprint: lem-weil-pbc-site-filtered-colimit-sections-finite-coverings).
-/

universe u

open CategoryTheory.Limits Opposite

namespace CategoryTheory

/-- On a site with finite covering presieves, the canonical map from the filtered
colimit of sections to the sections of a given sheaf colimit is bijective.
Source: Stacks Project, Sites, Lemma 0738(4)
(blueprint: lem-weil-pbc-site-filtered-colimit-sections-finite-coverings).

Proof:
1. Form the sectionwise presheaf colimit P, with its restriction maps and coprojections,
using lem-weil-pbc-presheaf-colimits-sectionwise.
2. For each finite covering, its sheaf condition is a finite limit: the equalizer of the
products over covering arrows and their pairwise fibre products. These fibre products exist
by def-weil-pbc-sites-and-cohomology. By
lem-weil-pbc-filtered-colimits-commute-finite-limits, the sectionwise filtered colimit of
the sheaf conditions is the sheaf condition for P. Thus P is a sheaf, including for empty
coverings (the empty finite limit).
3. Sheaves form a full subcategory of presheaves, so the presheaf colimit's universal
property makes P a colimit in sheaves, by def-weil-pbc-category-colimit.
4. The unique colimit comparison isomorphism from P to c.pt has component at U equal
to the canonical map: both have the prescribed composites with all coprojections.
Its component is bijective, by def-weil-pbc-category-colimit. -/
theorem siteFilteredColimit_sections_bijective
    {C : Type u} [SmallCategory C] (J : Precoverage C)
    [J.HasIsos] [J.IsStableUnderComposition] [J.IsStableUnderBaseChange] [J.HasPullbacks]
    (hfinite : J ≤ Precoverage.finite C)
    {Λ : Type u} [SmallCategory Λ] [IsFiltered Λ]
    (D : Λ ⥤ Sheaf J.toGrothendieck (Type u))
    (c : Cocone D) (hc : IsColimit c) (U : C) :
    Function.Bijective
      (colimit.desc (D ⋙ (sheafSections J.toGrothendieck (Type u)).obj (op U))
        (((sheafSections J.toGrothendieck (Type u)).obj (op U)).mapCocone c)) := by
  sorry

/-- For abelian sheaves on a site with finite coverings, the canonical map from the
filtered colimit of section groups to the sections of a given sheaf colimit is an isomorphism.
Source: Stacks Project, Sites, Lemma 0738(4), and Modules on Sites, Lemma 03CO
(blueprint: lem-weil-pbc-site-filtered-colimit-sections-finite-coverings).

Proof:
1. Form the sectionwise abelian presheaf colimit P using
lem-weil-pbc-presheaf-colimits-sectionwise.
2. The sheaf condition is the finite equalizer diagram of the covering sections and
sections of their pairwise fibre products (def-weil-pbc-sites-and-cohomology).
By the abelian-group clause of lem-weil-pbc-filtered-colimits-commute-finite-limits,
P satisfies this condition for every finite covering and is an abelian sheaf.
3. Fullness of the abelian sheaf subcategory restricts the presheaf colimit universal
property to sheaves, by def-weil-pbc-category-colimit.
4. Compare P with the given colimit c by the unique colimit isomorphism. Its component
at U equals the canonical homomorphism, since its composites with the section coprojections
are c's section coprojections. That component is an isomorphism of abelian groups,
by def-weil-pbc-category-colimit. -/
theorem siteFilteredColimit_sections_isIso
    {C : Type u} [SmallCategory C] (J : Precoverage C)
    [J.HasIsos] [J.IsStableUnderComposition] [J.IsStableUnderBaseChange] [J.HasPullbacks]
    (hfinite : J ≤ Precoverage.finite C)
    {Λ : Type u} [SmallCategory Λ] [IsFiltered Λ]
    (D : Λ ⥤ Sheaf J.toGrothendieck AddCommGrpCat.{u})
    (c : Cocone D) (hc : IsColimit c) (U : C) :
    IsIso
      (colimit.desc (D ⋙ (sheafSections J.toGrothendieck AddCommGrpCat.{u}).obj (op U))
        (((sheafSections J.toGrothendieck AddCommGrpCat.{u}).obj (op U)).mapCocone c)) := by
  sorry

end CategoryTheory
