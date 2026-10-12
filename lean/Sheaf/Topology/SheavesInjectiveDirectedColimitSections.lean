/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
module

public import Mathlib.Topology.Sheaves.Sheaf
public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import Mathlib.Topology.Compactness.Compact
import Sheaf.Paper.SiteSheafificationSectionsLocal

/-!
# Sections of directed colimits with injective transition maps

Source: Stacks Project, Sheaves, Lemma 009F, parts (1) and (3)
(blueprint: lem-weil-pbc-sheaves-injective-directed-colimit-qc-sections).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace TopCat

/-- Source: Stacks Project, Sheaves, Lemma 009F, parts (1) and (3)
(blueprint: lem-weil-pbc-sheaves-injective-directed-colimit-qc-sections).

1. Identify the colimit cocone with the sheafification of the sectionwise presheaf
colimit, using `lem-weil-pbc-sheaves-colimit-sheafification`,
`def-weil-pbc-sheafification` and uniqueness of colimits (`def-weil-pbc-category-colimit`).
2. By `lem-weil-pbc-filtered-colimit-sets-elementwise`, injective transition maps make
all presheaf coprojections injective. Represent two sections at one common index;
if they agree locally, their representatives agree locally and hence globally by the
sheaf axiom (`def-weil-pbc-sites-and-cohomology`). Thus the presheaf colimit is separated.
3. The local-equality clause of `lem-weil-pbc-site-sheafification-sections-local` makes
the map from this separated presheaf to its sheafification injective. Composing with
the presheaf coprojections gives injectivity of every leg on every open.
4. By the local-lifting clause of `lem-weil-pbc-site-sheafification-sections-local`
and elementwise representation in a filtered colimit, each section of the colimit
sheaf locally comes from a section of one of the diagram sheaves.
5. On a quasi-compact open choose a finite subcover and a common upper index (also
when the open is empty, using nonemptiness of the index set). Transport all local
lifts to that index. They agree on overlaps by injectivity of the colimit leg, so
glue by the sheaf axiom. The glued section maps to the given section. Consequently
the canonical map from the colimit of sections is surjective and, by step 3,
injective, hence bijective. -/
theorem sheaves_injective_directedColimit_sections
    (X : TopCat.{u}) (I : Type u) [Preorder I] [Nonempty I]
    [IsDirected I (· ≤ ·)] (D : I ⥤ TopCat.Sheaf (Type u) X)
    (hinj : ∀ (i i' : I) (h : i ≤ i') (W : Opens X),
      Function.Injective ((D.map (homOfLE h)).1.app (op W)))
    (c : Cocone D) (hc : IsColimit c) :
    (∀ (W : Opens X) (i : I), Function.Injective ((c.ι.app i).1.app (op W))) ∧
    (∀ (U : Opens X), IsCompact (U : Set X) →
      (∀ t : c.pt.obj.obj (op U),
        ∃ (i : I) (s : (D.obj i).obj.obj (op U)), (c.ι.app i).1.app (op U) s = t) ∧
      Function.Bijective
        (colimit.desc (D ⋙ TopCat.Sheaf.forget (Type u) X ⋙
          (evaluation (Opens X)ᵒᵖ (Type u)).obj (op U))
          ((TopCat.Sheaf.forget (Type u) X ⋙
            (evaluation (Opens X)ᵒᵖ (Type u)).obj (op U)).mapCocone c))) := by
  sorry

end TopCat
