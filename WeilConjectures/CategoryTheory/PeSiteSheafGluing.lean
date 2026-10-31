/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Sites.Descent.DescentData
public import Mathlib.CategoryTheory.Sites.PseudofunctorSheafOver
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.CategoryTheory.Sites.Limits

/-!
# Effective gluing of sheaves of sets on localized sites

Source: Stacks Project, `sites.tex`, Tag 04TR, `lemma-glue-sheaves` and the
preceding gluing datum (blueprint: lem-pe-site-sheaf-gluing).
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- Effective gluing of sheaves of sets on the slices of a site.

Source: Stacks Project, `sites.tex`, Tag 04TR, `lemma-glue-sheaves`, with the
compatible gluing datum immediately preceding the lemma
(blueprint: lem-pe-site-sheaf-gluing).

The `DescentData` structure records, for every pair of members of the covering,
the isomorphism after restriction to every common object, including equal
indices, together with its diagonal normalization and the triple cocycle.
Thus it is the intrinsic formulation of the displayed overlap isomorphisms
`φ_ij` on `U_i ×_U U_j`; it is available without assuming arbitrary pullbacks,
because the site axiom supplies the pullbacks needed for a covering family.
The conclusion says that this datum is induced by a sheaf on `C/U`, and that
the resulting component isomorphisms are compatible with every overlap.

Proof: the site covering-pullback axiom supplies the double and triple
intersections and their covering families.  Base-changing the local sheaves
to `C/U` gives sheaves `H_i` and `K_ij`.  Sectionwise products and the
finite equalizer of the two transition maps are sheaves by
`lem-weil-pbc-site-sheaf-sets-limits-sectionwise`; its sections are compatible
tuples.  Pulling the cocycle to the triple diagonal and cancelling an
automorphism gives diagonal normalization.  Graph pullback defines the maps
`e_i` and the cocycle defines their inverses; the two composites and naturality
are checked sectionwise.  Pulling the tuple equations to the double-overlap
graph gives `φ_ij ≫ e_i = e_j`.
-/
theorem peSiteSheafGluing
    {C : Type u} [Category.{v} C]
    (J : Precoverage C) (_hJ : J.IsSiteForCoverings)
    {I : Type (max u v)} (U : C) (X : I → C)
    (f : ∀ i, X i ⟶ U)
    (_hcover : Presieve.ofArrows X f ∈ J U) :
    ∀ D :
        (J.toGrothendieck.pseudofunctorOver (Type (max u v))).DescentData f,
      ∃ F : Sheaf (J.toGrothendieck.over U) (Type (max u v)),
        Nonempty
          (D ≅
            ((J.toGrothendieck.pseudofunctorOver (Type (max u v))).toDescentData f).obj F) := by
  sorry

end CategoryTheory
