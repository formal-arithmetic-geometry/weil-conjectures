/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q42
-/
module

public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Sheaf.CategoryTheory.Sites.CoherentTopos
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Yoneda
import Mathlib.CategoryTheory.Sites.LocallySurjective
import WeilConjectures.AlgebraicGeometry.SiteSheafificationSectionsLocal

/-!
# Quasi-compactness of a site object and its sheafified representable

Source: Stacks Project, `sites.tex`, Tag 0D06 and Definition 090H
(blueprint: lem-trf-site-quasicompact-sheafification-criterion).
-/

@[expose] public section

set_option autoImplicit false
set_option warn.sorry false

universe u v

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-
The site condition is expressed using covering presieves of arrows.  The
finite-image requirement is the condition that the refinement uses only
finitely many members of the original covering family.
-/
/--
Source: Stacks Project, `sites.tex`, Tag 0D06 and Definition 090H
(blueprint: lem-trf-site-quasicompact-sheafification-criterion).

Proof plan (the two steps of the node).
1. Assume the finite-image refinement property.  Given an epimorphic
   coproduct of sheaves onto the sheafified representable, use
   lem-weil-pbc-site-sheaf-sets-epi-locally-surjective to lift the identity
   section on a covering.  A coproduct is the sheafification of the
   objectwise disjoint union, by def-weil-pbc-sheafification and its
   adjunction.  The local representation clause of
   lem-weil-pbc-site-sheafification-sections-local refines this covering so
   that every lift is a section of one summand.  Compose these coverings
   using def-weil-pbc-sites-and-cohomology.  Apply the finite-image
   refinement property, and restrict the chosen sections to its members.
   The summand indices now have finite image.  The corresponding maps from
   sheafified representables factor through these finitely many summands.
   To see that their family is epimorphic, locally represent any section of
   the sheafified representable by arrows to U, pull the refinement back
   along those arrows, and compose the covers.  Each restriction then
   lifts through the representable of a refinement member.  The local
   surjectivity criterion proves that the finite sub-coproduct is epi.
2. Conversely, given a covering, the sheafified representables of its
   members form an epimorphic family: represent sections locally by arrows
   to U and pull the covering back.  Quasi-compactness gives a finite
   sub-coproduct that is still epi.  Lift the identity locally using the
   same local-surjectivity criterion.  Refine the lifted coproduct sections
   to sections of individual sheafified representables, and then to actual
   arrows using the local representation clause of
   lem-weil-pbc-site-sheafification-sections-local twice.  The composite
   arrow to U and the structure arrow have the same sheafified image;
   its local equality clause gives one further covering where they agree.
   Compose all these coverings using def-weil-pbc-sites-and-cohomology.
   Their arrows lie over U, and their original-cover indices range inside
   the finite subfamily.  This is the required finite-image refinement.
-/
theorem site_quasiCompact_iff_sheafifiedYoneda_quasiCompact
    {C : Type u} [Category.{v} C]
    (J : Precoverage C) (_hJ : J.IsSiteForCoverings) (U : C) :
    (∀ (I : Type (max u v)) (U_i : I → C) (a : ∀ i, U_i i ⟶ U),
      Presieve.ofArrows U_i a ∈ J U →
        ∃ (K : Type (max u v)) (V : K → C) (b : ∀ k, V k ⟶ U)
          (α : K → I) (c : ∀ k, V k ⟶ U_i (α k)),
          Set.Finite (Set.range α) ∧
            (∀ k, c k ≫ a (α k) = b k) ∧
              Presieve.ofArrows V b ∈ J U) ↔
      IsQuasiCompactObject.{max u v}
        ((presheafToSheaf J.toGrothendieck (Type (max u v))).obj
          (uliftYoneda.{u}.obj U)) := by
  sorry

end CategoryTheory
