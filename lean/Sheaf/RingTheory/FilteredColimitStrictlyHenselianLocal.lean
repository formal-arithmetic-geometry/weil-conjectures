/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N6
-/
module

public import WeilConjectures.Mathlib.RingTheory.Henselian
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.Order.Directed
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
import Mathlib.FieldTheory.Separable
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import WeilConjectures.RingTheory.HenselianLocalRootLifting
import Sheaf.RingTheory.FilteredColimitFiniteData

/-!
# Directed colimits of strictly henselian local rings

Source: Stacks Project, Algebra, Tag 04GI, `lemma-colimit-henselian`, strictly henselian case
(blueprint: lem-sfb-filtered-colimit-strictly-henselian-local).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace CommRingCat

/-- A nonempty directed colimit of strictly henselian local rings with local transition
maps is strictly henselian local. Locality is expressed by the inverse image of the
maximal ideal, exactly as in the node. The transition maps need not be injective or
surjective.

Source: Stacks Project, Algebra, Tag 04GI, `lemma-colimit-henselian`, strictly henselian case
(blueprint: lem-sfb-filtered-colimit-strictly-henselian-local).

Proof for stage 3:
1. Write alpha_i for the colimit maps and M for the union of their maximal-ideal images.
   By `lem-pc-filtered-colimit-commrings-elementwise`, representatives and equalities can
   be moved to common stages. This makes M an ideal. If alpha_i(x) = alpha_j(y) with
   y in the maximal ideal at j, equality at a common stage and locality imply that x
   is in the maximal ideal at i. Thus the inverse image of M at i is that maximal
   ideal, and M is proper, using a stage supplied by nonemptiness.
2. Represent any element outside M at a stage. Its representative is outside that
   stage's maximal ideal, hence is a unit by `lem-weil-pbc-local-ring-unit-criterion`.
   Its inverse maps to an inverse in the colimit. Therefore M is the unique maximal
   ideal and the colimit is local; all colimit legs are local as well.
3. The local maps induce compatible maps of residue fields. The map from each residue
   field to R/M is injective by the contraction equality in step 1. These maps exhibit
   R/M as the ring colimit: a compatible family of maps from the residue fields gives
   a map from R by its universal property, kills M, and factors uniquely through R/M.
4. For a nonconstant separable polynomial over R/M, choose a Bezout identity with its
   derivative, by `def-pc-separable-polynomial`. Descend all coefficients and the finite
   equations of that identity using `lemma-nagata-filtered-colimit-finite-data`.
   A nonzero positive-degree coefficient stays nonzero at its representative stage.
   The descended polynomial is nonconstant and separable and has a root there by
   `def-pc-separably-closed` and strict henselianity of that stage. Its image is a root
   of the original polynomial. Consequently R/M is separably closed.
5. Given a monic polynomial over R and a simple residue root, descend its coefficients
   below the leading term by `lemma-nagata-filtered-colimit-finite-data` and form a
   monic lift of the same degree. Represent the residue root at a stage by
   `lem-pc-filtered-colimit-commrings-elementwise` for the residue-field colimit.
   Move both choices to a common stage.
6. Evaluation and differentiation commute with these maps. Injectivity of the
   residue-field map implies that the descended residue root is a root; its
   derivative is nonzero because its image is nonzero. Apply the simple-root lifting
   direction of `lem-weil-pbc-henselian-local-root-lifting` at that stage. Mapping the
   lifted root into R gives a root with the prescribed residue.
7. The converse direction of `lem-weil-pbc-henselian-local-root-lifting` makes R
   henselian. Together with the separably closed residue field in step 4, this is
   strict henselianity by `def-weil-pbc-henselian-terminology`. -/
theorem isStrictlyHenselianLocalRing_colimit_of_local_maps
    {I : Type u} [PartialOrder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (F : I ⥤ CommRingCat.{u}) [∀ i : I, IsStrictlyHenselianLocalRing (F.obj i)]
    (hlocal : ∀ (i j : I) (hij : i ≤ j),
      (IsLocalRing.maximalIdeal (F.obj j)).comap (F.map (homOfLE hij)).hom =
        IsLocalRing.maximalIdeal (F.obj i)) :
    IsStrictlyHenselianLocalRing ↑(CategoryTheory.Limits.colimit F) := by
  sorry

end CommRingCat
