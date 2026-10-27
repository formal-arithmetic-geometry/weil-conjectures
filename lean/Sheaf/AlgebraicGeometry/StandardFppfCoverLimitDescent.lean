/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q139
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.CategoryTheory.Comma.Over.Pullback
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
import WeilConjectures.AlgebraicGeometry.LimitAffineTransition
import Sheaf.AlgebraicGeometry.FinitePresentationFamilyDescent
import WeilConjectures.AlgebraicGeometry.DescendAffine
import WeilConjectures.AlgebraicGeometry.DescendFlatFinitePresentation
import WeilConjectures.AlgebraicGeometry.FiniteFamilyJointSurjectivityStage

/-!
# Standard fppf coverings descend through affine inverse limits

Source: Stacks Project, Topologies, Tag 049N, lemma-limit-fppf-topology, clause (1),
for the fppf topology; Tag 021Q, definition-standard-fppf.
(blueprint: lem-sfb-standard-fppf-cover-limit-descent)
-/

@[expose] public section

universe u v

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- A finite affine flat locally finitely presented covering of an affine inverse limit
is the base change, with its original labels, of such a covering at one stage.
The index type of the covering may be empty. The last conjunct gives isomorphisms in
`Over c.pt.left`, so they commute with the covering maps to the limit.

Source: Stacks Project, Topologies, Tag 049N, lemma-limit-fppf-topology, clause (1),
fppf case; Tag 021Q, definition-standard-fppf.
(blueprint: lem-sfb-standard-fppf-cover-limit-descent)

Proof:
1. Forget the maps to S. Nonempty directedness makes the indexing category connected,
   so the underlying cone of schemes is limiting. Its affine stages have affine
   transition maps (pqf-lem-affine-local-target). By lem-weil-pbc-limit-affine-transition
   the limit is affine. Affine schemes are qcqs by lem-weil-pbc-affine-scheme-qcqs;
   maps between them are affine, hence qcqs by lem-weil-pbc-affine-morphism-permanence.
   Thus the locally finitely presented covering maps are finitely presented.
2. Apply lem-weil-pbc-finite-presentation-family-descent to obtain one stage i0,
   finite-presentation models with qcqs sources, and cartesian identifications with
   every original component. Base change preserves these properties by
   lem-weil-pbc-qcqs-morphism-permanence. The identity of the base is finitely presented.
3. For each label apply lem-weil-pbc-descend-affine and
   lem-weil-pbc-descend-flat-finite-presentation to its model morphism. Choose a common
   upper bound i1 of their finitely many stages. Affineness and flatness persist by
   lem-weil-pbc-affine-morphism-permanence and lem-weil-pbc-flat-morphism-base-change;
   an affine morphism to the affine stage has affine source. For no labels take i1=i0.
4. Apply lem-weil-pbc-finite-family-joint-surjectivity-stage with target the identity
   scheme at i1. The limit maps are jointly surjective by the covering hypothesis;
   the lemma gives a later stage i2 where the model family is jointly surjective.
   It also covers the empty family: in that case the stage i2 has no points.
5. Pull the models to i2. Their affineness, flatness and local finite presentation
   persist under base change. Cartesian-square pasting
   (lem-weil-pbc-cartesian-square-pasting) identifies each pullback to the limit with
   the original component over the limit, preserving every label. Composing the
   structure maps with the maps to S makes these also identifications over S. -/
theorem exists_standardFppfCover_stage
    (S : Scheme.{u}) {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Over S) (hD : ∀ i : Iᵒᵖ, IsAffine (D.obj i).left)
    (c : Cone D) (hc : IsLimit c)
    {κ : Type v} [Finite κ] (V : κ → Over c.pt.left)
    (hV : ∀ a : κ, IsAffine (V a).left)
    (hflat : ∀ a : κ, Flat (V a).hom)
    (hlfp : ∀ a : κ, LocallyOfFinitePresentation (V a).hom)
    (hcov : ∀ x : c.pt.left, ∃ a : κ, ∃ y : (V a).left, (V a).hom y = x) :
    ∃ (i : I) (W : κ → Over (D.obj (op i)).left),
      (∀ a : κ, IsAffine (W a).left) ∧
      (∀ a : κ, Flat (W a).hom) ∧
      (∀ a : κ, LocallyOfFinitePresentation (W a).hom) ∧
      (∀ x : (D.obj (op i)).left,
        ∃ a : κ, ∃ y : (W a).left, (W a).hom y = x) ∧
      ∀ a : κ,
        Nonempty ((Over.pullback (c.π.app (op i)).left).obj (W a) ≅ V a) := by
  sorry

end AlgebraicGeometry.Scheme
