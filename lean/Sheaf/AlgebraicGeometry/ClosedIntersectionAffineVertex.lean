/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C3
-/
module

public import Sheaf.AlgebraicGeometry.ClosedIntersectionAugmentedRow

/-! Affine closed base change and the signed vertex insertion homotopy. -/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtaleTensorComparison

namespace AlgebraicGeometry.ClosedIntersection

/-- A single affine vertex supplies the prescribed base-change comparisons,
inverse restriction maps, and insertion homotopy for any augmented row.

Source: Stacks Project, Tags 09AA and 09AH, and the arbitrary-ring closed
base-change mate of lem-sf-ring-sheaf-base-change-mates; steps 5-7 of
lem-sfb-closed-intersection-vertex-contraction.
(blueprint: lem-sfb-closed-intersection-affine-vertex).

Proof: Each intersection is closed and has quasi-compact complementary open,
whose finiteness follows by taking a finite union of the original complementary
opens. Over the affine base all closed members are affine, so both bases of the
closed base-change square are qcqs. Apply the arbitrary-ring closed base-change
mate to each intersection, including Z at the empty index. Transport its module
objects to the actual inverse-image coefficient modules, retaining the specified
unit sections. Its inverse-image square is delta, its section formula gives
normalized, and the mate equation gives beta and mate.
The fibre product with vertex a is the intersection indexed by insert a s. This
follows from the product universal property for nonempty s; at the empty index
it follows because the vertex factors through the monomorphism Z into X. These
are unionIntersection. Transport the actual restrictions through these
comparisons to obtain intersectionRestriction. Naturality of the counit and
the composite-unit equation show that the transported faces are the same actual
unit faces. They prove restriction_units and faces. For the empty summand the
closed counit gives augmentation; its composite with the pulled-back unit is
the identity by the triangle equation. Adjoining a vertex already in the
intersection is the identity closed subscheme, so the restriction for adjoining
a is invertible. Choose its inverse as back. Both inverse equations follow.
Define h by its product projections. Its component at s is zero if a belongs to
s, and otherwise is (-1)^(number of b in s with b<a) times the projection at
insert a s followed by back s. Preservation of finite products by closed inverse
image makes this a natural module map. This gives component_zero and
component_insert, including the empty output and absent degrees.
Check the homotopy identity on each projection indexed by J. If a belongs to J,
only the term deleting a in dh survives and its two equal signs multiply to one;
the inverse equation makes it the identity. If a is absent, deletion of a in hd
gives the identity. For b in J, the other hd term and the corresponding dh term
have equal maps by the commuting restriction square. If k is the position of b,
their exponents are s_a(J)+k+[a<b] and k+s_a(J)-[b<a], which differ by one, so they
cancel over every coefficient ring. At degree -1 this is the inverse equation
for the augmentation; at the top degree every index contains a. Outside the
finite range both objects are zero. Product projections jointly detect equality,
so this proves contraction in every integer degree. Every construction uses
natural linear maps, and hence gives all the stated naturality. -/
theorem closed_intersection_affine_vertex {X Z : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] {m : ℕ} (W : Fin m → Over X)
    (hclosed : ∀ a, IsClosedImmersion (W a).hom)
    (hfactor : ∀ a, Nonempty (W a ⟶ Over.mk i))
    (hqc : ∃ U : X.Opens, Set.range U.ι = (Set.range i)ᶜ ∧ QuasiCompact U.ι)
    (hqcW : ∀ a, ∃ U : X.Opens,
      Set.range U.ι = (Set.range (W a).hom)ᶜ ∧ QuasiCompact U.ι)
    (A : Rings X) (D : Row i W A)
    [IsAffine X] (a : Fin m) : Nonempty (VertexContraction D a) := by sorry

end AlgebraicGeometry.ClosedIntersection
