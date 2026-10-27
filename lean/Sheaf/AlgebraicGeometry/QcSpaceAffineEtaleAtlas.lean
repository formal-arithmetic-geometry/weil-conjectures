/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q151
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceAffineEtaleCover
public import Mathlib.AlgebraicGeometry.AffineScheme
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFiniteAffineSubatlas
import Mathlib.AlgebraicGeometry.Limits

/-!
# An affine étale atlas of a quasi-compact algebraic space

Source: Stacks Project, Properties of Spaces, Tag 03H6,
`lemma-quasi-compact-affine-cover`, forward implication
(blueprint: lem-sfb-qc-space-affine-etale-atlas).

The topology on field-valued point classes is the existing `pointTopologicalSpace`,
which agrees with the quotient topology of a surjective étale scheme atlas.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.AlgebraicSpace

/-- A quasi-compact algebraic space over any scheme has an affine representable
surjective étale scheme atlas. Affineness is absolute, with no separatedness or
quasi-separatedness hypothesis on the space or base.

Source: Stacks Project, Properties of Spaces, Tag 03H6,
`lemma-quasi-compact-affine-cover`, forward implication
(blueprint: lem-sfb-qc-space-affine-etale-atlas).

Proof:
1. By `lem-a1-space-affine-etale-cover`, choose a representable surjective étale atlas
   `p : h_U → X` with `U` a disjoint union of affine schemes. Its point map is
   surjective and its quotient topology is the stipulated topology on `|X|`.
2. Apply `lem-a1-space-finite-affine-subatlas` to this atlas and the compactness of
   `|X|`. A finite subset of its affine components has union `W` whose restriction
   `h_W → X` is still representable surjective étale. The structure morphism to `S`
   is restricted from `U`. No assertion about intersections of affine opens is used.
3. By `lem-weil-pbc-finite-affine-coproduct-spectrum`, writing these components as
   `Spec A_d` identifies their finite coproduct with the spectrum of the product of
   the `A_d`. Thus `W` is affine. For empty `X`, the finite subset may be empty;
   its coproduct is the spectrum of the zero ring, so the same argument applies.
The source proof's final phrase "finite surjective" is a typo for "étale surjective";
the statement of Tag 03H6 and the present conclusion assert étale surjectivity. -/
theorem exists_affine_etale_atlas_of_compactSpace {S : Scheme.{u}} (X : AlgebraicSpace S)
    (hX : CompactSpace (Point X.obj.obj)) :
    ∃ (W : Over S) (p : yoneda.obj W ⟶ X.obj.obj),
      IsAffine W.left ∧ IsRepresentable p ∧ IsSurjective p ∧ IsEtale p := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
