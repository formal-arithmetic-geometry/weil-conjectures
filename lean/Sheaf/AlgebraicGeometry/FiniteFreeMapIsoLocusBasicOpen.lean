/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F4
-/
module

public import Sheaf.AlgebraicGeometry.ModuleMapIsoLocus
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free

/-! # The isomorphism locus in an affine finite free frame

Source: Stacks Project, Tag 05GD, Lemma 10.79.4(3), and Tag 0BDP, final sentence.
(blueprint: lem-sc-finite-free-map-iso-locus-basic-open)
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme.Modules

/-- In simultaneous finite free frames on an affine open, the locally invertible locus
is a basic open.
Source: Stacks Project, Tag 05GD, Lemma 10.79.4(3), local matrix argument, and
Tag 0BDP, final determinant sentence.
(blueprint: lem-sc-finite-free-map-iso-locus-basic-open)

Proof: Choose enumerations of the finite index types I and J. Transport the restriction
of the map through the two given frames. Its values on the basis sections give a matrix
with entries in the ring of sections on U, and restriction of that matrix to any smaller
open represents the restricted map. Compare tensor pullback along an open inclusion
with ordinary restriction using their common right adjoint, module pushforward.
If the two cardinalities agree, let f be the determinant of the square matrix. On the
basic open D(f), f is a unit and the adjugate matrix divided by f defines a sheaf inverse.
Thus every point of D(f) lies in moduleMapIsoLocus. Conversely, a point of U in that locus
has an open neighbourhood with a tensor-pullback inverse. Restrict this inverse to its
intersection with U and then take the stalk at the point. The matrices on the stalk are
mutually inverse, so the determinant of the original matrix is a unit in the local ring.
This says exactly that the point lies in D(f). If the cardinalities differ, take f = 0:
an inverse at a point would give an isomorphism of residue-field vector spaces with
different finite dimensions, which is impossible. Both sides are therefore empty.
This also covers an empty U (there are no points) and rank zero (the determinant of the
empty square matrix is 1). No reducedness or constant global rank is used. -/
theorem moduleMapIsoLocus_inter_eq_basicOpen_of_free {W : Scheme.{u}}
    {M N : W.Modules} (φ : M ⟶ N) (U : W.Opens) (hU : IsAffineOpen U)
    {I J : Type u} [Finite I] [Finite J]
    (eM : M.restrict U.ι ≅ SheafOfModules.free I)
    (eN : N.restrict U.ι ≅ SheafOfModules.free J) :
    ∃ f : W.presheaf.obj (.op U),
      (U : Set W) ∩ (moduleMapIsoLocus φ : Set W) = (W.basicOpen f : Set W) := by sorry

end AlgebraicGeometry.Scheme.Modules
