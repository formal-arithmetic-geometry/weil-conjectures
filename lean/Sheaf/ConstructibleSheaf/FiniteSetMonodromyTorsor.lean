/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U2
-/
module

public import Sheaf.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsor

/-!
# Connected monodromy torsors for finite sheaves of sets

Source: Stacks Project, Tags 0DV5 (1), 0DV6, and Section 03SF.
(blueprint: lem-weil-pbc-finite-set-monodromy-torsor)
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

/-- A finite locally constant sheaf of sets becomes constant on its connected monodromy
 torsor. Source: Stacks Project, Tags 0DV5 (1), 0DV6, and Section 03SF.
(blueprint: lem-weil-pbc-finite-set-monodromy-torsor)

Proof: choose a geometric point of the nonempty connected scheme U. The finite etale
and finite locally constant equivalence and the fundamental-group equivalence identify F
with a finite discrete set S acted on continuously by the fundamental group. The image
Q in the permutation group of S is finite. Its kernel is open: it is the intersection
of the finitely many open stabilizers of elements of S. It is normal because it is a
kernel. Shrink Q to Type u and transport its group structure. Under the Galois
correspondence, the regular transitive action on Q gives a connected finite etale
cover. Commuting right translations, converted to a left action by inversion, give
a Q-torsor. Transport this latter action to ULift Q. Base change to this cover restricts
the action on S to the kernel, where it is trivial. Compatibility of the equivalences with
inverse image
identifies this pullback with the constant sheaf of S. For the empty set S the image
is the trivial group and the cover is the identity; the same argument applies. -/
theorem exists_connected_torsor_constant_set_pullback
    {U : Scheme.{u}} [ConnectedSpace U]
    (F : Sheaf U.smallEtaleTopology (Type (u + 1)))
    (hF : IsFiniteLocallyConstantEtaleSheafOfSets F) :
    ∃ (Q : Type u) (_ : Group Q) (_ : Finite Q)
      (c : GaloisCover (ULift.{u + 1} Q) U) (_ : ConnectedSpace c.P),
      ((etaleSetPullback c.π).obj F).IsConstant c.P.smallEtaleTopology := by sorry

end AlgebraicGeometry.Scheme
