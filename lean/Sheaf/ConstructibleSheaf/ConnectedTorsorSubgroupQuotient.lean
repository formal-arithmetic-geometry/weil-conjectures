/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsor
public import WeilConjectures.AlgebraicGeometry.Morphisms.Finite.GeometricFiber
public import Mathlib.GroupTheory.Index
import Sheaf.AlgebraicGeometry.FundamentalGroup.FiberEquivalence
import Sheaf.AlgebraicGeometry.FundamentalGroup.LocallyConstantEquivalence
import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree

/-!
# Subgroup quotients of connected finite etale torsors

Source: Stacks Project, proof of Tag 0A3R, and Tag 0BND.
(blueprint: lem-weil-pbc-connected-torsor-subgroup-quotient)
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory Limits
namespace AlgebraicGeometry
open Etale

/-- The quotient of a connected finite Q-torsor by H is connected, of geometric
fibre cardinality [Q:H], and has the same total space as an H-torsor.
Source: Stacks Project, Tag 0A3R, proof at T = Y/H; Tag 0BND (1), (3).
(blueprint: lem-weil-pbc-connected-torsor-subgroup-quotient)

Proof:
1. Choose a geometric point of U and a lift to c.P. The fibre is the regular
Q-set, with the fundamental group acting through a surjection onto Q because
c.P is connected. The quotient of the regular fibre by the deck action of H is the coset set
H\Q (identified by inversion with Q/H). The commuting monodromy action remains
transitive. This finite continuous fundamental-group set corresponds under the finite etale
Galois equivalence to a connected finite etale map v : V -> U.
2. The quotient map c.P -> V is induced by the equivariant projection from the
regular fibre to its H-orbits.
The H action on c.P gives an H-torsor over V: on the chosen geometric fibre
the map H times Q -> Q times_(H\Q) Q is a bijection. The fibre functor reflects
isomorphisms, so the corresponding scheme map is an isomorphism. The quotient
is surjective because its image on the fibre is surjective. Use the same total
space for cH; e can then be the identity, and the displayed square commutes.
3. Every geometric fibre of v has the cardinality of H\Q: fibre functors at
any two geometric points of connected U are isomorphic. This applies also to
separably closed fields, since finite etale algebras split over such fields.
Its cardinality is the subgroup index. The construction works for H = 1,
H = Q, and Q = 1 without a nonzero-rank hypothesis. -/
theorem Scheme.GaloisCover.exists_connected_subgroup_quotient
    {U : Scheme.{u}} [ConnectedSpace U]
    (Q : Type u) [Group Q] [Finite Q]
    (c : Scheme.GaloisCover (ULift.{u + 1} Q) U) [ConnectedSpace c.P]
    (H : Subgroup Q) :
    ∃ (V : Scheme.{u}) (v : V ⟶ U) (_ : IsFinite v) (_ : Etale v)
      (_ : ConnectedSpace V),
      (∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ U),
        Nat.card (v.GeometricFiber s) = H.index) ∧
      ∃ (cH : Scheme.GaloisCover (ULift.{u + 1} H) V) (_ : ConnectedSpace cH.P)
        (e : cH.P ≅ c.P), e.hom ≫ c.π = cH.π ≫ v := by sorry

end AlgebraicGeometry
