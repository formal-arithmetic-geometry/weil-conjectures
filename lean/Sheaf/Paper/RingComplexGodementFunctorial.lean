/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A3
-/
module

public import Sheaf.Paper.RingComplexGodementConstruction
import Sheaf.Paper.RingComplexGodementModelMaps

/-! # Functorial maps of the concrete Godement ring complex -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry

/-- The Godement mapping fibres form a strictly functorial augmented family.
Source: Stacks Project, Tag 099D(a),(b), via the concrete Godement construction,
Tag 0FKS. (blueprint: lem-weil-pbc-ring-complex-godement-functorial)

Proof: a ring map induces a map between the open complements, since a prime
contains the extended ideal precisely when its inverse image contains the original
ideal. Apply ringComplex_godement_model_maps to the structure-module coefficient map.
It gives extended cochain maps with strict identity and composition equations and
the actual germ-augmentation square. Take global sections; these operations
preserve those equations and the cochain equation.
Together with the coefficient homomorphism in degree zero this gives a square of
the restriction maps A[0] to Godement sections after restriction of scalars
from B to A. Restriction of scalars preserves finite biproducts and shifts, so
apply the mapping-cone map and inverse rotation, then identify its target with
the restriction of the B mapping fibre. On sections this is a semilinear map.
Its projection is the ring map, so the
augmentation square commutes. For an identity, the coordinate formula is the
identity; for a composite both formulas select the same point and apply the
composite stalk map. Thus identity and composition hold on the nose, including
all transports along equal ideals, by proof irrelevance. -/
theorem ringComplex_godement_functorial :
    ∃ m : RingComplexMaps (fun A I ↦ ringComplexGodement A I.val),
      RingComplexFunctorial (fun A I ↦ ringComplexGodement A I.val)
        (fun A I ↦ ringComplexGodementAugmentation A I.val) m := by sorry

end AlgebraicGeometry
