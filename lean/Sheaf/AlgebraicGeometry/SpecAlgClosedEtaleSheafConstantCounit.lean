/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Small
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
import Sheaf.AlgebraicGeometry.ConstantSheafSetSectionsConnectedNatural
import Sheaf.AlgebraicGeometry.EtaleFibreDiscreteSeparablePoints

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- The constant-sheaf counit is an isomorphism in the algebraically closed étale case.
Source: Stacks Project, Remark 59.23.2 (Tag 03P5).
(blueprint: lem-weil-pbc-spec-algebraically-closed-etale-sheaf-constant-counit).

Proof: An etale scheme over Ω is the disjoint union of its open singleton points,
by the discrete separable fibre theorem. Each residue extension is finite separable
and hence equals Ω, so each singleton is a copy of Spec Ω over the base. The sheaf
condition for this covering identifies G(U) with the product of G(Spec Ω), since
distinct singletons have empty intersections and a sheaf has one section on the
empty object. The constant sheaf with value G(Spec Ω) has the same product of
sections: its sections on each singleton are its value, by the connected constant
sheaf comparison. On each singleton the adjunction counit is the identity of that
value. Consequently its map on U is a product of bijections, including the empty
product, and thus a bijection. Componentwise bijectivity gives an isomorphism of
presheaves and hence of sheaves. -/
theorem spec_algClosed_etale_sheaf_constant_counit
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    (G : Sheaf ((Spec (CommRingCat.of Ω)).smallEtaleTopology) (Type (u + 1))) :
    IsIso ((constantSheafAdj (Spec (CommRingCat.of Ω)).smallEtaleTopology
      (Type (u + 1)) terminalIsTerminal).counit.app G) := by
  sorry

end AlgebraicGeometry.Scheme
