/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.ResidueField

/-!
# Residue fields under a closed immersion

Source: Stacks Project, Schemes, Section 26.4 (Tag 01HJ), and Morphisms,
Lemma 29.2.1 (Tag 01QO) (blueprint: lem-weil-pbc-closed-immersion-residue-field-iso).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- A closed immersion induces an isomorphism `κ(i(z)) → κ(z)` on residue fields.
Source: Stacks Project, Schemes, Tag 01HJ-area, and Morphisms, Lemma Tag 01QO.
(blueprint: lem-weil-pbc-closed-immersion-residue-field-iso)

Proof:
1. Put `A = O_{X,i(z)}` and `B = O_{Z,z}`. By `def-weil-closed-immersion`, the
   structure-sheaf map is surjective. By `lem-weil-pbc-locally-surjective-iff-stalks`,
   its map on stalks at `i(z)` is surjective. The bijection in clause (2) of
   `lem-weil-pbc-closed-pushforward-stalks` identifies the pushforward stalk with `B`.
   The germ formula identifies the composite with `i.stalkMap z`. It is local by
   `def-weil-locally-ringed-space-morphism`, so this is a surjective local map `A → B`.
2. By `def-weil-residue-field`, the induced map is `A/m_A → B/m_B`. Surjectivity of
   `A → B` gives surjectivity of this quotient map. Locality says that the inverse
   image of `m_B` is `m_A`, so the quotient map has zero kernel. Thus it is bijective
   and hence an isomorphism of residue fields. -/
theorem Hom.isIso_residueFieldMap_of_isClosedImmersion {Z X : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] (z : Z) : IsIso (i.residueFieldMap z) := by
  sorry

end AlgebraicGeometry.Scheme
