/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q103
-/
module

public import Sheaf.AlgebraicGeometry.SchemeCardinalSize
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.Topology.Defs.Filter
import Mathlib.SetTheory.Cardinal.Arithmetic

/-! # Scheme size for a quasi-compact locally finite type source

Source: Stacks Project, sets.tex, Tag 04T7, lemma-bound-finite-type
(blueprint: lem-sfb-qc-lft-scheme-size-bound).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- A locally finite type morphism with quasi-compact source bounds the size of the source
by the size of the target. No quasi-compactness or quasi-separatedness of the target, or
quasi-compactness of the morphism, is assumed.

Source: Stacks Project, sets.tex, Tag 04T7, lemma-bound-finite-type
(blueprint: lem-sfb-qc-lft-scheme-size-bound).

Proof plan:
1. Put κ = cardinalSize S, so ℵ₀ ≤ κ. By [lem-weil-pbc-affine-opens-basis], cover S by affine
opens V = Spec A. The definition [def-weil-finite-type-morphism] covers each preimage by
affine opens U = Spec B with B finitely generated over A. These charts cover X, so
[def-weil-pbc-quasi-compact-scheme] selects finitely many Uᵢ, with corresponding Vᵢ = Spec Aᵢ
and Uᵢ = Spec Bᵢ [def-weil-affine-spectrum]. The family may be empty. Neither the preimages
nor f need be quasi-compact.
2. Each |Aᵢ| ≤ κ by the size definition. Choose finitely many algebra generators of Bᵢ.
Polynomial expressions in them and constants from Aᵢ are finite words in an alphabet of
cardinality at most max(ℵ₀, |Aᵢ|) ≤ κ. By [lem-weil-pbc-finite-list-cardinality], its finite
words have cardinal at most κ. Evaluation of valid expressions is surjective, hence |Bᵢ| ≤ κ.
This includes zero generators and the zero algebra.
3. By [lem-sfb-affine-scheme-size], cardinalSize Uᵢ = max(ℵ₀, |Bᵢ|) ≤ κ.
4. Apply [lem-sfb-open-cover-scheme-size] to the selected finite open cover of X. Its bound
max(ℵ₀, |I|, supᵢ cardinalSize Uᵢ) is at most κ, including when I is empty. No separatedness
or quasi-separatedness is used. -/
theorem cardinalSize_le_of_locallyOfFiniteType {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] [CompactSpace X] : X.cardinalSize ≤ S.cardinalSize := by
  sorry

end AlgebraicGeometry.Scheme
