/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
import Mathlib.Topology.Constructible

/-!
# Constructible subsets of constructible subspaces

Source: Stacks Project, Topology, Lemma 5.15.12, Tag 09YJ
(blueprint: lem-weil-pbc-constructible-in-retrocompact-open).
-/

universe u

namespace Topology

/-- In a space with a basis of quasi-compact opens, a subset constructible in a constructible
subspace is constructible in the ambient space. Source: Stacks Project, Topology,
Lemma 5.15.12, Tag 09YJ (blueprint: lem-weil-pbc-constructible-in-retrocompact-open).

Proof outline:
1. A retrocompact subspace inherits a basis of quasi-compact opens by intersecting the ambient
basis with it. Constructible sets are retrocompact by Tag 09YH
(`lem-weil-pbc-constructible-is-retrocompact`), so this applies to `E`.
2. Write `E` as a finite union of differences `Uᵢ \ Vᵢ` of retrocompact opens, using
`def-weil-constructible-subset`. Tag 09YI
(`lem-weil-pbc-constructible-intersection-in-constructible`) first in `X`, then in `E`,
shows that `F ∩ (Uᵢ \ Vᵢ)` is constructible in `Uᵢ \ Vᵢ`. Finite unions reduce the claim
to `E = U \ V`.
3. Factor the inclusion through `U`. The subspace `E` is closed in `U` with retrocompact
complement `U ∩ V`. Tag 09YG
(`lem-weil-pbc-constructible-image-closed-retrocompact-complement`) makes `F` constructible
in `U`. Tag 09YD (`lem-weil-pbc-constructible-image-retrocompact-open`) then makes it
constructible in `X`, since `U` is open and retrocompact. -/
theorem isConstructible_of_isConstructible_subspace {X : Type u} [TopologicalSpace X]
    (hBasis : TopologicalSpace.IsTopologicalBasis
      {U : Set X | IsOpen U ∧ IsCompact U})
    {E F : Set X} (hE : IsConstructible E) (hFE : F ⊆ E)
    (hF : IsConstructible ((Subtype.val : E → X) ⁻¹' F)) : IsConstructible F := by
  sorry

end Topology
