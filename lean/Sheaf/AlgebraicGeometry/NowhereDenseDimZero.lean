/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.Topology.GDelta.Basic
public import Sheaf.AlgebraicGeometry.Dimension

/-!
# Nowhere-dense closed subschemes in dimension at most one

Source: Stacks Project, Varieties, Tag 0AYY (blueprint: lem-pc-nowhere-dense-dim-zero).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A nowhere-dense closed subscheme of a finite-type scheme of dimension at most one has
dimension at most zero, and all of its points are closed in the subscheme (Stacks Project,
Varieties, Tag 0AYY; blueprint: lem-pc-nowhere-dense-dim-zero).

Proof: If `X` is empty, then the closed subscheme `Z` is empty. Otherwise finite type over the
field makes `X` Noetherian (`lem-weil-pbc-finite-type-over-noetherian`), with finitely many
irreducible components (`lem-weil-pbc-noetherian-finitely-many-components`) covering `X`
(`lem-sc-irreducible-components-cover`). Each component has a nonempty open subset obtained
by removing the other components: irreducibility and maximality prevent containment in their
finite union. By `lem-pc-scheme-dimension-local-rings`, the topological Krull dimension
(`def-kun-topological-krull-dimension`) of `X` is at most one. A strict chain of two nonempty
irreducible closed subsets in `Z` is also such a chain in `X`. Its larger member lies in a
component (`lem-sc-irreducible-components-cover`). If strictly smaller than that component,
the chain extends to length two, contradicting the dimension bound. Otherwise `Z` contains
the component and hence its nonempty open subset, contradicting nowhere density. Thus the
topological dimension of `Z` is at most zero, and `lem-pc-scheme-dimension-local-rings` gives
`Z.dim ≤ 0` in the sense of `def-pc-dimension`. Finally `lem-sc-dim0-finite` (Stacks, Tag 06LH)
applied to this closed subscheme of a finite-type scheme gives closedness of every point in
`Z`, including the empty case.
(blueprint: lem-pc-nowhere-dense-dim-zero)
-/
theorem dim_le_zero_of_isNowhereDense {k : Type u} [Field k] {X Z : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] [QuasiCompact f]
    (i : Z ⟶ X) [IsClosedImmersion i] (hX : X.dim ≤ 1)
    (hnow : IsNowhereDense (Set.range i.base)) : Z.dim ≤ 0 ∧
      ∀ z : Z, IsClosed ({z} : Set Z) := by
  sorry

end AlgebraicGeometry
