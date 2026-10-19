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
import WeilConjectures.Mathlib.Topology.KrullDimension
import Sheaf.AlgebraicGeometry.NowhereDenseDimensionDrop

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
  -- Reuse the proved general dimension-drop theorem for the component argument above.
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : IsNoetherian X := ⟨⟩
  have hi := i.isClosedEmbedding
  have hrange := hi.isEmbedding.topologicalKrullDim_eq_range
  have hdim : topologicalKrullDim Z ≤ 0 := by
    by_cases hzero : topologicalKrullDim X ≤ 0
    · exact hi.isInducing.topologicalKrullDim_le.trans hzero
    · have hpos : 0 < topologicalKrullDim X := lt_of_not_ge hzero
      obtain ⟨A, B, hAB⟩ := Order.krullDim_pos_iff.mp hpos
      obtain ⟨x, _⟩ := A.isIrreducible.nonempty
      have : Nonempty X := ⟨x⟩
      have hone : topologicalKrullDim X = 1 := by
        apply le_antisymm
        · simpa only [Scheme.dim_eq_topologicalKrullDim] using hX
        · simpa using (ENat.WithBot.add_one_le_iff (n := 0)).mpr hpos
      have hdrop := X.topologicalKrullDim_lt_of_isNowhereDense 1 hone
        (Set.range i.base) hi.isClosed_range hnow
      rw [← hrange] at hdrop
      exact ENat.WithBot.lt_add_one_iff.mp (by simpa using hdrop)
  refine ⟨by rwa [Scheme.dim_eq_topologicalKrullDim], fun z ↦ ?_⟩
  have hpoint :=
    (hi.isClosed_range.finite_and_isClosed_singleton_of_topologicalKrullDim_le_zero
      (by rwa [← hrange])).2 (i z) ⟨z, rfl⟩
  apply hi.isClosed_iff_image_isClosed.mpr
  simpa only [Set.image_singleton] using hpoint

end AlgebraicGeometry
