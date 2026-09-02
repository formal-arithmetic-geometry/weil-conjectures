/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Topology.LocallyClosed

/-!
# Stratifications of topological spaces

Following [Stacks 09XZ], a *stratification* of a topological space `X` is a partition of
`X` into pairwise disjoint locally closed subsets covering `X`. `Topology.Stratification`
additionally requires the partition to be finite, the case relevant for constructible
sheaves.

## Main definitions

- `Topology.Stratification.trivial`: the stratification of `X` with the single stratum `X`.
- `Topology.Stratification.sum`: stratifications of two spaces embedded in `X` with
  complementary images concatenate to a stratification of `X`.

## Implementation notes

The strata are indexed by `Fin n`. Concatenating two stratifications therefore goes through
`finSumFinEquiv`, and each field and each proof of `Topology.Stratification.sum` has to be
written through it; the same will be true of the common refinement of two stratifications,
which is indexed by a product. Indexing the strata by an arbitrary type with a `Finite`
instance instead would make these constructions transport-free (`ι := ι₁ ⊕ ι₂`, resp.
`ι := ι₁ × ι₂`), at the cost of a universe-polymorphic field; this is worth doing before
more stratification constructions are added.
-/

@[expose] public section

namespace Topology

/-- A *stratification* of a topological space `X`, following [Stacks 09XZ]: a finite
partition of `X` into pairwise disjoint locally closed subsets — the *strata* — covering
`X`. Finiteness is not required in loc. cit.; it is included here since finite
stratifications are the ones relevant for constructible sheaves. -/
@[stacks 09XZ]
structure Stratification (X : Type*) [TopologicalSpace X] where
  /-- The number of strata. -/
  n : ℕ
  /-- The strata. -/
  stratum : Fin n → Set X
  isLocallyClosed_stratum : ∀ i, IsLocallyClosed (stratum i)
  iUnion_stratum_eq_univ : ⋃ i, stratum i = Set.univ
  pairwise_disjoint_stratum : Pairwise (Function.onFun Disjoint stratum)

namespace Stratification

/-- The trivial stratification of `X`, with the single stratum `X`. -/
@[simps n stratum]
def trivial (X : Type*) [TopologicalSpace X] : Stratification X where
  n := 1
  stratum _ := Set.univ
  isLocallyClosed_stratum _ := isOpen_univ.isLocallyClosed
  iUnion_stratum_eq_univ := Set.iUnion_const _
  pairwise_disjoint_stratum k k' hkk' := (hkk' (Subsingleton.elim k k')).elim

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-- Stratifications of two spaces `Y`, `Z` embedded in `X` with locally closed and
complementary images concatenate to a stratification of `X`: the strata are the images of
the strata of `Y` and of `Z`.

```
        f                 g
   Y ────────→ X ←──────── Z        range g = (range f)ᶜ
```

The scheme-theoretic incarnation, for a complementary pair of immersions, is
`AlgebraicGeometry.Scheme.Stratification.openClosed`. -/
@[simps n stratum]
def sum {f : Y → X} {g : Z → X} (hf : IsEmbedding f) (hg : IsEmbedding g)
    (hf' : IsLocallyClosed (Set.range f)) (hg' : IsLocallyClosed (Set.range g))
    (hfg : Set.range g = (Set.range f)ᶜ) (SY : Stratification Y) (SZ : Stratification Z) :
    Stratification X where
  n := SY.n + SZ.n
  stratum k := Sum.elim (fun l ↦ f '' SY.stratum l) (fun l ↦ g '' SZ.stratum l)
    (finSumFinEquiv.symm k)
  isLocallyClosed_stratum k := by
    obtain l | l := finSumFinEquiv.symm k
    · exact (SY.isLocallyClosed_stratum l).image hf.isInducing hf'
    · exact (SZ.isLocallyClosed_stratum l).image hg.isInducing hg'
  iUnion_stratum_eq_univ := Set.eq_univ_of_forall fun x ↦ by
    by_cases hx : x ∈ Set.range f
    · obtain ⟨y, rfl⟩ := hx
      obtain ⟨l, hl⟩ := Set.mem_iUnion.mp (SY.iUnion_stratum_eq_univ ▸ Set.mem_univ y)
      exact Set.mem_iUnion.mpr ⟨finSumFinEquiv (Sum.inl l), by simpa using ⟨y, hl, rfl⟩⟩
    · rw [← Set.mem_compl_iff, ← hfg] at hx
      obtain ⟨z, rfl⟩ := hx
      obtain ⟨l, hl⟩ := Set.mem_iUnion.mp (SZ.iUnion_stratum_eq_univ ▸ Set.mem_univ z)
      exact Set.mem_iUnion.mpr ⟨finSumFinEquiv (Sum.inr l), by simpa using ⟨z, hl, rfl⟩⟩
  pairwise_disjoint_stratum k k' hkk' := by
    have hne : finSumFinEquiv.symm k ≠ finSumFinEquiv.symm k' :=
      fun h ↦ hkk' (finSumFinEquiv.symm.injective h)
    have hgf : Disjoint (Set.range f) (Set.range g) := by
      rw [hfg]
      exact disjoint_compl_right
    change Disjoint (Sum.elim _ _ (finSumFinEquiv.symm k)) (Sum.elim _ _ (finSumFinEquiv.symm k'))
    generalize finSumFinEquiv.symm k = s at hne ⊢
    generalize finSumFinEquiv.symm k' = s' at hne ⊢
    rcases s with l | l <;> rcases s' with l' | l' <;> simp only [Sum.elim_inl, Sum.elim_inr]
    · exact (Set.disjoint_image_iff hf.injective).mpr
        (SY.pairwise_disjoint_stratum (fun h ↦ hne (by rw [h])))
    · exact hgf.mono (Set.image_subset_range _ _) (Set.image_subset_range _ _)
    · exact hgf.symm.mono (Set.image_subset_range _ _) (Set.image_subset_range _ _)
    · exact (Set.disjoint_image_iff hg.injective).mpr
        (SZ.pairwise_disjoint_stratum (fun h ↦ hne (by rw [h])))

end Stratification

end Topology
