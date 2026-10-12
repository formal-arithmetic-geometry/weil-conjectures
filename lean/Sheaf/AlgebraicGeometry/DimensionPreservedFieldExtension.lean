/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Topology.KrullDimension
import Sheaf.AlgebraicGeometry.DimensionAtPointFieldExtension
import Sheaf.Topology.DimensionSupremumLocalDimensions

/-!
# Dimension of an affine spectrum under field extension

Source: Stacks Project, Algebra, Lemma 10.116.5 (Tag 00P3)
(blueprint: lem-weil-pbc-dimension-preserved-field-extension).
-/

@[expose] public section

universe u v w

open scoped TensorProduct

namespace AlgebraicGeometry

/-- Scalar extension preserves the topological Krull dimension of an affine spectrum.
Source: Stacks Project, Algebra, Lemma 10.116.5 (Tag 00P3)
(blueprint: lem-weil-pbc-dimension-preserved-field-extension).

Proof (the node's split, using Tags 00P4 and 0B7I):
1. By `lem-weil-pbc-field-extension-base-change-faithfully-flat`, the map from `S`
   to `S ⊗[k] K` is faithfully flat. Transport along tensor-factor symmetry to obtain
   the faithfully flat map from `S` to `K ⊗[k] S`, sending `s` to `1 ⊗ s`.
2. By `lem-weil-pbc-faithfully-flat-surjective-spectrum`, contraction along this map
   is surjective on prime spectra: every prime of `S` has a prime above it.
3. For each prime of `K ⊗[k] S`, apply
   `lem-weil-pbc-dimension-at-point-field-extension` (00P4). The same tensor symmetry
   identifies its spectrum with that of `S ⊗[k] K`, preserving local dimensions and
   contraction. Thus its local dimension equals that at the contracted prime of `S`.
4. By `lem-weil-pbc-dimension-supremum-local-dimensions` (0B7I), each global dimension
   is the supremum of its local dimensions. Surjectivity from step 2 and equality
   from step 3 identify these suprema. The empty spectrum has supremum `⊥`, so the
   zero algebra is included as well.
-/
theorem topologicalKrullDim_spec_tensorProduct_of_field_extension
    (k : Type u) (K : Type v) (S : Type w) [Field k] [Field K] [CommRing S]
    [Algebra k K] [Algebra k S] [Algebra.FiniteType k S] :
    topologicalKrullDim (Spec (CommRingCat.of (K ⊗[k] S))) =
      topologicalKrullDim (Spec (CommRingCat.of S)) := by
  sorry

end AlgebraicGeometry
