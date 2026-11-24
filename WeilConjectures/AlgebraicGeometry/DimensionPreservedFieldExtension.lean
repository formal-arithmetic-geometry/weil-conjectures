/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Topology.KrullDimension
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import WeilConjectures.AlgebraicGeometry.DimensionAtPointFieldExtension
import WeilConjectures.Topology.DimensionSupremumLocalDimensions

/-!
# Dimension of an affine spectrum under field extension

## References

* Stacks Project, Tag 00P3
-/

@[expose] public section

universe u v w

open scoped TensorProduct

namespace AlgebraicGeometry

/-- Scalar extension preserves the topological Krull dimension of an affine spectrum.
(Stacks, Tag 00P3) -/
theorem topologicalKrullDim_spec_tensorProduct_of_field_extension
    (k : Type u) (K : Type v) (S : Type w) [Field k] [Field K] [CommRing S]
    [Algebra k K] [Algebra k S] [Algebra.FiniteType k S] :
    topologicalKrullDim (Spec (CommRingCat.of (K ⊗[k] S))) =
      topologicalKrullDim (Spec (CommRingCat.of S)) := by
  let e := PrimeSpectrum.homeomorphOfRingEquiv
    (Algebra.TensorProduct.comm k K S).toRingEquiv
  change topologicalKrullDim (PrimeSpectrum (K ⊗[k] S)) =
    topologicalKrullDim (PrimeSpectrum S)
  rw [IsHomeomorph.topologicalKrullDim_eq e e.isHomeomorph]
  rw [topologicalKrullDim_eq_iSup_topologicalKrullDimAt,
    topologicalKrullDim_eq_iSup_topologicalKrullDimAt]
  have hsurj : Function.Surjective
      (PrimeSpectrum.comap
        (Algebra.TensorProduct.includeLeftRingHom (R := k) (A := S) (B := K))) :=
    PrimeSpectrum.comap_surjective_of_faithfullyFlat
  calc
    (⨆ q : PrimeSpectrum (S ⊗[k] K), topologicalKrullDimAt q) =
        ⨆ q : PrimeSpectrum (S ⊗[k] K), topologicalKrullDimAt
          (PrimeSpectrum.comap
            (Algebra.TensorProduct.includeLeftRingHom (R := k) (A := S) (B := K)) q) :=
      iSup_congr fun q ↦ (topologicalKrullDimAt_spec_tensorProduct_field_extension q).symm
    _ = ⨆ q : PrimeSpectrum S, topologicalKrullDimAt q :=
      hsurj.iSup_comp topologicalKrullDimAt

end AlgebraicGeometry
