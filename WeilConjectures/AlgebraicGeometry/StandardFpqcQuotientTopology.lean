/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

import Mathlib.RingTheory.RingHom.Flat

@[expose] public section

universe u v

open CategoryTheory

namespace AlgebraicGeometry

/-- Standard finite affine fpqc covers detect openness.
Source: Stacks Project, Morphisms, Tag 02JY
(blueprint: lem-weil-pbc-standard-fpqc-quotient-topology).

Proof: Package the finite family as the spectrum of the product ring, apply the
quotient-topology theorem for flat quasi-compact surjective morphisms, and use
that the coproduct summands are open and cover the product spectrum. -/
theorem standard_fpqc_quotient_topology
    (R : Type u) [CommRing R]
    (J : Type v) [Finite J]
    (A : J → Type u) [∀ j, CommRing (A j)] [∀ j, Algebra R (A j)]
    [Module.FaithfullyFlat R (∀ j, A j)]
    (W : Set (Spec (CommRingCat.of R)))
    (hW : ∀ j : J,
      IsOpen ((Spec.map (CommRingCat.ofHom (algebraMap R (A j)))) ⁻¹' W)) :
    IsOpen W := by
  let B := ∀ j, A j
  have hq : Topology.IsQuotientMap (PrimeSpectrum.comap (algebraMap R B)) :=
    PrimeSpectrum.isQuotientMap_of_generalizingMap
      PrimeSpectrum.comap_surjective_of_faithfullyFlat
      (RingHom.Flat.generalizingMap_comap
        (RingHom.flat_algebraMap_iff.mpr inferInstance))
  apply hq.isOpen_preimage.mp
  apply (PrimeSpectrum.sigmaToPiHomeo A).isOpen_preimage.mp
  rw [isOpen_sigma_iff]
  intro j
  have hj : IsOpen (PrimeSpectrum.comap (algebraMap R (A j)) ⁻¹' W) := hW j
  convert hj using 1
  ext p
  change PrimeSpectrum.comap (algebraMap R B)
      (PrimeSpectrum.comap (Pi.evalRingHom A j) p) ∈ W ↔
    PrimeSpectrum.comap (algebraMap R (A j)) p ∈ W
  rw [← PrimeSpectrum.comap_comp_apply]
  rfl

end AlgebraicGeometry
