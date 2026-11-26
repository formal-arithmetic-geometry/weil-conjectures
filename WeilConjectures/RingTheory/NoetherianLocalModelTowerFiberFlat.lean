/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.NoetherianLocalModelTower
public import Mathlib.RingTheory.Flat.Basic
import WeilConjectures.RingTheory.NoetherianLocalModelTowerFiberFlatStage
import WeilConjectures.RingTheory.NoetherianLocalModelTowerFiberFlatPersistence

/-!
# Closed-fibre flatness eventually holds in a Noetherian local model tower

If the closed-fibre module of the limit is flat, then the stage closed-fibre modules are flat
from some index on.

## Implementation details

The closed-fibre quotients form a Noetherian local system whose colimit is the closed fibre;
`RingTheory.exists_flat_stage` gives one fibre-flat stage, and flatness persists at later stages
by base change and localization. No base-flatness hypothesis is needed.

## References

* [Stacks, Tag 00R7] (second paragraph of the proof)
* [Stacks, Tag 00R6]
-/

@[expose] public section

universe u v w t

open scoped TensorProduct

namespace Module

set_option linter.style.haveILetI false in
/-- Flatness of the limit closed fibre descends to a tail of the model tower. -/
theorem NoetherianLocalModelTower.eventually_fiberFlat
    {R : Type u} {S : Type v} {S' : Type w} {M : Type t}
    [CommRing R] [CommRing S] [CommRing S'] [IsLocalRing R] [AddCommGroup M]
    [Algebra R S] [Algebra S S'] [Module S' M] [Module S M]
    [IsScalarTower S S' M]
    (X : NoetherianLocalModelTower R S S' M)
    (h_fibre : Module.Flat
      (S ⧸ Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R))
      ((S ⧸ Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R)) ⊗[S] M)) :
    letI := X.preorder
    letI := X.commR
    letI := X.commS
    letI := X.localR
    letI := X.algRS
    letI := X.addN
    letI := X.moduleS
    ∃ i : X.ι, ∀ j : X.ι, i ≤ j → Module.Flat
      (X.S₀ j ⧸ Ideal.map (algebraMap (X.R₀ j) (X.S₀ j))
        (IsLocalRing.maximalIdeal (X.R₀ j)))
      ((X.S₀ j ⧸ Ideal.map (algebraMap (X.R₀ j) (X.S₀ j))
        (IsLocalRing.maximalIdeal (X.R₀ j))) ⊗[X.S₀ j] X.N₀ j) := by
  letI := X.preorder
  letI := X.commR
  letI := X.commS
  letI := X.localR
  letI := X.algRS
  letI := X.addN
  letI := X.moduleS
  obtain ⟨i, hi⟩ := X.exists_fiberFlat_stage h_fibre
  refine ⟨i, fun j hij ↦ X.fiberFlat_of_le i j hij hi⟩

end Module
