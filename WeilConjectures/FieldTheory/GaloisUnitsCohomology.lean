/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.FieldTheory.KrullTopology
public import Mathlib.RepresentationTheory.Homological.ContCohomology.Basic
public import Mathlib.RepresentationTheory.Rep.Basic

/-!
# Continuous Galois cohomology of separable-closure units

We define the units of a separable closure as a discrete topological representation of the
absolute Galois group with its Krull topology (`Field.galoisUnitsTopRep`), and its second
continuous cohomology group (`Field.GaloisUnitsH2`).

## Implementation details

`Field.GaloisUnitsH2` uses Mathlib's homogeneous continuous cochains; it is not the abstract group
cohomology of the underlying group.

## References

* [Stacks Project, Tag 04JP](https://stacks.math.columbia.edu/tag/04JP)
* [Stacks Project, Tag 04JR](https://stacks.math.columbia.edu/tag/04JR)
* [Stacks Project, Tag 0DVG](https://stacks.math.columbia.edu/tag/0DVG)
* [Stacks Project, Tag 03QQ](https://stacks.math.columbia.edu/tag/03QQ)
* [Stacks Project, Example 03QV](https://stacks.math.columbia.edu/tag/03QV)
-/

@[expose] public section

universe u

namespace Field

variable (K : Type u) [Field K]

local instance : TopologicalSpace ((Rep.ofAlgebraAutOnUnits K (SeparableClosure K))) := ⊥
local instance : DiscreteTopology ((Rep.ofAlgebraAutOnUnits K (SeparableClosure K))) := ⟨rfl⟩

/-- The natural action of the Galois group `Gal(K^sep/K)` on the discrete units of a separable
closure, written additively, as a topological representation over `ℤ`. -/
noncomputable def galoisUnitsTopRep : TopRep ℤ (SeparableClosure K ≃ₐ[K] SeparableClosure K) :=
  TopRep.of
    ⟨{ toFun := fun g ↦
          { toLinearMap := (Rep.ofAlgebraAutOnUnits K (SeparableClosure K)).ρ g
            cont := continuous_of_discreteTopology }
       map_one' := by
         ext x
         exact congrArg (fun f ↦ f x)
           (Rep.ofAlgebraAutOnUnits K (SeparableClosure K)).ρ.map_one
       map_mul' := by
         intro g h
         ext x
         exact congrArg (fun f ↦ f x)
           ((Rep.ofAlgebraAutOnUnits K (SeparableClosure K)).ρ.map_mul g h) }⟩

/-- The second continuous Galois cohomology `H²(Gal(K^sep/K), (K^sep)ˣ)` of the discrete units of
a separable closure, for the Krull topology on the Galois group. -/
noncomputable abbrev GaloisUnitsH2 : Type u := continuousCohomology 2 (galoisUnitsTopRep K)

end Field
