/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.IsStrictHenselization
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import WeilConjectures.RingTheory.FlatModuleCompletion
import WeilConjectures.RingTheory.StrictHenselizationModPowerFree

/-!
# Flatness over the base of the completed strict henselization

Let `A` be a Noetherian local ring with maximal ideal `n` and let `C` be a strict
henselization of `A`. We show that the `nC`-adic completion of `C` is flat over `A`.

## Implementation details

The completion is identified with the `n`-adic completion of a free `A`-module `F`, using
compatible isomorphisms modulo `n^r`. Since `F` is flat, its completion is flat over the
completion of `A`, which is flat over `A`.

## References

* [Stacks, Tag 06LJ], proof of (c)
-/

@[expose] public section

universe v

namespace Algebra

/-- For a Noetherian local ring `A`, the completion of its strict henselization `C` at
`nC`, where `n` is the maximal ideal of `A`, is flat over `A`. -/
theorem strictHenselization_completion_flat_over_base
    (A K C : Type v) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [Field K]
    [Algebra (IsLocalRing.ResidueField A) K] [IsSepClosure (IsLocalRing.ResidueField A) K]
    [Algebra A K] [IsScalarTower A (IsLocalRing.ResidueField A) K]
    [CommRing C] [Algebra A C] (hC : IsStrictHenselization A K C) :
    (algebraMap A
      (AdicCompletion ((IsLocalRing.maximalIdeal A).map (algebraMap A C)) C)).Flat := by
  obtain ⟨X, _, _, _, E, _⟩ := strictHenselization_mod_power_free A K C hC
  let I := IsLocalRing.maximalIdeal A
  have : Module.Flat (AdicCompletion I A) (AdicCompletion I (X →₀ A)) :=
    Module.flat_adicCompletion A I (X →₀ A)
  have : Module.Flat A (AdicCompletion I (X →₀ A)) :=
    Module.Flat.trans A (AdicCompletion I A) (AdicCompletion I (X →₀ A))
  exact RingHom.flat_algebraMap_iff.mpr (Module.Flat.of_linearEquiv E.symm)

end Algebra
