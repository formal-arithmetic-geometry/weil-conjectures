/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.IsStrictHenselization
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import WeilConjectures.RingTheory.AdicCompletionNoetherianOfQuotient
import WeilConjectures.RingTheory.StrictHenselizationCompletionFlat
import WeilConjectures.RingTheory.StrictHenselizationLocalMaximalIdeal
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra

/-!
# Noetherianity and faithful flatness of the completed strict henselization

Let `A` be a Noetherian local ring with maximal ideal `m` and let `C` be a strict
henselization of `A`. We show that the `mC`-adic completion of `C` is Noetherian and that the
completion map from `C` is local and faithfully flat.

## Implementation details

Since `C` is local with finitely generated maximal ideal `mC`, the completion is Noetherian by
the criterion via the Noetherian quotient `C / mC`, and it is local with local completion map.
Flatness and locality give faithful flatness.

## References

* [Stacks, Tag 06LJ], parts (a) and (c)
* [Stacks, Tag 00HR]
-/

@[expose] public section

universe u

namespace Algebra

/-- The completion of the strict henselization of a Noetherian local ring at the extended
maximal ideal is Noetherian, and the canonical completion map is local and faithfully flat. -/
theorem strictHenselization_completion_noetherian_faithfullyFlat
    (A K C : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [Field K]
    [Algebra (IsLocalRing.ResidueField A) K] [IsSepClosure (IsLocalRing.ResidueField A) K]
    [Algebra A K] [IsScalarTower A (IsLocalRing.ResidueField A) K]
    [CommRing C] [Algebra A C] (hC : IsStrictHenselization A K C) :
    IsNoetherianRing
        (AdicCompletion ((IsLocalRing.maximalIdeal A).map (algebraMap A C)) C) ∧
      IsLocalHom (algebraMap C
        (AdicCompletion ((IsLocalRing.maximalIdeal A).map (algebraMap A C)) C)) ∧
      Module.FaithfullyFlat C
        (AdicCompletion ((IsLocalRing.maximalIdeal A).map (algebraMap A C)) C) := by
  obtain ⟨hlocal, hmax⟩ := strictHenselization_local_maximalIdeal A K C hC
  let I := (IsLocalRing.maximalIdeal A).map (algebraMap A C)
  have hI : I.FG := (IsLocalRing.maximalIdeal A).fg_of_isNoetherianRing.map _
  have hm : (IsLocalRing.maximalIdeal C).FG := by
    rw [hmax]
    exact hI
  have hquotient : IsNoetherianRing (C ⧸ I) := by
    change IsNoetherianRing (C ⧸ (IsLocalRing.maximalIdeal A).map (algebraMap A C))
    rw [← hmax]
    change IsNoetherianRing (IsLocalRing.ResidueField C)
    infer_instance
  have hn := (AdicCompletion.isNoetherianRing_and_isAdicComplete_of_quotient I hI).1
  have hl : IsLocalRing (AdicCompletion I C) := by
    change IsLocalRing
      (AdicCompletion ((IsLocalRing.maximalIdeal A).map (algebraMap A C)) C)
    rw [← hmax]
    exact AdicCompletion.isLocalRing_of_fg hm
  have hh : IsLocalHom (algebraMap C (AdicCompletion I C)) := by
    change IsLocalHom (algebraMap C
      (AdicCompletion ((IsLocalRing.maximalIdeal A).map (algebraMap A C)) C))
    rw [← hmax]
    exact AdicCompletion.algebraMap_isLocalHom_of_fg hm
  have hf : Module.Flat C (AdicCompletion I C) :=
    RingHom.flat_algebraMap_iff.mp (strictHenselization_completion_flat A K C hC)
  exact ⟨hn, hh, Module.FaithfullyFlat.of_flat_of_isLocalHom⟩

end Algebra
