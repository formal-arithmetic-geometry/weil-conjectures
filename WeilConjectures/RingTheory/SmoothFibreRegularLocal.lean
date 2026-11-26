/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Smooth.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.RingTheory.RegularLocalRing.Defs
import WeilConjectures.RingTheory.RegularLocalRing.Smooth

/-!
# Smooth fibres have regular local rings

## References

* [Stacks, Tag 00T4]
* [Stacks, Tag 00TT]
-/

@[expose] public section

universe u v

namespace Algebra

/-- A smooth algebra has smooth residue-field fibres, whose prime localizations are regular
local rings. -/
theorem smooth_fibre_regular_local
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [Smooth R S] :
    ∀ p : PrimeSpectrum R,
      Smooth p.asIdeal.ResidueField (p.asIdeal.Fiber S) ∧
        ∀ Q : PrimeSpectrum (p.asIdeal.Fiber S),
          IsRegularLocalRing (Localization.AtPrime Q.asIdeal) := by
  intro p
  have hs : Smooth p.asIdeal.ResidueField (p.asIdeal.Fiber S) := inferInstance
  refine ⟨hs, ?_⟩
  intro Q
  exact Smooth.isRegularLocalRing_localization p.asIdeal.ResidueField (p.asIdeal.Fiber S) Q.asIdeal

end Algebra
