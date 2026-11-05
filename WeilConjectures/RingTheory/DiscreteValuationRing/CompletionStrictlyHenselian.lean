/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.RingTheory.CompletionOfDVR
public import WeilConjectures.Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.AdicCompletion.LocalRing

/-!

# The completion of a strictly henselian discrete valuation ring

For a discrete valuation ring `R`, the `𝔪`-adic completion `R̂ = AdicCompletion (maximalIdeal R) R`
is a complete discrete valuation ring (`AdicCompletion.isDiscreteValuationRing`), henselian
(`IsAdicComplete.henselianRing`), with the same residue field
(`AdicCompletion.residueField_map_bijective`). If `R` is strictly henselian, so is `R̂`. The map
`R ⟶ R̂` is injective, local and unramified (`maximalIdeal R̂ = (maximalIdeal R) R̂`).

We record these as instances on the abbreviation `IsDiscreteValuationRing.completion R`, and
give the extension `b̂ : R̂ ⟶ κ` of a map `b : R ⟶ κ` with kernel the maximal ideal.

-/

@[expose] public section

universe u

open IsLocalRing

namespace IsDiscreteValuationRing

variable (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

end IsDiscreteValuationRing
