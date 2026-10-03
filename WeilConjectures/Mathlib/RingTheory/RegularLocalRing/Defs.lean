/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.DiscreteValuationRing.TFAE

/-!
# Regular local rings are domains

## Main results

- `IsRegularLocalRing.isDomain`: a regular local ring is an integral domain.
- `IsRegularLocalRing.of_isIntegrallyClosed`: an integrally closed noetherian local domain of
  dimension at most one is regular.
- `IsRegularLocalRing.isIntegrallyClosed`: a regular local ring of dimension at most one is
  integrally closed.

## Blueprint

- `sk-i-geometry`: regular local rings are domains.
-/

@[expose] public section

/-- A regular local ring is an integral domain. (blueprint: `sk-i-geometry`) -/
instance IsRegularLocalRing.isDomain (R : Type*) [CommRing R] [IsRegularLocalRing R] :
    IsDomain R := by
  sorry

/-- An integrally closed noetherian local domain of Krull dimension at most one is a regular
local ring: it is a field or, by Stacks `00PD`, a discrete valuation ring.
(blueprint: `lem-sc-normal-dim1-dvr`) -/
theorem IsRegularLocalRing.of_isIntegrallyClosed (R : Type*) [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] [IsDomain R] [IsIntegrallyClosed R] (h : ringKrullDim R ≤ 1) :
    IsRegularLocalRing R := by
  have : Ring.KrullDimLE 1 R := Ring.krullDimLE_iff.mpr (by exact_mod_cast h)
  have : Ring.DimensionLEOne R :=
    ⟨fun {p} hp hp' ↦ Ring.krullDimLE_one_iff_of_noZeroDivisors.mp this p hp hp'⟩
  have : IsDedekindDomain R := { }
  exact .of_isRegularRing_of_isLocalRing R

/-- A regular local ring of Krull dimension at most one is integrally closed: it is a field or
a discrete valuation ring. -/
theorem IsRegularLocalRing.isIntegrallyClosed (R : Type*) [CommRing R] [IsRegularLocalRing R]
    (h : ringKrullDim R ≤ 1) : IsIntegrallyClosed R := by
  by_cases hR : IsField R
  · let := hR.toField
    infer_instance
  have hdim : ringKrullDim R = 1 := by
    refine le_antisymm h (not_lt.mp fun h' ↦ hR ?_)
    have : Ring.KrullDimLE 0 R :=
      Ring.krullDimLE_iff.mpr (ENat.WithBot.lt_add_one_iff.mp (by simpa using h'))
    exact Ring.KrullDimLE.isField_of_isDomain
  have hfin : Module.finrank (IsLocalRing.ResidueField R) (IsLocalRing.CotangentSpace R) = 1 := by
    have := (IsRegularLocalRing.iff_finrank_cotangentSpace R).mp inferInstance
    rw [hdim] at this
    exact_mod_cast this
  have : IsDiscreteValuationRing R := ((IsDiscreteValuationRing.TFAE R hR).out 0 5).mpr hfin
  infer_instance
