/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.IsStrictHenselization
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.RegularLocalRing.Defs
import WeilConjectures.RingTheory.StrictHenselizationCotangentDimension
import WeilConjectures.RingTheory.StrictHenselizationDimension
import WeilConjectures.RingTheory.StrictHenselizationNoetherian

/-!
# Regularity and strict henselization

A Noetherian local ring is regular if and only if its strict henselization is regular.

## Implementation details

The strict henselization is Noetherian, has the same Krull dimension, and its cotangent space
has the same dimension over its residue field; regularity is the equality of these two
dimensions.

## References

* [Stacks, Tag 06LN], equivalence of conditions (1) and (3)
-/

@[expose] public section

universe v

namespace Algebra

/-- A Noetherian local ring is regular exactly when its strict henselization is regular.
Here `C` is the strict henselization of `R` with respect to the separable closure `K` of
the residue field of `R`. -/
theorem isRegularLocalRing_iff_strictHenselization
    (R K C : Type v) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [Field K]
    [Algebra (IsLocalRing.ResidueField R) K] [IsSepClosure (IsLocalRing.ResidueField R) K]
    [Algebra R K] [IsScalarTower R (IsLocalRing.ResidueField R) K]
    [CommRing C] [Algebra R C] (hC : IsStrictHenselization R K C) :
    IsRegularLocalRing R ↔ IsRegularLocalRing C := by
  have : IsNoetherianRing C :=
    (isNoetherianRing_iff_isStrictHenselization R K C hC).mp inferInstance
  obtain ⟨hlocal, _, hcotangent⟩ :=
    finrank_cotangentSpace_eq_of_isStrictHenselization R K C hC
  have : IsLocalRing C := hlocal
  rw [IsRegularLocalRing.iff_finrank_cotangentSpace R,
    IsRegularLocalRing.iff_finrank_cotangentSpace C, hcotangent,
    ringKrullDim_eq_of_isStrictHenselization R K C hC]

end Algebra
