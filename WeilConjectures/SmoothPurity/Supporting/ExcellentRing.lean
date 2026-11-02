/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.RingTheory.GRing
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Excellent and quasi-excellent rings

Source: Stacks Project, More on Algebra, Tags 07QT and 07P7; Algebra, Tags 00NI and
00NL (blueprint: def-exc-excellent-ring).

## Main definitions

* `IsQuasiExcellent` is the quasi-excellent predicate.
* `IsExcellent` is the excellent predicate.
* `IsCatenaryRing` and `IsUniversallyCatenary` encode the chain conditions used by
  the excellent predicate.
-/

@[expose] public section

set_option autoImplicit false

universe u

/-- A commutative ring is quasi-excellent when it is Noetherian, a G-ring, and every
finite type algebra has open regular locus. Source: Stacks Project, More on Algebra,
Definition 07QT and Definition 07P7 (blueprint: def-exc-excellent-ring). -/
def IsQuasiExcellent (R : Type u) [CommRing R] : Prop :=
  IsNoetherianRing R ∧ IsGRing R ∧
    ∀ (A : Type u) [CommRing A] [Algebra R A] [Algebra.FiniteType R A],
      IsOpen {p : PrimeSpectrum A | IsRegularLocalRing (Localization.AtPrime p.asIdeal)}
