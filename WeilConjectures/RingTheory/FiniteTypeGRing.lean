/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.GRing
public import Mathlib.RingTheory.FiniteType
import WeilConjectures.RingTheory.FiniteTypeGRingAux

/-!
# Finite type algebras over G-rings

A finite type algebra over a G-ring is a G-ring.

## References

* Stacks Project, More on Algebra, Proposition 07PV.
-/

@[expose] public section

universe u v

/-- A finite type algebra over a G-ring is a G-ring. -/
theorem isGRing_of_finiteType {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    [Algebra R S] (hR : IsGRing R) [Algebra.FiniteType R S] : IsGRing S := by
  let _ : IsNoetherianRing R := hR.1
  let _ : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing R S
  refine ⟨inferInstance, ?_⟩
  exact finiteType_completion_regular hR
