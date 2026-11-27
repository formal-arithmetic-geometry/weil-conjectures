/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.Noetherian.Basic
import WeilConjectures.RingTheory.FiniteModuleComplete
import Mathlib.RingTheory.LocalRing.RingHom.Basic

/-!
# Quotients of complete Noetherian local rings

Any proper quotient of a Noetherian complete local ring is again a Noetherian complete local
ring.

## Implementation details

Completeness of `R ⧸ I` follows by viewing it as a finite `R`-module, which is complete for
the maximal ideal of `R`, and identifying `m^n (R ⧸ I)` with `(m ⧸ I)^n`.

## References

* [Stacks, Tag 0325], first sentence
-/

@[expose] public section


universe u

/-- Any proper quotient of a Noetherian adically complete local ring is Noetherian,
local, and complete for the quotient of its maximal ideal. -/
theorem quotient_complete_local
    (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    (I : Ideal R) (hI : I ≠ ⊤) :
    letI : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI
    letI : IsLocalRing (R ⧸ I) :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
    IsNoetherianRing (R ⧸ I) ∧
      IsLocalRing (R ⧸ I) ∧
      IsLocalRing.maximalIdeal (R ⧸ I) =
        (IsLocalRing.maximalIdeal R).map (Ideal.Quotient.mk I) ∧
      IsAdicComplete (IsLocalRing.maximalIdeal (R ⧸ I)) (R ⧸ I) := by
  have : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI
  have : IsLocalRing (R ⧸ I) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  have hnoeth : IsNoetherianRing (R ⧸ I) :=
    isNoetherianRing_of_surjective R (R ⧸ I) (Ideal.Quotient.mk I)
      Ideal.Quotient.mk_surjective
  have hmax : IsLocalRing.maximalIdeal (R ⧸ I) =
      (IsLocalRing.maximalIdeal R).map (Ideal.Quotient.mk I) := by
    symm
    exact IsLocalRing.map_maximalIdeal_of_surjective (Ideal.Quotient.mk I)
      Ideal.Quotient.mk_surjective
  have hcomp : IsAdicComplete
      ((IsLocalRing.maximalIdeal R).map (algebraMap R (R ⧸ I))) (R ⧸ I) := by
    rw [IsAdicComplete.map_algebraMap_iff]
    exact finite_module_complete_over_complete_noetherian R
      (IsLocalRing.maximalIdeal R) (R ⧸ I)
  refine ⟨hnoeth, inferInstance, hmax, ?_⟩
  rw [hmax]
  convert hcomp using 1
