/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.Jacobson.Radical
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic

/-!
# Integral algebras over local rings

Two consequences of the fact that a maximal ideal of an integral algebra `S` over a local
ring `R` contracts to the maximal ideal of `R`:

* `IsLocalRing.map_maximalIdeal_le_jacobson`: `m_R S` is contained in the Jacobson radical
  of `S`;
* `IsLocalRing.isLocalHom_algebraMap_of_isIntegral`: if `S` is local, then `R → S` is a local
  homomorphism.
-/

@[expose] public section

open IsLocalRing

/-- If `S` is integral over a local ring `R`, the extension of the maximal ideal of `R` is
contained in the Jacobson radical of `S`. -/
theorem IsLocalRing.map_maximalIdeal_le_jacobson (R S : Type*) [CommRing R] [CommRing S]
    [IsLocalRing R] [Algebra R S] [Algebra.IsIntegral R S] :
    (maximalIdeal R).map (algebraMap R S) ≤ Ring.jacobson S := by
  rw [← Ideal.jacobson_bot]
  intro x hx
  rw [Ideal.jacobson, Ideal.mem_sInf]
  rintro M ⟨-, hM⟩
  have h : M.comap (algebraMap R S) = maximalIdeal R :=
    IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal M)
  exact Ideal.map_le_iff_le_comap.mpr h.ge hx

/-- A local homomorphism: if `S` is an integral algebra over a local ring `R` and `S` is local,
then `R → S` is a local homomorphism. -/
theorem IsLocalRing.isLocalHom_algebraMap_of_isIntegral (R S : Type*) [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] [Algebra R S] [Algebra.IsIntegral R S] :
    IsLocalHom (algebraMap R S) := by
  refine ⟨fun a h ↦ ?_⟩
  by_contra hcon
  have ha : a ∈ maximalIdeal R := (IsLocalRing.mem_maximalIdeal a).mpr hcon
  have hcomap : (maximalIdeal S).comap (algebraMap R S) = maximalIdeal R :=
    IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal _)
  rw [← hcomap, Ideal.mem_comap] at ha
  exact (IsLocalRing.mem_maximalIdeal _).mp ha h
