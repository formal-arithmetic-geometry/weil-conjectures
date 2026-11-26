/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.AdicCompletion.Basic
public import WeilConjectures.RingTheory.IsRegularSystemOfParameters
import WeilConjectures.RingTheory.CompleteLocalMapCohenPresentation

/-!
# Compatible regular presentations of a map of complete local rings

Every local map of complete Noetherian local rings has compatible presentations by complete
regular local rings, linked by a flat map with regular closed fibre.

## Implementation details

The result is obtained from `RingHom.exists_complete_local_map_cohen_presentation`, which
presents both rings by power-series rings over fields or Cohen rings. The residue-field
isomorphism is induced by the surjection `R → A`.

## References

* [Stacks, Tag 07NN]
-/

@[expose] public section

universe u v

namespace RingHom

/-- Every local map `f : A → B` of complete Noetherian local rings has compatible regular
presentations: surjections `q : R → A` and `v : S → B` from complete regular local rings and a
flat local map `u : R → S` with `v ∘ u = f ∘ q`, such that `q` induces an isomorphism of
residue fields, a regular system of parameters of `R` maps into one of `S`, and the closed
fibre `S ⧸ m_R S` is regular local. -/
theorem exists_complete_local_map_regular_presentation
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] [IsNoetherianRing A] [IsNoetherianRing B]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [IsAdicComplete (IsLocalRing.maximalIdeal B) B]
    (f : A →+* B) [IsLocalHom f] :
    ∃ (R S : Type (max u v)) (_ : CommRing R) (_ : CommRing S)
      (_ : IsRegularLocalRing R) (_ : IsRegularLocalRing S),
      IsAdicComplete (IsLocalRing.maximalIdeal R) R ∧
      IsAdicComplete (IsLocalRing.maximalIdeal S) S ∧
      ∃ (q : R →+* A) (v : S →+* B) (u : R →+* S),
        Function.Surjective q ∧ IsLocalHom q ∧
        Function.Surjective v ∧ IsLocalHom v ∧ IsLocalHom u ∧
        v.comp u = f.comp q ∧
        (∃ e : (R ⧸ IsLocalRing.maximalIdeal R) ≃+* (A ⧸ IsLocalRing.maximalIdeal A),
          ∀ r : R,
            e (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R) r) =
              Ideal.Quotient.mk (IsLocalRing.maximalIdeal A) (q r)) ∧
        (∃ (t : List R) (z : List S),
          IsLocalRing.IsRegularSystemOfParameters t ∧
          IsLocalRing.IsRegularSystemOfParameters (t.map u ++ z)) ∧
        u.Flat ∧ IsRegularLocalRing (S ⧸ (IsLocalRing.maximalIdeal R).map u) := by
  obtain ⟨ΛA, ΛB, cA, cB, n, m, hR, hS, hcR, hcS, hchar, hcohen,
    hdata⟩ := exists_complete_local_map_cohen_presentation f
  obtain ⟨q, v, u, hq, hq_local, hv, hv_local, hu_local, hcomm,
    hflat, hfiber, hparams⟩ := hdata
  obtain ⟨t, z, ht, hz, hp⟩ := hparams
  let R := MvPowerSeries (Fin n) ΛA
  let S := MvPowerSeries (Fin m) ΛB
  let : CommRing ΛA := cA
  let : CommRing ΛB := cB
  let : CommRing R := inferInstance
  let : CommRing S := inferInstance
  let : IsRegularLocalRing R := hR
  let : IsRegularLocalRing S := hS
  let : IsLocalHom q := hq_local
  let qres := IsLocalRing.ResidueField.map q
  have hsurj : Function.Surjective qres := by
    intro a
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective a
    obtain ⟨r, rfl⟩ := hq a
    exact ⟨IsLocalRing.residue R r, rfl⟩
  have hres : ∃ e : (R ⧸ IsLocalRing.maximalIdeal R) ≃+*
      (A ⧸ IsLocalRing.maximalIdeal A),
      ∀ r : R, e (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R) r) =
        Ideal.Quotient.mk (IsLocalRing.maximalIdeal A) (q r) := by
    exact ⟨RingEquiv.ofBijective qres ⟨qres.injective, hsurj⟩, fun _ ↦ rfl⟩
  exact ⟨R, S, inferInstance, inferInstance, hR, hS, hcR, hcS,
    q, v, u, hq, hq_local, hv, hv_local, hu_local, hcomm, hres,
    ⟨t, z, ht, hz⟩, hflat, hfiber⟩

end RingHom
