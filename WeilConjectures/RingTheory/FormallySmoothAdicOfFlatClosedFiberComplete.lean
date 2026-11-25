/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.FormallySmoothAdic
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.LocalRing.Basic
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.AdicCompletion.Basic
import WeilConjectures.RingTheory.CompleteLocalMapCohenPresentation
import WeilConjectures.RingTheory.FlatClosedFiberPowerSeriesModel
import WeilConjectures.RingTheory.PowerSeriesParameterMapFormallySmoothAdic
import WeilConjectures.RingTheory.FormallySmoothAdicUniverseLift
import Mathlib.Algebra.CharP.Algebra

/-! # The complete case of the flat closed-fibre criterion

A flat local homomorphism of complete Noetherian local rings with formally smooth closed fibre
is formally smooth for the maximal-ideal-adic topology.

## Implementation details

A compatible Cohen power-series presentation `R → S`, `R → A`, `S → B` is chosen, splitting
into residue characteristic zero and prime characteristic (Cohen rings, first parameter `p`).
`RingHom.exists_flat_closedFiber_powerSeries_model` removes the equations of the regular closed
fibre, giving a power-series ring `T` with a surjection `v : T → B` whose kernel is generated
by `ker (R → A)`. The coordinate lifting criterion shows that `R → T` is adically formally
smooth (the filtration, parameter correction and derivation correction of Tag 07NQ), and this
lifting property descends along the two surjections to `A → B`. The chosen model is only used
inside the proof.

## References

* [Stacks, Tag 07NQ], (2) implies (3), after completing both rings
-/

@[expose] public section

universe u v

open IsLocalRing

namespace RingHom

private theorem formallySmoothAdic_descend_surjections
    {R T A B : Type*} [CommRing R] [CommRing T] [CommRing A] [CommRing B]
    [Algebra R T] [Algebra A B]
    (q : R →+* A) (v : T →+* B)
    (hq : Function.Surjective q) (hv : Function.Surjective v)
    (hcomm : v.comp (algebraMap R T) = (algebraMap A B).comp q)
    (hker : RingHom.ker v = (RingHom.ker q).map (algebraMap R T))
    (n : Ideal T) (nB : Ideal B) (hmap : n.map v ≤ nB)
    (hfs : Algebra.FormallySmoothAdic R T n) :
    Algebra.FormallySmoothAdic A B nB := by
  classical
  intro D _ _ J hJ g hg
  let : Algebra R D := ((algebraMap A D).comp q).toAlgebra
  let gT : T →ₐ[R] D ⧸ J :=
    { toRingHom := g.toRingHom.comp v
      commutes' := by
        intro r
        change g (v (algebraMap R T r)) =
          Ideal.Quotient.mk J (algebraMap A D (q r))
        rw [show v (algebraMap R T r) = algebraMap A B (q r) from
          DFunLike.congr_fun hcomm r]
        exact g.commutes (q r) }
  obtain ⟨k, hk, hgk⟩ := hg
  have hgT : ∃ k : ℕ, 1 ≤ k ∧ ∀ x ∈ n ^ k, gT x = 0 := by
    refine ⟨k, hk, ?_⟩
    intro x hx
    apply hgk
    apply pow_le_pow_left' hmap k
    rw [← Ideal.map_pow]
    exact Ideal.mem_map_of_mem v hx
  obtain ⟨l, hl⟩ := Algebra.formallySmoothAdic_lift_universe R T n hfs D J hJ gT hgT
  have hkill : RingHom.ker v ≤ RingHom.ker l.toRingHom := by
    rw [hker, Ideal.map_le_iff_le_comap]
    intro r hr
    change l (algebraMap R T r) = 0
    rw [l.commutes]
    change algebraMap A D (q r) = 0
    rw [show q r = 0 from hr, map_zero]
  let lB : B →+* D := v.liftOfSurjective hv ⟨l.toRingHom, hkill⟩
  have hlB (x : T) : lB (v x) = l x :=
    v.liftOfSurjective_comp_apply hv ⟨l.toRingHom, hkill⟩ x
  let lA : B →ₐ[A] D :=
    { toRingHom := lB
      commutes' := by
        intro a
        obtain ⟨r, rfl⟩ := hq a
        change lB (algebraMap A B (q r)) = algebraMap A D (q r)
        rw [← show v (algebraMap R T r) = algebraMap A B (q r) from
          DFunLike.congr_fun hcomm r, hlB, l.commutes]
        rfl }
  refine ⟨lA, ?_⟩
  ext b
  obtain ⟨x, rfl⟩ := hv b
  change Ideal.Quotient.mk J (lB (v x)) = g (v x)
  rw [hlB]
  exact DFunLike.congr_fun hl x


/-- The flat closed-fibre criterion for rings already complete at their maximal ideals: a flat
local homomorphism of complete Noetherian local rings whose closed fibre is formally smooth for
its maximal-ideal-adic topology is formally smooth for the maximal-ideal-adic topology. -/
theorem formallySmoothAdic_of_flat_closedFiber_complete
    (A : Type u) (B : Type v) [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] [IsNoetherianRing A] [IsNoetherianRing B]
    [IsAdicComplete (maximalIdeal A) A] [IsAdicComplete (maximalIdeal B) B]
    (f : A →+* B) [IsLocalHom f] (hflat : f.Flat) :
    letI : Algebra A B := f.toAlgebra
    let I : Ideal B := Ideal.map f (maximalIdeal A)
    letI : Algebra (A ⧸ maximalIdeal A) (B ⧸ I) :=
      Ideal.Quotient.algebraQuotientOfLEComap (Ideal.le_comap_map :
        maximalIdeal A ≤ I.comap (algebraMap A B))
    Algebra.FormallySmoothAdic (A ⧸ maximalIdeal A) (B ⧸ I)
        (Ideal.map (Ideal.Quotient.mk I) (maximalIdeal B)) →
      Algebra.FormallySmoothAdic A B (maximalIdeal B) := by
  let : Algebra A B := f.toAlgebra
  dsimp only
  intro hfibre
  obtain ⟨ΛR, ΛS, cR, cS, n, m, hR, hS, _, _, hzero, hpos,
    q, b, i, hq, hqlocal, hb, hblocal, hi, hcomm, _, _, t, z, ht, hz, hp⟩ :=
    exists_complete_local_map_cohen_presentation f
  let : CommRing ΛR := cR
  let : CommRing ΛS := cS
  let R := MvPowerSeries (Fin n) ΛR
  let S := MvPowerSeries (Fin m) ΛS
  let : IsRegularLocalRing R := hR
  let : IsRegularLocalRing S := hS
  let : IsLocalHom q := hqlocal
  let : IsLocalHom b := hblocal
  let : IsLocalHom i := hi
  have hcoeff : (IsField ΛR ∧ IsField ΛS ∧ CharZero ΛR ∧ CharZero ΛS) ∨
      ∃ p : ℕ, p.Prime ∧ IsCohenRing p ΛR ∧ IsCohenRing p ΛS ∧
        t.head? = some (p : R) := by
    rcases CharP.exists (ResidueField A) with ⟨p, hchar⟩
    let := hchar
    rcases CharP.char_is_prime_or_zero (ResidueField A) p with hprime | rfl
    · exact Or.inr ⟨p, hprime, (hpos p hprime hchar).1,
        (hpos p hprime hchar).2, hp p hprime hchar⟩
    · let : CharZero (ResidueField A) := CharP.charP_to_charZero (ResidueField A)
      have : CharZero (ResidueField B) :=
        charZero_of_injective_ringHom (ResidueField.map f).injective
      exact Or.inl ⟨(hzero inferInstance).1, (hzero inferInstance).2,
        ((residue A).comp (q.comp MvPowerSeries.C)).charZero,
        ((residue B).comp (b.comp MvPowerSeries.C)).charZero⟩
  obtain ⟨m', hT, v, j, hv, hj, hcomm', hker, y, hy, hfibreT⟩ :=
    exists_flat_closedFiber_powerSeries_model A B f hflat ΛR ΛS n m q b i
      hq hb hcomm t z ht hz hcoeff hfibre
  let T := MvPowerSeries (Fin m') ΛS
  let : IsRegularLocalRing T := hT
  let : IsLocalHom j := hj
  let : Algebra R T := j.toAlgebra
  have hsmooth : Algebra.FormallySmoothAdic R T (maximalIdeal T) :=
    MvPowerSeries.formallySmoothAdic_of_parameters_closedFiber ΛR ΛS n m' j t y
      ht hy hcoeff hfibreT
  apply formallySmoothAdic_descend_surjections q v hq hv hcomm' hker
    (maximalIdeal T) (maximalIdeal B) ?_ hsmooth
  exact (map_maximalIdeal_of_surjective v hv).le

end RingHom
