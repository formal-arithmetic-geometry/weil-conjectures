/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G3
-/
module

public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.Algebra.Regular.SMul
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.KrullDimension.Regular

/-!
# Regularity of a root algebra along its root divisor

Source: Stacks Project, Tags 0EYH and 0EYG, the local verification along the divisor.
(blueprint: lem-sbc-root-algebra-regular-at-root)
-/

@[expose] public section

universe u
open Polynomial IsLocalRing

namespace AdjoinRoot
noncomputable section

private theorem lift_regular
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (x : R) (hx : x ∈ maximalIdeal R) (hreg : IsSMulRegular R x)
    [IsRegularLocalRing (R ⧸ Ideal.span {x})] : IsRegularLocalRing R := by
  classical
  let I := Ideal.span ({x} : Set R)
  let Q := R ⧸ I
  let φ := Ideal.Quotient.mk I
  let m := maximalIdeal R
  let mq := maximalIdeal Q
  obtain ⟨s, hcard, hs⟩ := (IsNoetherian.noetherian mq).exists_span_finset_card_eq_spanFinrank
  let a : Q → R := Function.surjInv Ideal.Quotient.mk_surjective
  have ha (y : Q) : φ (a y) = y := Function.surjInv_eq _ y
  let t : Set R := insert x (a '' (s : Set Q))
  have hfin : t.Finite := (s.finite_toSet.image a).insert x
  have ht : Ideal.span t = m := by
    have hmap : (Ideal.span t).map φ = mq := by
      rw [Ideal.map_span, Set.image_insert_eq]
      have hx0 : φ x = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self x)
      rw [hx0, Set.image_image]
      simp only [ha, Set.image_id']
      rw [Ideal.span_insert_zero]
      exact hs
    have hI : I ≤ Ideal.span t := Ideal.span_mono (by
      intro y hy
      have hyx : y = x := Set.mem_singleton_iff.mp hy
      subst y
      exact Set.mem_insert _ _)
    have hc : (Ideal.span t).comap (RingHom.id R) = m := by
      rw [Ideal.comap_id]
      have hh := congrArg (Ideal.comap φ) hmap
      rw [Ideal.comap_map_of_surjective φ Ideal.Quotient.mk_surjective,
        ← RingHom.ker_eq_comap_bot, Ideal.mk_ker, sup_eq_left.mpr hI] at hh
      have hm : mq.comap φ = m := by
        rw [show mq = m.map φ from (map_maximalIdeal_of_surjective φ
          Ideal.Quotient.mk_surjective).symm]
        rw [Ideal.comap_map_of_surjective φ Ideal.Quotient.mk_surjective,
          ← RingHom.ker_eq_comap_bot, Ideal.mk_ker,
          sup_eq_left.mpr (Ideal.span_le.mpr (by rintro y rfl; exact hx))]
      exact hh.trans hm
    simpa using hc
  have hbound : m.spanFinrank ≤ mq.spanFinrank + 1 := by
    rw [← ht]
    calc
      _ ≤ t.ncard := Submodule.spanFinrank_span_le_ncard_of_finite hfin
      _ ≤ (a '' (s : Set Q)).ncard + 1 := Set.ncard_insert_le _ _
      _ ≤ (s : Set Q).ncard + 1 := Nat.add_le_add_right (Set.ncard_image_le s.finite_toSet) 1
      _ = mq.spanFinrank + 1 := by rw [Set.ncard_coe_finset, hcard]
  apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
  have hdim := ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim_of_mem_jacobson
    hreg (by simpa [ringJacobson_eq_maximalIdeal] using hx)
  rw [← hdim, ← IsRegularLocalRing.spanFinrank_maximalIdeal (R := Q)]
  exact_mod_cast hbound

private theorem root_pow (R : Type u) [CommRing R] (f : R) (n : ℕ) :
    AdjoinRoot.root ((X : R[X]) ^ n - C f) ^ n =
      AdjoinRoot.of ((X : R[X]) ^ n - C f) f := by
  have h := AdjoinRoot.eval₂_root ((X : R[X]) ^ n - C f)
  simpa only [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C, sub_eq_zero] using h

set_option backward.isDefEq.respectTransparency false in
private def root_quotient_equiv (R : Type u) [CommRing R] (f : R) (n : ℕ) (hn : 0 < n) :
    (AdjoinRoot ((X : R[X]) ^ n - C f) ⧸
      Ideal.span {AdjoinRoot.root ((X : R[X]) ^ n - C f)}) ≃+*
      (R ⧸ Ideal.span {f}) := by
  let P := (X : R[X]) ^ n - C f
  let B := AdjoinRoot P
  let t := AdjoinRoot.root P
  let I := Ideal.span ({t} : Set B)
  let J := Ideal.span ({f} : Set R)
  let v := AdjoinRoot.lift (f := P) (Ideal.Quotient.mk J) 0 (by
    simp only [P, eval₂_sub, eval₂_pow, eval₂_X, eval₂_C, zero_pow hn.ne', zero_sub,
      neg_eq_zero]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self f))
  let g : B ⧸ I →+* R ⧸ J := Ideal.Quotient.lift I v (by
    intro y hy
    obtain ⟨z, rfl⟩ := Ideal.mem_span_singleton.mp hy
    rw [map_mul]
    have hv : v t = 0 := AdjoinRoot.lift_root _
    rw [hv, zero_mul])
  let w := (Ideal.Quotient.mk I).comp (AdjoinRoot.of P)
  have hw : w f = 0 := by
    change Ideal.Quotient.mk I (AdjoinRoot.of P f) = 0
    rw [← root_pow R f n, map_pow]
    have ht : Ideal.Quotient.mk I t = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self t)
    change (Ideal.Quotient.mk I t) ^ n = 0
    rw [ht, zero_pow hn.ne']
  let h : R ⧸ J →+* B ⧸ I := Ideal.Quotient.lift J w (by
    intro y hy
    obtain ⟨z, rfl⟩ := Ideal.mem_span_singleton.mp hy
    rw [map_mul, hw, zero_mul])
  apply RingEquiv.ofRingHom g h
  · apply Ideal.Quotient.ringHom_ext
    ext r
    change v (AdjoinRoot.of P r) = Ideal.Quotient.mk J r
    exact AdjoinRoot.lift_of _
  · apply Ideal.Quotient.ringHom_ext
    apply AdjoinRoot.ringHom_ext
    · ext r
      change h (g (Ideal.Quotient.mk I (AdjoinRoot.of P r))) =
        Ideal.Quotient.mk I (AdjoinRoot.of P r)
      change h (v (AdjoinRoot.of P r)) = _
      rw [show v (AdjoinRoot.of P r) = Ideal.Quotient.mk J r from AdjoinRoot.lift_of _]
      rfl
    · change h (g (Ideal.Quotient.mk I t)) = Ideal.Quotient.mk I t
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self t)]
      rw [map_zero, map_zero]

/-- A prime localization containing the root coordinate is regular local.

Source: Stacks Project, Tag 0EYH, the local verification over the divisor;
Tag 0EYG, the paragraph introducing the finite free root algebra.
(blueprint: lem-sbc-root-algebra-regular-at-root)

Proof: Put P = X^n-C(f), B = R[X]/(P), and t = the image of X. The positive
exponent makes P monic, and the monomial basis 1,t,...,t^(n-1) makes B finite
free over R. In particular B is Noetherian. Injective multiplication by f on R
therefore gives injective multiplication by its image on B. Since t^n=f,
multiplication by t is injective, and remains injective after localization.
Evaluation at X=0 identifies B/(t) with R/(f): imposing X=0 in the defining
relation imposes exactly f=0. For a prime q containing t, quotienting B_q by t
commutes with localization and identifies this quotient with the localization
of R/(f) at the prime induced by q. It is regular local by the regularity of
R/(f). In a Noetherian local ring a nonzerodivisor in the maximal ideal with
regular local quotient lifts regularity (Stacks Tag 00NU). Apply this to the
image of t in B_q. No invertibility of n or regularity of R is needed here.
The zero ring has no primes, and if f is a unit then t is a unit, so the
hypothesis t in q is impossible; n=1 reduces to the same lifting argument. -/
theorem isRegularLocalRing_atPrime_of_root_mem
    (R : Type u) [CommRing R] [IsNoetherianRing R] (f : R)
    (hf : IsSMulRegular R f) [IsRegularRing (R ⧸ Ideal.span {f})]
    (n : ℕ) (hn : 0 < n)
    (q : Ideal (AdjoinRoot ((Polynomial.X : Polynomial R) ^ n - Polynomial.C f)))
    [q.IsPrime]
    (ht : AdjoinRoot.root ((Polynomial.X : Polynomial R) ^ n - Polynomial.C f) ∈ q) :
    IsRegularLocalRing (Localization.AtPrime q) := by
  classical
  let P := (X : R[X]) ^ n - C f
  let B := AdjoinRoot P
  let t := AdjoinRoot.root P
  let I := Ideal.span ({t} : Set B)
  let L := Localization.AtPrime q
  let a := algebraMap B L
  have hmonic : P.Monic := Polynomial.monic_X_pow_sub_C f hn.ne'
  have : Module.Free R B := hmonic.free_adjoinRoot
  have htf : t ^ n = algebraMap R B f := root_pow R f n
  have htfreg : IsSMulRegular B (t ^ n) := by
    rw [htf]
    exact hf.of_flat
  have htreg : IsSMulRegular B t := (IsSMulRegular.pow_iff hn).mp htfreg
  have hxreg : IsSMulRegular L (a t) := htreg.of_flat
  have hx : a t ∈ maximalIdeal L :=
    (IsLocalization.AtPrime.to_map_mem_maximal_iff L q t).mpr ht
  have hIq : I ≤ q := Ideal.span_le.mpr (by rintro x rfl; exact ht)
  let q' := q.map (Ideal.Quotient.mk I)
  have hq' : q'.IsPrime := Ideal.isPrime_map_quotientMk_of_isPrime hIq
  have hcomap : q'.comap (Ideal.Quotient.mk I) = q := by
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
      ← RingHom.ker_eq_comap_bot, Ideal.mk_ker, sup_eq_left.mpr hIq]
  have hBQ : IsRegularRing (B ⧸ I) :=
    IsRegularRing.of_ringEquiv (root_quotient_equiv R f n hn).symm
  let : Algebra B (B ⧸ I) := Ideal.Quotient.algebra B
  have hcompl : Algebra.algebraMapSubmonoid (B ⧸ I) q.primeCompl = q'.primeCompl := by
    change Submonoid.map (Ideal.Quotient.mk I) q.primeCompl = q'.primeCompl
    have h := Ideal.map_primeCompl_comap_of_surjective (Ideal.Quotient.mk I)
      Ideal.Quotient.mk_surjective q'
    simpa only [hcomap] using h
  have : IsLocalization q'.primeCompl (L ⧸ I.map a) := by
    rw [← hcompl]
    infer_instance
  have hloc : IsRegularLocalRing (L ⧸ I.map a) :=
    IsRegularLocalRing.of_ringEquiv
      (IsLocalization.algEquiv q'.primeCompl (Localization.AtPrime q')
        (L ⧸ I.map a)).toRingEquiv
  have hmap : I.map a = Ideal.span ({a t} : Set L) := by
    rw [Ideal.map_span, Set.image_singleton]
  have : IsRegularLocalRing (L ⧸ Ideal.span {a t}) := by
    rw [← hmap]
    exact hloc
  exact lift_regular L (a t) hx hxreg

end

end AdjoinRoot
