/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.GroupTheory.TateModule
import Mathlib.Algebra.CharP.CharAndCard
import WeilConjectures.Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-!
# Frobenius on roots of unity and the cyclotomic Tate module

Source: Deligne, Weil I (2.2), pp. 280--281, and Weil II (1.1.7), pp. 150--151
(blueprint: lem-pur-frobenius-roots-of-unity-power).

The integral cyclotomic Tate module is `AddCommGroup.tateModule ℓ (Additive D.kˣ)`, the
unfolding of the existing upstream `cyclotomicTateModule D.k ℓ`. Its coordinates
are units killed by the powers of the coefficient prime, written additively, and its
transition maps are multiplication by that prime. The induced maps below are the existing
coordinatewise linear maps `AddCommGroup.tateModule.map`. A linear equivalence with the
coefficient ring expresses freeness of rank one. The unit `u` is specified by its value `q`,
so the scalar actions are independent of any choice of generator.
-/

@[expose] public section

universe u

namespace WeilConjectures.FiniteFieldDatum

/-- Arithmetic Frobenius raises roots of unity to the `q`-th power; geometric Frobenius
raises them to any inverse exponent modulo their order. On the integral cyclotomic Tate
module these are multiplication by the unit `q` and its inverse.

Source: Deligne, Weil I (2.2), pp. 280--281, and Weil II (1.1.7), pp. 150--151
(blueprint: lem-pur-frobenius-roots-of-unity-power).

Proof: Since `N` is prime to the characteristic, `X ^ N - 1` is separable and splits over
`D.k`. It has exactly `N` roots, and the finite subgroup of units consisting of those roots
is cyclic. Any field automorphism preserves the equation and its inverse does too, giving
bijectivity on the roots. Arithmetic Frobenius is `z ↦ z ^ q`. Since `q = p ^ a` is coprime
to `N`, Bezout gives an integer inverse `q'` modulo `N`. On an `N`-th root, raising to `q'`
is inverse to raising to `q`; this also works for negative `q'` because roots are units.
For the coefficient prime `ℓ ≠ p`, choose a primitive `ℓ`-th root and successively lift it
along the surjective `ℓ`-power maps. These lifts are primitive of orders `ℓ ^ r` and form a
compatible generator of the inverse limit. Expressing every compatible system in these
cyclic generators identifies its exponents with `ℤ_[ℓ]`, proving freeness of rank one.
The coordinatewise arithmetic action raises each coordinate to `q`, hence is scalar `q`
under the canonical `ℤ_[ℓ]`-action. This scalar is a unit because `ℓ` does not divide `q`.
The coordinatewise geometric action is its inverse, hence is scalar `q⁻¹`.
The imported upstream definitions of the Tate module and its induced maps supply exactly
these compatible systems and their componentwise actions; no generator is chosen in the
statement. -/
theorem frobenius_rootsOfUnity_power (D : WeilConjectures.FiniteFieldDatum.{u})
    (N : ℕ) (hN : 1 ≤ N) (hNp : N.Coprime D.p) :
    (IsCyclic (rootsOfUnity N D.k) ∧ Nat.card (rootsOfUnity N D.k) = N ∧
      ∀ σ : D.k ≃+* D.k,
        Set.BijOn (Units.map σ.toRingHom.toMonoidHom)
          (rootsOfUnity N D.k) (rootsOfUnity N D.k)) ∧
    ((∀ ζ : rootsOfUnity N D.k,
        (@FiniteField.frobeniusAlgEquivOfAlgebraic D.k₀ _ (Fintype.ofFinite D.k₀)
          D.k _ _ _) ((ζ : D.kˣ) : D.k) = ((ζ : D.kˣ) : D.k) ^ D.q) ∧
      (∃ q' : ℤ, Int.ModEq (N : ℤ) ((D.q : ℤ) * q') 1) ∧
      ∀ q' : ℤ, Int.ModEq (N : ℤ) ((D.q : ℤ) * q') 1 →
        ∀ ζ : rootsOfUnity N D.k,
          Units.map
            (@FiniteField.frobeniusAlgEquivOfAlgebraic D.k₀ _ (Fintype.ofFinite D.k₀)
              D.k _ _ _).symm.toRingHom.toMonoidHom (ζ : D.kˣ) = (ζ : D.kˣ) ^ q') ∧
    (∀ (ℓ : ℕ) [Fact ℓ.Prime], ℓ ≠ D.p →
      Nonempty (AddCommGroup.tateModule ℓ (Additive D.kˣ) ≃ₗ[ℤ_[ℓ]] ℤ_[ℓ]) ∧
        ∃ u : ℤ_[ℓ]ˣ, (u : ℤ_[ℓ]) = (D.q : ℤ_[ℓ]) ∧
          ∀ t : AddCommGroup.tateModule ℓ (Additive D.kˣ),
            AddCommGroup.tateModule.map
              (Units.map
                (@FiniteField.frobeniusAlgEquivOfAlgebraic D.k₀ _ (Fintype.ofFinite D.k₀)
                  D.k _ _ _).toRingHom.toMonoidHom).toAdditive t = (u : ℤ_[ℓ]) • t ∧
            AddCommGroup.tateModule.map
              (Units.map
                (@FiniteField.frobeniusAlgEquivOfAlgebraic D.k₀ _ (Fintype.ofFinite D.k₀)
                  D.k _ _ _).symm.toRingHom.toMonoidHom).toAdditive t =
              (↑(u⁻¹) : ℤ_[ℓ]) • t) :=
  by
  classical
  let _ : Fintype D.k₀ := Fintype.ofFinite D.k₀
  have hc : Fintype.card D.k₀ = D.q := by
    simpa only [Nat.card_eq_fintype_card] using D.card_base
  have _ : Fact D.p.Prime := ⟨D.prime⟩
  have _ : CharP D.k₀ D.p := charP_of_card_eq_prime_pow (hc.trans D.cardinality_eq)
  have _ : CharP D.k D.p := charP_of_injective_algebraMap' D.k₀ D.p
  have _ : IsAlgClosed D.k := IsAlgClosure.isAlgClosed D.k₀
  have _ : NeZero N := ⟨by omega⟩
  have _ : NeZero (N : D.k) := ⟨by
    intro h
    exact (D.prime.coprime_iff_not_dvd.mp hNp.symm) ((CharP.cast_eq_zero_iff D.k D.p N).mp h)⟩
  let F := FiniteField.frobeniusAlgEquivOfAlgebraic D.k₀ D.k
  have hF (x : D.k) : F x = x ^ D.q := by
    change x ^ Fintype.card D.k₀ = x ^ D.q
    rw [hc]
  have hFu (x : D.kˣ) : Units.map F.toRingHom.toMonoidHom x = x ^ D.q := by
    apply Units.ext
    exact hF x
  have hcop : D.q.Coprime N := by
    rw [D.cardinality_eq]
    exact hNp.symm.pow_left _
  refine ⟨?_, ⟨?_, ?_, ?_⟩, ?_⟩
  · obtain ⟨_, _, ζ, hζ, _⟩ := IsSepClosed.exists_isPrimitiveRoot.{u, u} D.k N
    refine ⟨inferInstance, hζ.card_rootsOfUnity, ?_⟩
    intro σ
    refine ⟨?_, ?_, ?_⟩
    · intro x hx
      simp only [SetLike.mem_coe, mem_rootsOfUnity] at hx ⊢
      rw [← map_pow, hx, map_one]
    · intro x _ y _ hxy
      apply Units.ext
      exact σ.injective (congrArg Units.val hxy)
    · intro x hx
      refine ⟨Units.map σ.symm.toRingHom.toMonoidHom x, ?_, ?_⟩
      · simp only [SetLike.mem_coe, mem_rootsOfUnity] at hx ⊢
        rw [← map_pow, hx, map_one]
      · apply Units.ext
        exact σ.apply_symm_apply _
  · intro ζ
    exact hF _
  · refine ⟨Nat.gcdA D.q N, ?_⟩
    apply Int.modEq_iff_dvd.mpr
    refine ⟨Nat.gcdB D.q N, ?_⟩
    have hbez := Nat.gcd_eq_gcd_ab D.q N
    rw [hcop.gcd_eq_one] at hbez
    push_cast at hbez
    linarith
  · intro q' hq' ζ
    change Units.map F.symm.toRingHom.toMonoidHom (ζ : D.kˣ) = (ζ : D.kˣ) ^ q'
    apply Units.map_injective (f := F.toRingHom.toMonoidHom) F.injective
    have hz : (ζ : D.kˣ) ^ N = 1 := (mem_rootsOfUnity N _).mp ζ.2
    have hm : orderOf (ζ : D.kˣ) ∣ N := orderOf_dvd_of_pow_eq_one hz
    have he : (ζ : D.kˣ) ^ ((D.q : ℤ) * q') = (ζ : D.kˣ) := by
      nth_rw 2 [← zpow_one (ζ : D.kˣ)]
      rw [zpow_eq_zpow_iff_modEq]
      exact hq'.of_dvd (by exact_mod_cast hm)
    calc
      _ = (ζ : D.kˣ) := by
        apply Units.ext
        exact F.apply_symm_apply _
      _ = ((ζ : D.kˣ) ^ D.q) ^ q' := by
        rw [← zpow_natCast, ← zpow_mul, he]
      _ = _ := by rw [map_zpow, hFu]
  · intro ℓ _ hℓ
    have hpℓ : ℓ.Coprime D.p := (Nat.coprime_primes Fact.out D.prime).mpr hℓ
    have _ : NeZero (ℓ : D.k) := ⟨by
      intro h
      exact (D.prime.coprime_iff_not_dvd.mp hpℓ.symm)
        ((CharP.cast_eq_zero_iff D.k D.p ℓ).mp h)⟩
    have hdiv : ∀ x : Additive D.kˣ, ∃ y : Additive D.kˣ, (ℓ : ℤ) • y = x := by
      intro x
      obtain ⟨y, hy⟩ := IsAlgClosed.exists_pow_nat_eq (x.toMul : D.k) (Fact.out : ℓ.Prime).pos
      have hy0 : y ≠ 0 := by
        intro h
        rw [h, zero_pow (Fact.out : ℓ.Prime).ne_zero] at hy
        exact x.toMul.ne_zero hy.symm
      refine ⟨Additive.ofMul (Units.mk0 y hy0), ?_⟩
      apply Additive.toMul.injective
      change (Units.mk0 y hy0) ^ (ℓ : ℤ) = x.toMul
      rw [zpow_natCast]
      apply Units.ext
      exact hy
    let e : AddSubgroup.torsionBy (Additive D.kˣ) (ℓ : ℤ) ≃ rootsOfUnity ℓ D.k :=
      { toFun := fun x ↦ ⟨x.val.toMul, by
          rw [mem_rootsOfUnity]
          have hx : (ℓ : ℤ) • (x : Additive D.kˣ) = 0 := x.prop
          have hx' := congrArg Additive.toMul hx
          simpa only [toMul_zsmul, zpow_natCast, toMul_zero] using hx' ⟩
        invFun := fun x ↦ ⟨Additive.ofMul x.val, by
          change (ℓ : ℤ) • Additive.ofMul x.val = 0
          apply Additive.toMul.injective
          simpa only [toMul_zsmul, toMul_ofMul, zpow_natCast,
            toMul_zero] using (mem_rootsOfUnity ℓ _).mp x.prop⟩
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl }
    have hcard : Nat.card (AddSubgroup.torsionBy (Additive D.kˣ) (ℓ : ℤ)) = ℓ ^ 1 := by
      rw [Nat.card_congr e, HasEnoughRootsOfUnity.natCard_rootsOfUnity, pow_one]
    obtain ⟨eT⟩ := AddCommGroup.tateModule.nonempty_linearEquiv_of_natCard_eq
      ℓ (Additive D.kˣ) hdiv 1 hcard
    refine ⟨⟨eT.trans (LinearEquiv.piUnique ℤ_[ℓ] (fun _ : Fin 1 ↦ ℤ_[ℓ]))⟩, ?_⟩
    have hunit : IsUnit (D.q : ℤ_[ℓ]) := by
      rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff, D.cardinality_eq]
      exact hpℓ.pow_right _
    obtain ⟨u, hu⟩ := hunit
    refine ⟨u, hu, ?_⟩
    have hscalar (s : AddCommGroup.tateModule ℓ (Additive D.kˣ)) :
        AddCommGroup.tateModule.map (Units.map F.toRingHom.toMonoidHom).toAdditive s =
          (D.q : ℤ_[ℓ]) • s := by
      apply Subtype.ext
      funext n
      rw [AddCommGroup.tateModule.coe_map_apply, AddCommGroup.tateModule.coe_smul_apply,
        AddCommGroup.tateModule.appr_zsmul_coe_eq s (D.q : ℤ_[ℓ]) (x := D.q) (by simp)]
      change Additive.ofMul (Units.map F.toRingHom.toMonoidHom ((s.val n).toMul)) =
        Additive.ofMul (((s.val n).toMul) ^ (D.q : ℤ))
      rw [hFu, zpow_natCast]
    intro t
    constructor
    · rw [hu]
      exact hscalar t
    · change AddCommGroup.tateModule.map
        (Units.map F.symm.toRingHom.toMonoidHom).toAdditive t = (↑(u⁻¹) : ℤ_[ℓ]) • t
      have hcomp : AddCommGroup.tateModule.map
          (Units.map F.toRingHom.toMonoidHom).toAdditive
          (AddCommGroup.tateModule.map
            (Units.map F.symm.toRingHom.toMonoidHom).toAdditive t) = t := by
        apply Subtype.ext
        funext n
        rw [AddCommGroup.tateModule.coe_map_apply, AddCommGroup.tateModule.coe_map_apply]
        apply Additive.toMul.injective
        apply Units.ext
        exact F.apply_symm_apply _
      rw [hscalar, ← hu] at hcomp
      have hi := congrArg (fun s ↦ (↑(u⁻¹) : ℤ_[ℓ]) • s) hcomp
      simpa [smul_smul] using hi

end WeilConjectures.FiniteFieldDatum
