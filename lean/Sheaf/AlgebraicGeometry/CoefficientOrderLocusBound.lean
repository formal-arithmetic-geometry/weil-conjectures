/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U8
-/
module

public import Sheaf.AlgebraicGeometry.CoefficientDivisionData
import Mathlib.RingTheory.MvPowerSeries.Inverse

/-! # The Taylor order bound on the coefficient order locus

Source: Bierstone--Milman, Invent. Math. 128 (1997), completion of Theorem 9.6, p.282.
(blueprint: lem-trf-coefficient-order-locus-bound)
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory MonomialDiagram

namespace AlgebraicGeometry.HilbertCoefficient

/-- A centered ring homomorphism satisfies the lower order bound on the germ-defined
coefficient order locus. Smoothness and differentiation are unnecessary here.

Source: BM 1997, completion of Theorem 9.6, p.282, order-locus argument
(blueprint: lem-trf-coefficient-order-locus-bound).

Proof: Since N is affine, its stalk at b is the localization of global sections
at the kernel of residue evaluation. Every denominator has nonzero evaluation,
so its Taylor series has invertible constant coefficient and is a unit. Extend
T to the stalk by the universal property of localization. Constant coefficient
of this extension is the residue map, by equality on global sections and
uniqueness of localization extensions. Thus it sends the maximal ideal into the
kernel of constant coefficient, and sends its h-th power into the h-th power of
that ideal. The latter consists of series of order at least h. For a mixed
exponent (delta,gamma) of degree less than d_i, gamma has degree less than d_i,
and the order-locus hypothesis puts its coefficient germ in m_b^(d_i-|gamma|).
Its Taylor coefficient at delta therefore vanishes, since |delta| is smaller
than that exponent. All coefficients of total degree less than d_i vanish,
which is precisely the claimed lower order bound. Zero series and degree-zero
vertices are included. -/
theorem coefficient_order_locus_bound {N : Scheme.{u}} [IsAffine N] {m n s : ℕ}
    (α : Fin s → Fin n →₀ ℕ)
    (c : Fin s → (Fin n →₀ ℕ) → Γ(N, ⊤)) (b : N)
    (T : Γ(N, ⊤) →+* MvPowerSeries (Fin m) (N.residueField b))
    (hconst : ∀ r : Γ(N, ⊤), MvPowerSeries.constantCoeff (T r) = N.Γevaluation b r)
    (hb : b ∈ coefficientFamilyOrderLocus α c) :
    ∀ i : Fin s, ((α i).degree : ℕ∞) ≤ (coefficientFamilySeries T c i).order := by
  classical
  let P := (isAffineOpen_top N).primeIdealOf ⟨b, trivial⟩
  let R := N.presheaf.stalk b
  let : Algebra Γ(N, ⊤) R :=
    TopCat.Presheaf.algebra_section_stalk N.presheaf (⟨b, trivial⟩ : (⊤ : N.Opens))
  have : IsLocalization.AtPrime R P.asIdeal :=
    (isAffineOpen_top N).isLocalization_stalk ⟨b, trivial⟩
  have hunit : ∀ x : P.asIdeal.primeCompl, IsUnit (T x.val) := by
    intro x
    apply MvPowerSeries.isUnit_iff_constantCoeff.mpr
    rw [hconst]
    have hx := (IsLocalization.map_units R x).map (N.residue b).hom
    exact hx
  let E : R →+* MvPowerSeries (Fin m) (N.residueField b) := IsLocalization.lift hunit
  have hE (r : Γ(N, ⊤)) :
      E (N.presheaf.germ ⊤ b (by trivial) r) = T r :=
    IsLocalization.lift_eq hunit r
  have hEconst : MvPowerSeries.constantCoeff.comp E = (N.residue b).hom := by
    apply IsLocalization.ringHom_ext P.asIdeal.primeCompl
    ext r
    change MvPowerSeries.constantCoeff (E (N.presheaf.germ ⊤ b (by trivial) r)) = _
    rw [hE, hconst]
    rfl
  let J : ℕ → Ideal (MvPowerSeries (Fin m) (N.residueField b)) := fun r ↦
    { carrier := {f | (r : ℕ∞) ≤ f.order}
      zero_mem' := by simp
      add_mem' := fun hx hy ↦ (le_min hx hy).trans MvPowerSeries.min_order_le_add
      smul_mem' := fun a f hf ↦ hf.trans
        ((le_add_left le_rfl).trans MvPowerSeries.le_order_mul) }
  have hmul (r t : ℕ) : J r * J t ≤ J (r + t) := by
    apply Ideal.mul_le.mpr
    intro x hx y hy
    change ((r + t : ℕ) : ℕ∞) ≤ (x * y).order
    rw [Nat.cast_add]
    exact (add_le_add hx hy).trans MvPowerSeries.le_order_mul
  have hpow : ∀ r : ℕ, J 1 ^ r ≤ J r := by
    intro r
    induction r with
    | zero =>
      intro x _
      change (0 : ℕ∞) ≤ x.order
      exact bot_le
    | succ r ih =>
      rw [pow_succ]
      exact (Ideal.mul_mono_left ih).trans (hmul r 1)
  have hmax : Ideal.map E (IsLocalRing.maximalIdeal R) ≤ J 1 := by
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    change (1 : ℕ∞) ≤ (E x).order
    apply MvPowerSeries.one_le_order_iff_constCoeff_eq_zero.mpr
    have hc := RingHom.congr_fun hEconst x
    exact hc.trans ((IsLocalRing.residue_eq_zero_iff x).mpr hx)
  have horder (r : Γ(N, ⊤)) (p : ℕ)
      (hr : N.presheaf.germ ⊤ b (by trivial) r ∈ IsLocalRing.maximalIdeal R ^ p) :
      (p : ℕ∞) ≤ (T r).order := by
    have hm := Ideal.mem_map_of_mem E hr
    rw [Ideal.map_pow] at hm
    have hp := hpow p ((pow_le_pow_left' hmax p) hm)
    change (p : ℕ∞) ≤ (E (N.presheaf.germ ⊤ b (by trivial) r)).order at hp
    rwa [hE] at hp
  intro i
  apply MvPowerSeries.nat_le_order
  intro e he
  let δ := Finsupp.comapDomain.addMonoidHom Sum.inl_injective e
  let γ := Finsupp.comapDomain.addMonoidHom Sum.inr_injective e
  have hdeg : δ.degree + γ.degree = e.degree := by
    simp [δ, γ, Finsupp.degree_eq_sum,
      Finsupp.comapDomain_apply, Fintype.sum_sum_type]
  have hγ : γ.degree < (α i).degree := by omega
  have hδ : δ.degree < (α i).degree - γ.degree := by omega
  have ho := horder (c i γ) ((α i).degree - γ.degree) (hb i γ hγ)
  change MvPowerSeries.coeff δ (T (c i γ)) = 0
  have hδ' : (δ.degree : ℕ∞) < ((α i).degree - γ.degree : ℕ) := by
    exact_mod_cast hδ
  exact MvPowerSeries.coeff_of_lt_order (hδ'.trans_le ho)

end AlgebraicGeometry.HilbertCoefficient
