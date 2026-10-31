/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.TraitSliceGaloisClosure
public import WeilConjectures.TraceFormula.Specialization.TraitSliceGaloisSepClosed

/-!

# Henselian discrete valuation rings in `K⟦t⟧` with residue field `κ` are separably closed in
`K((t))`

Let `κ` be a separably closed field, `K ⊇ κ` an algebraically closed field of transcendence
degree `≤ 1` over `κ`, `R` a henselian discrete valuation ring with a uniformizer `π` and
`ι : R ⟶ K⟦t⟧` a local injection with `ι π = t`, such that

* (H1) the constants `κ ⊆ K⟦t⟧` lie in `ι(R)`, and
* (H2) `ι(R) ⊆ κ⟦t⟧`.

Then `Frac R` is separably closed in `K((t))`
(`IsDiscreteValuationRing.mem_range_lift_of_isSeparable`): an element separable over `Frac R` is
separable over `κ((t))`, hence lies in `κ((t))`
(`AlgebraicGeometry.mem_range_traitLaurentFieldMap_of_isSeparable`); after clearing a power of
`t` it is a simple root in `κ⟦t⟧`, which is the `t`-adic closure of `ι(R)` by (H1), and it lies in
`ι(R)` by the Hensel argument (`IsDiscreteValuationRing.mem_range_of_isRoot_of_forall_exists_dvd`).

For the strict localization `S'` of `𝔸¹_S` at the generic point of its special fibre, with
`κ = k'(x)^sep` and `K = k'(x)^alg`, this is the separable closedness of `Frac S'` in
`K((t))` used in SGA 4½, [Th. finitude], 3.3–3.4.

-/

@[expose] public section

universe u

open Polynomial PowerSeries IsLocalRing

namespace IsDiscreteValuationRing

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {K : Type u} [Field K] (ι : R →+* PowerSeries K) {π : R} (hπ : Irreducible π)
  (hιπ : ι π = PowerSeries.X) {κ : Type u} [Field κ] [Algebra κ K]

omit [IsDomain R] [IsDiscreteValuationRing R] in
include hιπ in
/-- **Density**: if the constants `κ` lie in `ι(R)`, every power series with coefficients in `κ`
is a `t`-adic limit of elements of `ι(R)`. -/
lemma exists_X_pow_dvd_sub_map (h₁ : ∀ a : κ, PowerSeries.C (algebraMap κ K a) ∈ ι.range)
    (n : ℕ) (φ : PowerSeries κ) :
    ∃ z : R, (PowerSeries.X : PowerSeries K) ^ n ∣ ι z - PowerSeries.map (algebraMap κ K) φ := by
  induction n generalizing φ with
  | zero => exact ⟨0, by simp⟩
  | succ n ih =>
    obtain ⟨z₁, hz₁⟩ := ih (PowerSeries.mk fun p ↦ coeff (p + 1) φ)
    obtain ⟨r₀, hr₀⟩ := h₁ (PowerSeries.constantCoeff φ)
    refine ⟨r₀ + π * z₁, ?_⟩
    conv_rhs => rw [φ.eq_X_mul_shift_add_const]
    rw [map_add, map_mul, hr₀, hιπ, map_add, map_mul, PowerSeries.map_X, PowerSeries.map_C]
    convert mul_dvd_mul_left (PowerSeries.X : PowerSeries K) hz₁ using 1
    · rw [pow_succ']
    · ring

/-- The factorisation of `ι` through `κ⟦t⟧` when `ι(R) ⊆ κ⟦t⟧`. -/
noncomputable def liftCoeff (h₂ : ∀ r n, coeff n (ι r) ∈ (algebraMap κ K).range) :
    R →+* PowerSeries κ :=
  have hinj : Function.Injective (PowerSeries.map (algebraMap κ K)) :=
    PowerSeries.map_injective _ (algebraMap κ K).injective
  have hmem : ∀ r, ι r ∈ (PowerSeries.map (algebraMap κ K)).range := fun r ↦
    ⟨PowerSeries.mk fun n ↦ (h₂ r n).choose, by ext n; simp [(h₂ r n).choose_spec]⟩
  ((RingEquiv.ofLeftInverse (Function.leftInverse_invFun hinj)).symm.toRingHom).comp
    (ι.codRestrict _ hmem)

omit [IsDomain R] [IsDiscreteValuationRing R] in
lemma map_liftCoeff (h₂ : ∀ r n, coeff n (ι r) ∈ (algebraMap κ K).range) (r : R) :
    PowerSeries.map (algebraMap κ K) (liftCoeff ι h₂ r) = ι r := by
  simp only [liftCoeff, RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe,
    RingHom.coe_coe]
  exact congrArg Subtype.val ((RingEquiv.ofLeftInverse _).apply_symm_apply _)

omit [IsDomain R] [IsDiscreteValuationRing R] in
/-- A power series over `K` whose image in `K((t))` comes from `κ((t))` has coefficients in `κ`. -/
lemma coeff_mem_range_of_algebraMap_mem_range {φ : PowerSeries K}
    (h : algebraMap (PowerSeries K) (FractionRing (PowerSeries K)) φ ∈
      (AlgebraicGeometry.traitLaurentFieldMap κ K).range) (n : ℕ) :
    coeff n φ ∈ (algebraMap κ K).range := by
  obtain ⟨w, hw⟩ := h
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := PowerSeries κ) w
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  obtain ⟨u, hu, hbu⟩ := PowerSeries.exists_eq_X_pow_mul_isUnit hb0
  have hinjK : Function.Injective (algebraMap (PowerSeries K) (FractionRing (PowerSeries K))) :=
    IsFractionRing.injective _ _
  have hbK : algebraMap (PowerSeries K) (FractionRing (PowerSeries K))
      (PowerSeries.map (algebraMap κ K) b) ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ hinjK, map_eq_zero_iff _
      (PowerSeries.map_injective _ (algebraMap κ K).injective)]
    exact hb0
  rw [map_div₀, AlgebraicGeometry.traitLaurentFieldMap_algebraMap,
    AlgebraicGeometry.traitLaurentFieldMap_algebraMap, div_eq_iff hbK, ← map_mul] at hw
  have h₁ := hinjK hw
  rw [hbu, map_mul, map_pow, PowerSeries.map_X] at h₁
  have h₂ : φ * PowerSeries.X ^ b.order.toNat =
      PowerSeries.map (algebraMap κ K) (a * ↑hu.unit⁻¹) := by
    rw [map_mul, h₁]
    have : PowerSeries.map (algebraMap κ K) u *
        PowerSeries.map (algebraMap κ K) ↑hu.unit⁻¹ = 1 := by
      rw [← map_mul, hu.mul_val_inv, map_one]
    calc φ * PowerSeries.X ^ b.order.toNat
        = φ * (PowerSeries.X ^ b.order.toNat * PowerSeries.map (algebraMap κ K) u) *
          PowerSeries.map (algebraMap κ K) ↑hu.unit⁻¹ := by
            rw [← mul_assoc φ, mul_assoc (φ * _), this, mul_one]
      _ = _ := by ring
  have h₃ := congrArg (PowerSeries.coeff (n + b.order.toNat)) h₂
  rw [PowerSeries.coeff_mul_X_pow, PowerSeries.coeff_map] at h₃
  exact ⟨_, h₃.symm⟩

section Main

variable (hι : Function.Injective ι)

omit [IsDomain R] [IsDiscreteValuationRing R] in
include hι in
lemma injective_algebraMap_comp :
    Function.Injective ((algebraMap (PowerSeries K) (FractionRing (PowerSeries K))).comp ι) :=
  by rw [RingHom.coe_comp]; exact (IsFractionRing.injective _ _).comp hι

/-- The embedding `Frac R ⟶ K((t))` induced by `ι`. -/
noncomputable def fractionRingLift : FractionRing R →+* FractionRing (PowerSeries K) :=
  IsFractionRing.lift (injective_algebraMap_comp ι hι)

omit [IsDiscreteValuationRing R] in
lemma fractionRingLift_algebraMap (r : R) :
    fractionRingLift ι hι (algebraMap R _ r) = algebraMap _ _ (ι r) :=
  IsFractionRing.lift_algebraMap _ r

variable [IsLocalHom ι] [HenselianLocalRing R] [IsSepClosed κ] [IsAlgClosed K]

include hπ hιπ in
/-- **`Frac R` is separably closed in `K((t))`**: for a henselian discrete valuation ring
`ι : R ⟶ K⟦t⟧` with uniformizer `π ↦ t`, containing the constants `κ` and contained in `κ⟦t⟧`,
every element of `K((t))` separable over `Frac R` lies in `Frac R`. -/
theorem mem_range_fractionRingLift_of_isSeparable (htr : Algebra.trdeg κ K ≤ 1)
    (h₁ : ∀ a : κ, PowerSeries.C (algebraMap κ K a) ∈ ι.range)
    (h₂ : ∀ r n, PowerSeries.coeff n (ι r) ∈ (algebraMap κ K).range)
    (y : FractionRing (PowerSeries K))
    (hy : letI := (fractionRingLift ι hι).toAlgebra; IsSeparable (FractionRing R) y) :
    y ∈ (fractionRingLift ι hι).range := by
  let _ : Algebra (FractionRing R) (FractionRing (PowerSeries K)) :=
    (fractionRingLift ι hι).toAlgebra
  set jF := fractionRingLift ι hι
  set φK := algebraMap (PowerSeries K) (FractionRing (PowerSeries K))
  have hφK : Function.Injective φK := IsFractionRing.injective _ _
  -- clear the denominator by a power of `t`
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := PowerSeries K) y
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  obtain ⟨w, hw, hbw⟩ := PowerSeries.exists_eq_X_pow_mul_isUnit hb0
  set v := b.order.toNat
  set y₁ := a * ↑hw.unit⁻¹
  have hπv : jF (algebraMap R _ (π ^ v)) = φK (PowerSeries.X ^ v) := by
    rw [fractionRingLift_algebraMap, map_pow, hιπ]
  have hX0 : φK (PowerSeries.X ^ v) ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ hφK]; exact pow_ne_zero _ PowerSeries.X_ne_zero
  have hw0 : φK w ≠ 0 := by rw [Ne, map_eq_zero_iff _ hφK]; exact hw.ne_zero
  have hyw : φK y₁ * φK w = φK a := by
    rw [← map_mul, mul_assoc, hw.val_inv_mul, mul_one]
  have hy₁ : φK y₁ = φK a / φK b * jF (algebraMap R _ (π ^ v)) := by
    rw [hπv, hbw, map_mul φK (PowerSeries.X ^ v) w, div_mul_eq_mul_div,
      eq_div_iff (mul_ne_zero hX0 hw0), ← hyw]
    ring
  -- `y₁` is separable over `Frac R`
  have hsep₁ : IsSeparable (FractionRing R) (φK y₁) := by
    rw [hy₁]
    exact Field.isSeparable_mul hy (isSeparable_algebraMap _)
  -- hence over `κ((t))`, so it lies in `κ((t))`
  have hinjκ : Function.Injective
      ((algebraMap (PowerSeries κ) (FractionRing (PowerSeries κ))).comp (liftCoeff ι h₂)) := by
    rw [RingHom.coe_comp]
    refine (IsFractionRing.injective _ _).comp fun r s hrs ↦ hι ?_
    rw [← map_liftCoeff ι h₂ r, ← map_liftCoeff ι h₂ s, hrs]
  let jκ : FractionRing R →+* FractionRing (PowerSeries κ) := IsFractionRing.lift hinjκ
  let _ : Algebra (FractionRing R) (FractionRing (PowerSeries κ)) := jκ.toAlgebra
  let _ : Algebra (FractionRing (PowerSeries κ)) (FractionRing (PowerSeries K)) :=
    (AlgebraicGeometry.traitLaurentFieldMap κ K).toAlgebra
  have htower : (AlgebraicGeometry.traitLaurentFieldMap κ K).comp jκ = jF := by
    refine IsLocalization.ringHom_ext (nonZeroDivisors R) (RingHom.ext fun r ↦ ?_)
    simp only [RingHom.coe_comp, Function.comp_apply, jκ, IsFractionRing.lift_algebraMap,
      AlgebraicGeometry.traitLaurentFieldMap_algebraMap, map_liftCoeff, jF,
      fractionRingLift_algebraMap]
  have : IsScalarTower (FractionRing R) (FractionRing (PowerSeries κ))
      (FractionRing (PowerSeries K)) :=
    IsScalarTower.of_algebraMap_eq fun x ↦ (RingHom.congr_fun htower x).symm
  have hmem := AlgebraicGeometry.mem_range_traitLaurentFieldMap_of_isSeparable htr (φK y₁)
    (hsep₁.tower_top (FractionRing (PowerSeries κ)))
  have hc := coeff_mem_range_of_algebraMap_mem_range hmem
  let φ₀ : PowerSeries κ := PowerSeries.mk fun n ↦ (hc n).choose
  have hφ₀ : PowerSeries.map (algebraMap κ K) φ₀ = y₁ := by
    ext n
    simp [φ₀, (hc n).choose_spec]
  -- a polynomial over `R` with the simple root `y₁`
  set p := minpoly (FractionRing R) (φK y₁)
  have hpsep : p.Separable := hsep₁
  obtain ⟨c, hcmem, hcp⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors R) p
  set f := IsLocalization.integerNormalization (nonZeroDivisors R) p
  have hcomp : jF.comp (algebraMap R (FractionRing R)) = φK.comp ι :=
    RingHom.ext fun r ↦ fractionRingLift_algebraMap ι hι r
  have heval : ∀ g : R[X], φK ((g.map ι).eval y₁) =
      ((g.map (algebraMap R (FractionRing R))).map jF).eval (φK y₁) := fun g ↦ by
    rw [Polynomial.eval_map, Polynomial.hom_eval₂, Polynomial.map_map, hcomp, Polynomial.eval_map]
  have hjc : jF (algebraMap R _ c) ≠ 0 := by
    rw [fractionRingLift_algebraMap, Ne, map_eq_zero_iff _ hφK, map_eq_zero_iff _ hι]
    exact nonZeroDivisors.ne_zero hcmem
  have hsmul : ∀ q : (FractionRing R)[X], (c • q).map jF =
      Polynomial.C (jF (algebraMap R _ c)) * q.map jF := fun q ↦ by
    rw [Algebra.smul_def, Polynomial.algebraMap_apply, Polynomial.map_mul, Polynomial.map_C]
  have hroot : (f.map ι).IsRoot y₁ := by
    rw [IsRoot, ← map_eq_zero_iff _ hφK, heval, hcp, hsmul, Polynomial.eval_mul,
      Polynomial.eval_C, ← Polynomial.eval₂_eq_eval_map]
    change _ * Polynomial.aeval (φK y₁) p = 0
    rw [minpoly.aeval, mul_zero]
  have hder : (f.map ι).derivative.eval y₁ ≠ 0 := by
    rw [Polynomial.derivative_map, Ne, ← map_eq_zero_iff _ hφK, heval, ← Polynomial.derivative_map,
      hcp, Polynomial.derivative_smul, hsmul, Polynomial.eval_mul, Polynomial.eval_C,
      ← Polynomial.eval₂_eq_eval_map]
    change _ * Polynomial.aeval (φK y₁) (Polynomial.derivative p) ≠ 0
    exact mul_ne_zero hjc (hpsep.aeval_derivative_ne_zero (minpoly.aeval _ _))
  obtain ⟨z, hz⟩ := mem_range_of_isRoot_of_forall_exists_dvd ι hπ hιπ f hroot hder
    (fun n ↦ by simpa [hφ₀] using exists_X_pow_dvd_sub_map ι hιπ h₁ n φ₀)
  refine ⟨algebraMap R _ z / algebraMap R _ (π ^ v), ?_⟩
  have hπ0 : jF (algebraMap R _ (π ^ v)) ≠ 0 := hπv ▸ hX0
  rw [map_div₀, fractionRingLift_algebraMap, hz, hy₁, mul_div_cancel_right₀ _ hπ0]

end Main

end IsDiscreteValuationRing
