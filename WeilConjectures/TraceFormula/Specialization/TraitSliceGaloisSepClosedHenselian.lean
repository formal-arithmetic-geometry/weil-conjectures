/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.RingTheory.Localization.FractionRing
public import WeilConjectures.RingTheory.PowerSeries.HenselianDVRClosure
public import WeilConjectures.TraceFormula.Specialization.TraitSliceGaloisSepClosed

/-!
# Henselian DVRs in `K⟦t⟧` are separably closed in `K((t))`

Let `κ` be a separably closed field, `K ⊇ κ` an algebraically closed field of transcendence
degree `≤ 1` over `κ`, `R` a henselian discrete valuation ring with a uniformizer `π` and
`ι : R ⟶ K⟦t⟧` a local injection with `ι π = t`, such that

* (H1) the constants `κ ⊆ K⟦t⟧` lie in `ι(R)`, and
* (H2) `ι(R) ⊆ κ⟦t⟧`.

Then `Frac R` is separably closed in `K((t))`
(`IsDiscreteValuationRing.mem_range_isFractionRingMap_of_isSeparable`): an element separable over
`Frac R` is separable over `κ((t))`, hence lies in `κ((t))`
(`AlgebraicGeometry.mem_range_traitLaurentFieldMap_of_isSeparable`); after clearing a power of
`t` it is a simple root in `κ⟦t⟧`, which is the `t`-adic closure of `ι(R)` by (H1), and it lies in
`ι(R)` by the Hensel argument (`IsDiscreteValuationRing.mem_range_of_isRoot_of_forall_exists_dvd`).

For the strict localization `S'` of `𝔸¹_S` at the generic point of its special fibre, with
`κ = k'(x)^sep` and `K = k'(x)^alg`, this is the separable closedness of `Frac S'` in
`K((t))` used in SGA 4½, [Th. finitude], 3.3–3.4.
-/

@[expose] public section

universe u

open Polynomial IsLocalRing

namespace IsDiscreteValuationRing

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
  {K : Type u} [Field K] [IsAlgClosed K] {κ : Type u} [Field κ] [IsSepClosed κ] [Algebra κ K]

/-- **`Frac R` is separably closed in `K((t))`**: for a henselian discrete valuation ring
`ι : R ⟶ K⟦t⟧` with uniformizer `π ↦ t`, containing the constants `κ` (H1) and contained in
`κ⟦t⟧` (H2), every element of `K((t))` separable over `Frac R` lies in `Frac R`. -/
theorem mem_range_isFractionRingMap_of_isSeparable (ι : R →+* PowerSeries K) [IsLocalHom ι]
    (hι : Function.Injective ι) {π : R} (hπ : Irreducible π) (hιπ : ι π = PowerSeries.X)
    (htr : Algebra.trdeg κ K ≤ 1) (h₁ : ∀ a : κ, PowerSeries.C (algebraMap κ K a) ∈ ι.range)
    (h₂ : ∀ r n, PowerSeries.coeff n (ι r) ∈ (algebraMap κ K).range)
    (y : FractionRing (PowerSeries K))
    (hy : letI := (IsFractionRing.map (K := FractionRing R)
        (L := FractionRing (PowerSeries K)) hι).toAlgebra
      IsSeparable (FractionRing R) y) :
    y ∈ (IsFractionRing.map (K := FractionRing R) (L := FractionRing (PowerSeries K)) hι).range := by
  have hjF : ∀ r, IsFractionRing.map (K := FractionRing R) (L := FractionRing (PowerSeries K)) hι
      (algebraMap R _ r) = algebraMap _ _ (ι r) := IsFractionRing.map_algebraMap hι
  generalize IsFractionRing.map (K := FractionRing R) (L := FractionRing (PowerSeries K)) hι = jF
    at hy hjF ⊢
  let _ : Algebra (FractionRing R) (FractionRing (PowerSeries K)) := jF.toAlgebra
  set φK := algebraMap (PowerSeries K) (FractionRing (PowerSeries K))
  have hφK : Function.Injective φK := IsFractionRing.injective _ _
  -- clear the denominator by a power of `t`
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := PowerSeries K) y
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  obtain ⟨w, hw, hbw⟩ := PowerSeries.exists_eq_X_pow_mul_isUnit hb0
  set v := b.order.toNat
  set y₁ := a * ↑hw.unit⁻¹
  have hπv : jF (algebraMap R _ (π ^ v)) = φK (PowerSeries.X ^ v) := by
    rw [hjF, map_pow, hιπ]
  have hX0 : φK (PowerSeries.X ^ v) ≠ 0 :=
    (map_ne_zero_iff _ hφK).2 (pow_ne_zero _ PowerSeries.X_ne_zero)
  have hw0 : φK w ≠ 0 := (map_ne_zero_iff _ hφK).2 hw.ne_zero
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
  set ικ := PowerSeries.liftOfCoeffMemRange ι h₂
  have hικ : Function.Injective ικ := fun r s hrs ↦ hι (by
    rw [← PowerSeries.map_liftOfCoeffMemRange ι h₂ r, ← PowerSeries.map_liftOfCoeffMemRange ι h₂ s,
      hrs])
  let jκ : FractionRing R →+* FractionRing (PowerSeries κ) := IsFractionRing.map hικ
  let _ : Algebra (FractionRing R) (FractionRing (PowerSeries κ)) := jκ.toAlgebra
  let _ : Algebra (FractionRing (PowerSeries κ)) (FractionRing (PowerSeries K)) :=
    (AlgebraicGeometry.traitLaurentFieldMap κ K).toAlgebra
  have htower : (AlgebraicGeometry.traitLaurentFieldMap κ K).comp jκ = jF := by
    refine IsLocalization.ringHom_ext (nonZeroDivisors R) (RingHom.ext fun r ↦ ?_)
    simp [jκ, ικ, hjF, AlgebraicGeometry.traitLaurentFieldMap_algebraMap]
  have : IsScalarTower (FractionRing R) (FractionRing (PowerSeries κ))
      (FractionRing (PowerSeries K)) :=
    IsScalarTower.of_algebraMap_eq fun x ↦ (RingHom.congr_fun htower x).symm
  have hmem := AlgebraicGeometry.mem_range_traitLaurentFieldMap_of_isSeparable htr (φK y₁)
    (hsep₁.tower_top (FractionRing (PowerSeries κ)))
  have hc := PowerSeries.coeff_mem_range_of_algebraMap_mem_range
    (AlgebraicGeometry.traitLaurentFieldMap_algebraMap κ K) hmem
  let φ₀ : PowerSeries κ := PowerSeries.mk fun n ↦ (hc n).choose
  have hφ₀ : PowerSeries.map (algebraMap κ K) φ₀ = y₁ := by
    ext n
    simp [φ₀, (hc n).choose_spec]
  -- a polynomial over `R` with the simple root `y₁`
  set p := minpoly (FractionRing R) (φK y₁)
  have hpsep : p.Separable := hsep₁
  have hp : p.eval₂ jF (φK y₁) = 0 := by
    rw [← minpoly.aeval (FractionRing R) (φK y₁), Polynomial.aeval_def,
      RingHom.algebraMap_toAlgebra]
  have hp' : p.derivative.eval₂ jF (φK y₁) ≠ 0 := by
    rw [← RingHom.algebraMap_toAlgebra jF, ← Polynomial.aeval_def]
    exact hpsep.aeval_derivative_ne_zero (minpoly.aeval _ _)
  obtain ⟨c, hcmem, hcp⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors R) p
  set f := IsLocalization.integerNormalization (nonZeroDivisors R) p
  have hcomp : jF.comp (algebraMap R (FractionRing R)) = φK.comp ι := RingHom.ext hjF
  have heval : ∀ g : R[X], φK ((g.map ι).eval y₁) =
      ((g.map (algebraMap R (FractionRing R))).map jF).eval (φK y₁) := fun g ↦ by
    rw [Polynomial.eval_map, Polynomial.hom_eval₂, Polynomial.map_map, hcomp, Polynomial.eval_map]
  have hjc : jF (algebraMap R _ c) ≠ 0 := by
    rw [hjF, map_ne_zero_iff _ hφK, map_ne_zero_iff _ hι]
    exact nonZeroDivisors.ne_zero hcmem
  have hsmul : ∀ q : (FractionRing R)[X], (c • q).map jF =
      Polynomial.C (jF (algebraMap R _ c)) * q.map jF := fun q ↦ by
    rw [Algebra.smul_def, Polynomial.algebraMap_apply, Polynomial.map_mul, Polynomial.map_C]
  have hroot : (f.map ι).IsRoot y₁ := by
    rw [IsRoot, ← map_eq_zero_iff _ hφK, heval, hcp, hsmul, Polynomial.eval_mul,
      Polynomial.eval_C, ← Polynomial.eval₂_eq_eval_map, hp, mul_zero]
  have hder : (f.map ι).derivative.eval y₁ ≠ 0 := by
    rw [Polynomial.derivative_map, Ne, ← map_eq_zero_iff _ hφK, heval, ← Polynomial.derivative_map,
      hcp, Polynomial.derivative_smul, hsmul, Polynomial.eval_mul, Polynomial.eval_C,
      ← Polynomial.eval₂_eq_eval_map]
    exact mul_ne_zero hjc hp'
  obtain ⟨z, hz⟩ := mem_range_of_isRoot_of_forall_exists_dvd ι hπ hιπ f hroot hder
    (fun n ↦ by simpa [hφ₀] using PowerSeries.exists_X_pow_dvd_sub_map_of_C_mem_range ι hιπ h₁ n φ₀)
  refine ⟨algebraMap R _ z / algebraMap R _ (π ^ v), ?_⟩
  have hπ0 : jF (algebraMap R _ (π ^ v)) ≠ 0 := hπv ▸ hX0
  rw [map_div₀, hjF, hz, hy₁, mul_div_cancel_right₀ _ hπ0]

end IsDiscreteValuationRing
