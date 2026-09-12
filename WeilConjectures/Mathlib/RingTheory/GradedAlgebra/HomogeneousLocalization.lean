/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
public import WeilConjectures.Mathlib.RingTheory.GradedAlgebra.RingHom

/-!
# `HomogeneousLocalization.Away.map` and `HomogeneousLocalization.Away.lift`

We show that `HomogeneousLocalization.Away.map` is compatible with the canonical ring
homomorphisms from the degree-zero subrings, and that it is surjective as soon as the
graded ring homomorphism it is built from is.

We also construct `HomogeneousLocalization.Away.lift`: a ring homomorphism `φ : A →+* R`
inverting a homogeneous element `f` induces a ring homomorphism `(A_f)₀ →+* R` on the
degree-zero part of the localization away from `f`, sending `a / fⁿ` to `φ a * (φ f)⁻ⁿ`.
Its main properties are compatibility with postcomposition (`Away.comp_lift`) and
invariance under rescaling `φ` on `𝒜 n` by the `n`-th power of a fixed unit
(`Away.lift_eq_lift_of_eq_unit_pow_mul`).

Finally, `HomogeneousLocalization.isUnit_mk_iff` records that a fraction `a / f` in the
homogeneous localization at a homogeneous prime ideal `𝔭` is a unit exactly when `a ∉ 𝔭`.
-/

@[expose] public section

namespace HomogeneousLocalization.Away

section map

variable {ι A B σ τ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  [CommRing B] [SetLike τ B] [AddSubgroupClass τ B] [DecidableEq ι] [AddCommMonoid ι]
  {𝒜 : ι → σ} {ℬ : ι → τ} [GradedRing 𝒜] [GradedRing ℬ]

/-- `HomogeneousLocalization.Away.map` is compatible with the canonical ring homomorphisms
from the degree-zero subrings. -/
lemma map_comp_fromZeroRingHom (g : 𝒜 →+*ᵍ ℬ) (s : A) :
    (HomogeneousLocalization.Away.map g s).comp
        (fromZeroRingHom 𝒜 (Submonoid.powers s)) =
      (fromZeroRingHom ℬ (Submonoid.powers (g s))).comp g.gradeZeroRingHom := by
  ext a
  simp [fromZeroRingHom, HomogeneousLocalization.Away.map, HomogeneousLocalization.map_mk,
    HomogeneousLocalization.val_mk]

/-- If `g : 𝒜 →+*ᵍ ℬ` is surjective, so is the induced map `(A_s)₀ → (B_{g s})₀` on the
degree-zero parts of the localizations away from a homogeneous element `s`.

Every element of `(B_{g s})₀` is a fraction `b / (g s) ^ n` with `b` homogeneous of degree
`n • d`, and `b` lifts to a homogeneous element of `𝒜 (n • d)` by
`GradedRingHom.exists_mem_of_surjective`. -/
theorem map_surjective (g : 𝒜 →+*ᵍ ℬ) (hg : Function.Surjective g) {d : ι} {s : A}
    (hs : s ∈ 𝒜 d) : Function.Surjective (HomogeneousLocalization.Away.map g s) := by
  intro z
  obtain ⟨n, b, hb, rfl⟩ := Away.mk_surjective ℬ (g.map_mem hs) z
  obtain ⟨a, ha, rfl⟩ := GradedRingHom.exists_mem_of_surjective hg hb
  exact ⟨Away.mk 𝒜 hs n a ha, by rw [Away.map_mk]⟩

end map

section lift

variable {ι A R R' σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  [DecidableEq ι] [AddCommMonoid ι] [CommRing R] [CommRing R']
  (𝒜 : ι → σ) [GradedRing 𝒜] {f : A}

/-- Given a ring homomorphism `φ : A →+* R` such that `φ f` is a unit, this is the induced
ring homomorphism from the degree zero part `(A_f)₀` of the localization of `A` away from `f`
to `R`, sending the fraction `a / f ^ n` to `φ a * (φ f)⁻¹ ^ n`. -/
noncomputable def lift (φ : A →+* R) (hφ : IsUnit (φ f)) : Away 𝒜 f →+* R :=
  (IsLocalization.Away.lift (S := Localization.Away f) f hφ).comp
    (algebraMap (Away 𝒜 f) (Localization.Away f))

lemma lift_apply (φ : A →+* R) (hφ : IsUnit (φ f)) (a : Away 𝒜 f) :
    lift 𝒜 φ hφ a = IsLocalization.Away.lift (S := Localization.Away f) f hφ a.val :=
  rfl

@[simp]
lemma lift_mk (φ : A →+* R) (hφ : IsUnit (φ f)) {d : ι} (hf : f ∈ 𝒜 d) (n : ℕ) (a : A)
    (ha : a ∈ 𝒜 (n • d)) :
    lift 𝒜 φ hφ (Away.mk 𝒜 hf n a ha) = φ a * (↑hφ.unit⁻¹ : R) ^ n := by
  rw [lift_apply, Away.val_mk]
  exact Localization.awayLift_mk φ f a _ hφ.mul_val_inv n

/-- Two ring homomorphisms out of `(A_f)₀` agree as soon as they agree on all fractions
`a / f ^ n`. -/
lemma ringHom_ext {d : ι} (hf : f ∈ 𝒜 d) {j k : Away 𝒜 f →+* R}
    (h : ∀ (n : ℕ) (a : A) (ha : a ∈ 𝒜 (n • d)), j (Away.mk 𝒜 hf n a ha) =
      k (Away.mk 𝒜 hf n a ha)) : j = k := by
  ext x
  obtain ⟨n, a, ha, rfl⟩ := Away.mk_surjective 𝒜 hf x
  exact h n a ha

lemma lift_congr {φ ψ : A →+* R} (hφ : IsUnit (φ f)) (hψ : IsUnit (ψ f)) (h : φ = ψ) :
    lift 𝒜 φ hφ = lift 𝒜 ψ hψ := by
  subst h; rfl

/-- `HomogeneousLocalization.Away.lift` is compatible with postcomposition. -/
lemma comp_lift (φ : A →+* R) (hφ : IsUnit (φ f)) (α : R →+* R') :
    α.comp (lift 𝒜 φ hφ) = lift 𝒜 (α.comp φ) (hφ.map α) := by
  rw [lift, lift, ← RingHom.comp_assoc]
  congr 1
  refine IsLocalization.ringHom_ext (Submonoid.powers f) ?_
  rw [RingHom.comp_assoc, IsLocalization.Away.lift_comp, IsLocalization.Away.lift_comp]

end lift

section twist

variable {A R σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A] [CommRing R]
  (𝒜 : ℕ → σ) [GradedRing 𝒜] {f : A}

/-- Rescaling a ring homomorphism `φ : A →+* R` on the degree `n` part of `A` by the `n`-th
power of a fixed unit `u : Rˣ` does not change the induced map on the degree zero part of the
localization away from a homogeneous element. -/
lemma lift_eq_lift_of_eq_unit_pow_mul (u : Rˣ) {d : ℕ} (hf : f ∈ 𝒜 d) (φ ψ : A →+* R)
    (hφ : IsUnit (φ f)) (hψ : IsUnit (ψ f))
    (h : ∀ (n : ℕ) (a : A), a ∈ 𝒜 n → ψ a = (u : R) ^ n * φ a) :
    lift 𝒜 ψ hψ = lift 𝒜 φ hφ := by
  refine ringHom_ext 𝒜 hf fun n a ha ↦ ?_
  have hψu : hψ.unit = u ^ d * hφ.unit := by
    ext
    rw [Units.val_mul, IsUnit.unit_spec, Units.val_pow_eq_pow_val, IsUnit.unit_spec, h d f hf]
  have hu : ((u : R)) ^ (n * d) * (↑u⁻¹ : R) ^ (n * d) = 1 := by
    rw [← mul_pow, u.mul_inv, one_pow]
  rw [lift_mk, lift_mk, h _ a ha, hψu, mul_inv_rev, Units.val_mul, ← inv_pow,
    Units.val_pow_eq_pow_val, mul_pow, smul_eq_mul, ← pow_mul, mul_comm d n]
  rw [show ((u : R)) ^ (n * d) * φ a * ((↑hφ.unit⁻¹ : R) ^ n * (↑u⁻¹ : R) ^ (n * d)) =
    (((u : R)) ^ (n * d) * (↑u⁻¹ : R) ^ (n * d)) * (φ a * (↑hφ.unit⁻¹ : R) ^ n) from by ring,
    hu, one_mul]

end twist

end HomogeneousLocalization.Away

namespace HomogeneousLocalization

section Algebra

variable {ι R A : Type*} [CommRing R] [CommRing A] [Algebra R A] [AddCommMonoid ι]
  [DecidableEq ι] (𝒜 : ι → Submodule R A) [GradedAlgebra 𝒜] (x : Submonoid A)

@[simp]
lemma val_fromZeroRingHom (a : 𝒜 0) :
    (fromZeroRingHom 𝒜 x a).val = algebraMap A (Localization x) (a : A) := by
  simp only [fromZeroRingHom, ← Localization.mk_one_eq_algebraMap]
  rfl

/-- If `A` is a graded `R`-algebra, its homogeneous localization at a submonoid of `A` is an
`R`-algebra, via the degree-zero part `𝒜 0`. -/
instance : Algebra R (HomogeneousLocalization 𝒜 x) where
  algebraMap := (fromZeroRingHom 𝒜 x).comp (algebraMap R (𝒜 0))
  smul := (· • ·)
  commutes' _ _ := mul_comm _ _
  smul_def' r z := by
    obtain ⟨c, rfl⟩ := mk_surjective z
    apply val_injective
    simp [val_smul, Algebra.smul_def, IsScalarTower.algebraMap_apply R A (Localization x)]

lemma algebraMap_eq' :
    algebraMap R (HomogeneousLocalization 𝒜 x) =
      (fromZeroRingHom 𝒜 x).comp (algebraMap R (𝒜 0)) :=
  rfl

@[simp]
lemma val_algebraMap (r : R) :
    (algebraMap R (HomogeneousLocalization 𝒜 x) r).val = algebraMap R (Localization x) r := by
  rw [algebraMap_eq']
  simp [IsScalarTower.algebraMap_apply R A (Localization x)]

instance : IsScalarTower R (HomogeneousLocalization 𝒜 x) (Localization x) :=
  .of_algebraMap_eq fun r ↦ (val_algebraMap 𝒜 x r).symm

end Algebra

section AtPrime

variable {ι σ A : Type*} [AddCommMonoid ι] [DecidableEq ι] [CommRing A] [SetLike σ A]
  [AddSubgroupClass σ A] {𝒜 : ι → σ} [GradedRing 𝒜] (𝔭 : Ideal A) [𝔭.IsPrime]

/-- A fraction `a / f` in the homogeneous localization of `A` at a homogeneous prime ideal `𝔭`
is a unit if and only if its numerator avoids `𝔭`. -/
theorem isUnit_mk_iff (y : NumDenSameDeg 𝒜 𝔭.primeCompl) :
    IsUnit (mk y : AtPrime 𝒜 𝔭) ↔ (y.num : A) ∉ 𝔭 := by
  rw [← isUnit_iff_isUnit_val, val_mk, Localization.mk_eq_mk'_apply,
    IsLocalization.AtPrime.isUnit_mk'_iff]
  exact Iff.rfl

end AtPrime

end HomogeneousLocalization
