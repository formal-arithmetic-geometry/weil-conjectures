/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
public import WeilConjectures.Mathlib.RingTheory.GradedAlgebra.RingHom
public import WeilConjectures.Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Homogeneous localization: functoriality, and the standard charts of a polynomial ring

We show that `HomogeneousLocalization.Away.map` is compatible with the canonical ring
homomorphisms from the degree-zero subrings, and that it is surjective as soon as the
graded ring homomorphism it is built from is.

For the total-degree grading on `MvPolynomial σ R`, we identify the homogeneous localization
away from a variable `X i` with the polynomial ring in the remaining variables. Geometrically
this is the standard chart `𝔸^{σ ∖ {i}} ≅ D₊(X i) ⊆ ℙ^σ` of projective space.

## Main definitions

- `MvPolynomial.awayXEquiv` — the ring isomorphism
  `(R[X]_{X i})₀ ≃+* MvPolynomial {j // j ≠ i} R`, sending the fraction `a / (X i) ^ n` with
  `a` homogeneous of degree `n` to its dehomogenization `a(X i = 1)`.
-/

@[expose] public section

namespace HomogeneousLocalization.Away

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

end HomogeneousLocalization.Away

namespace MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

open HomogeneousLocalization

variable {σ R : Type*} [CommRing R] (i : σ)

/-- The polynomial ring in the variables `j ≠ i` maps to the homogeneous localization of
`R[X]` away from `X i`, by `X j ↦ X j / X i`. This is an isomorphism, see
`MvPolynomial.awayXEquiv`. -/
noncomputable def toAwayX :
    MvPolynomial {j // j ≠ i} R →+* Away (homogeneousSubmodule σ R) (X i) :=
  eval₂Hom ((fromZeroRingHom _ _).comp (homogeneousSubmoduleZeroEquiv σ R).toRingHom)
    fun j ↦ Away.mk _ (X_mem_homogeneousSubmodule i) 1 (X j.1)
      (by simpa using X_mem_homogeneousSubmodule (R := R) j.1)

lemma toAwayX_C (r : R) :
    toAwayX i (C r) = fromZeroRingHom _ _ (homogeneousSubmoduleZeroEquiv σ R r) := by
  simp [toAwayX]

lemma toAwayX_X (j : {j // j ≠ i}) :
    toAwayX i (X j) = Away.mk (homogeneousSubmodule σ R) (X_mem_homogeneousSubmodule i) 1 (X j.1)
      (by simpa using X_mem_homogeneousSubmodule (R := R) j.1) := by
  simp [toAwayX]

lemma isUnit_dehomogenize_of_mem_powers (y : Submonoid.powers (X i : MvPolynomial σ R)) :
    IsUnit (dehomogenize i y.1) := by
  obtain ⟨y, k, rfl⟩ := y
  simp

/-- Dehomogenization of a fraction: the ring homomorphism sending `a / (X i) ^ n` to
`a (X i = 1)`. It is inverse to `MvPolynomial.toAwayX`, see `MvPolynomial.awayXEquiv`. -/
noncomputable def awayXDehomogenize :
    Away (homogeneousSubmodule σ R) (X i) →+* MvPolynomial {j // j ≠ i} R :=
  (IsLocalization.lift (M := Submonoid.powers (X i : MvPolynomial σ R))
      (S := Localization.Away (X i : MvPolynomial σ R)) (g := dehomogenize (R := R) i)
      (isUnit_dehomogenize_of_mem_powers i)).comp
    (algebraMap (Away (homogeneousSubmodule σ R) (X i))
      (Localization.Away (X i : MvPolynomial σ R)))

lemma val_fromZeroRingHom (f : homogeneousSubmodule σ R 0) :
    (fromZeroRingHom (homogeneousSubmodule σ R)
        (Submonoid.powers (X i : MvPolynomial σ R)) f).val =
      algebraMap (MvPolynomial σ R) (Localization.Away (X i : MvPolynomial σ R)) f.1 := by
  rw [← Localization.mk_one_eq_algebraMap]
  rfl

@[simp]
lemma awayXDehomogenize_mk (n : ℕ) (a : MvPolynomial σ R)
    (ha : a ∈ homogeneousSubmodule σ R (n • 1)) :
    awayXDehomogenize i (Away.mk _ (X_mem_homogeneousSubmodule i) n a ha) =
      dehomogenize i a := by
  have key : (Localization.mk a ⟨(X i : MvPolynomial σ R) ^ n, ⟨n, rfl⟩⟩ :
      Localization.Away (X i : MvPolynomial σ R)) *
        algebraMap _ _ ((X i : MvPolynomial σ R) ^ n) = algebraMap _ _ a := by
    rw [Localization.mk_eq_mk', IsLocalization.mk'_spec]
  simp only [awayXDehomogenize, RingHom.comp_apply, HomogeneousLocalization.algebraMap_apply,
    Away.val_mk]
  have := congrArg (IsLocalization.lift (M := Submonoid.powers (X i : MvPolynomial σ R))
    (S := Localization.Away (X i : MvPolynomial σ R)) (g := dehomogenize (R := R) i)
    (isUnit_dehomogenize_of_mem_powers i)) key
  rw [map_mul, IsLocalization.lift_eq, IsLocalization.lift_eq] at this
  simpa using this

lemma awayXDehomogenize_fromZeroRingHom (f : homogeneousSubmodule σ R 0) :
    awayXDehomogenize i (fromZeroRingHom _ _ f) = dehomogenize i f.1 := by
  simp only [awayXDehomogenize, RingHom.comp_apply, HomogeneousLocalization.algebraMap_apply,
    val_fromZeroRingHom, IsLocalization.lift_eq]

lemma awayXDehomogenize_toAwayX (p : MvPolynomial {j // j ≠ i} R) :
    awayXDehomogenize i (toAwayX i p) = p := by
  induction p using MvPolynomial.induction_on with
  | C r => rw [toAwayX_C, awayXDehomogenize_fromZeroRingHom]; simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p j hp => simp [hp, toAwayX_X]

/-- `1 / X i` in the localization of `R[X]` away from `X i`. -/
private noncomputable abbrev invX : Localization.Away (X i : MvPolynomial σ R) :=
  Localization.mk 1 ⟨X i, ⟨1, pow_one _⟩⟩

private lemma val_comp_toAwayX_comp_dehomogenize :
    (algebraMap (Away (homogeneousSubmodule σ R) (X i))
        (Localization.Away (X i : MvPolynomial σ R))).comp
      ((toAwayX i).comp (dehomogenize i)) =
      eval₂Hom ((algebraMap (MvPolynomial σ R)
          (Localization.Away (X i : MvPolynomial σ R))).comp C)
        (fun j ↦ invX (R := R) i *
          algebraMap (MvPolynomial σ R) (Localization.Away (X i : MvPolynomial σ R)) (X j)) := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simp only [RingHom.comp_apply, dehomogenize_C, toAwayX_C, coe_eval₂Hom, eval₂_C]
    rw [HomogeneousLocalization.algebraMap_apply, val_fromZeroRingHom,
      coe_homogeneousSubmoduleZeroEquiv]
  · intro j
    simp only [RingHom.comp_apply, coe_eval₂Hom, eval₂_X]
    by_cases h : j = i
    · subst h
      rw [dehomogenize_X_self, map_one, map_one, invX,
        ← Localization.mk_one_eq_algebraMap, Localization.mk_mul, one_mul, mul_one]
      exact (Localization.mk_self_mk (S := Submonoid.powers (X j : MvPolynomial σ R))
        _ ⟨1, pow_one _⟩).symm
    · rw [dehomogenize_X_of_ne i ⟨j, h⟩, toAwayX_X, HomogeneousLocalization.algebraMap_apply,
        Away.val_mk, invX, ← Localization.mk_one_eq_algebraMap, Localization.mk_mul, one_mul,
        mul_one]
      simp

private lemma eval₂Hom_algebraMap_eq :
    eval₂Hom ((algebraMap (MvPolynomial σ R)
          (Localization.Away (X i : MvPolynomial σ R))).comp C)
        (fun j ↦ algebraMap (MvPolynomial σ R)
          (Localization.Away (X i : MvPolynomial σ R)) (X j)) =
      algebraMap (MvPolynomial σ R) (Localization.Away (X i : MvPolynomial σ R)) := by
  apply MvPolynomial.ringHom_ext <;> simp

/-- Dehomogenizing a homogeneous polynomial `a` of degree `n` and rehomogenizing gives back
the fraction `a / (X i) ^ n`. -/
lemma toAwayX_dehomogenize {n : ℕ} (a : MvPolynomial σ R)
    (ha : a ∈ homogeneousSubmodule σ R (n • 1)) :
    toAwayX i (dehomogenize i a) =
      Away.mk (homogeneousSubmodule σ R) (X_mem_homogeneousSubmodule i) n a ha := by
  have hh : a.IsHomogeneous n := by
    simpa using (mem_homogeneousSubmodule _ _).mp ha
  apply HomogeneousLocalization.val_injective
  have h1 := RingHom.congr_fun (val_comp_toAwayX_comp_dehomogenize i) a
  rw [RingHom.comp_apply, RingHom.comp_apply, HomogeneousLocalization.algebraMap_apply] at h1
  rw [h1, coe_eval₂Hom, hh.eval₂_mul_left, ← coe_eval₂Hom, eval₂Hom_algebraMap_eq,
    Away.val_mk, invX, Localization.mk_pow, one_pow, ← Localization.mk_one_eq_algebraMap,
    Localization.mk_mul, one_mul, mul_one]
  congr 1

lemma toAwayX_surjective : Function.Surjective (toAwayX (R := R) i) := by
  intro z
  obtain ⟨n, a, ha, rfl⟩ := Away.mk_surjective (homogeneousSubmodule σ R)
    (X_mem_homogeneousSubmodule i) z
  exact ⟨dehomogenize i a, toAwayX_dehomogenize i a ha⟩

lemma toAwayX_awayXDehomogenize (z : Away (homogeneousSubmodule σ R) (X i)) :
    toAwayX i (awayXDehomogenize i z) = z := by
  obtain ⟨p, rfl⟩ := toAwayX_surjective i z
  rw [awayXDehomogenize_toAwayX]

/-- **The standard chart of projective space**: the degree-zero part of the localization of
`R[X]` away from the variable `X i` is the polynomial ring in the remaining variables, by
dehomogenization `a / (X i) ^ n ↦ a (X i = 1)`. -/
noncomputable def awayXEquiv :
    Away (homogeneousSubmodule σ R) (X i) ≃+* MvPolynomial {j // j ≠ i} R where
  toFun := awayXDehomogenize i
  invFun := toAwayX i
  left_inv := toAwayX_awayXDehomogenize i
  right_inv := awayXDehomogenize_toAwayX i
  map_mul' := map_mul _
  map_add' := map_add _

@[simp]
lemma awayXEquiv_apply (z : Away (homogeneousSubmodule σ R) (X i)) :
    awayXEquiv i z = awayXDehomogenize i z :=
  rfl

@[simp]
lemma awayXEquiv_symm_apply (p : MvPolynomial {j // j ≠ i} R) :
    (awayXEquiv i).symm p = toAwayX i p :=
  rfl

end MvPolynomial
