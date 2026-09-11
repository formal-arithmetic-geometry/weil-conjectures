/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
public import WeilConjectures.Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Homogeneous localization of a polynomial ring at a variable

For the total-degree grading `𝒜 = MvPolynomial.homogeneousSubmodule σ A` of the polynomial ring
`A[X] = MvPolynomial σ A`, we identify the degree-zero part of the homogeneous localization of
`A[X]` away from a variable `X a` with the polynomial ring in the fractions `X b / X a`,
`b ≠ a`, and its analogue away from a product `X a * X b` of two variables with a localization
of the latter. Geometrically these are the coordinate ring of a standard chart of the
projective space `Proj A[X]` and the coordinate ring of the overlap of two standard charts, but
everything here is pure algebra: no schemes occur.

The identification is by *dehomogenization*: a fraction `p / (X a) ^ n` with `p` homogeneous of
degree `n` is sent to `p` with `1` substituted for `X a`.

## Main definitions

- `MvPolynomial.dehomogenize` — the `A`-algebra map `A[X] → A[X_b : b ≠ a]` substituting `1`
  for `X a`, and `MvPolynomial.dehomogenizeAway`, its extension to the localization
  `A[X]_{X a}`.
- `MvPolynomial.toAwayX` and `MvPolynomial.fromAwayX` — the mutually inverse `A`-algebra maps
  between `A[X_b : b ≠ a]` and the degree-zero part of the homogeneous localization of `A[X]`
  away from `X a`.
- `MvPolynomial.toAwayXMul` — the transition map from the chart ring at `a` to the overlap ring
  at `a` and `b`, i.e. `HomogeneousLocalization.awayMap` read through `toAwayX`.

## Main results

- `MvPolynomial.awayXAlgEquiv` — the `A`-algebra isomorphism
  `HomogeneousLocalization.Away 𝒜 (X a) ≃ₐ[A] MvPolynomial {b // b ≠ a} A` sending the class of
  `X b / X a` to the variable `X b`.
- `MvPolynomial.isLocalization_away_toAwayXMul` and `MvPolynomial.awayXMulRingEquiv` — the
  overlap ring `HomogeneousLocalization.Away 𝒜 (X a * X b)` is the localization of the chart
  ring `MvPolynomial {c // c ≠ a} A` away from the variable `X b`, via the transition map.
- `MvPolynomial.toAwayXMul_X_mul_toAwayXMul_X` — the transition between the charts at `a` and
  at `b` inverts the variable: the images of `X b` and of `X a` in the overlap ring are
  inverse to each other.

## Implementation notes

The total-degree grading is not a global instance in Mathlib, since one may want to grade
`MvPolynomial σ A` by another weight function, so it is enabled locally here.

Surjectivity of `toAwayX` is the computation `p / (X a) ^ n = ∑ ν c_ν ∏_{b ≠ a} (X b / X a) ^ ν b`
for `p = ∑ ν c_ν X^ν` homogeneous of degree `n`. It is carried out in the localization
`A[X]_{X a}`, where it becomes the identity `q * (X a) ^ n = p` for `q` the image of `p` under
the ring map `X i ↦ X i / X a`, and where it is proved monomial by monomial.
-/

@[expose] public section

open HomogeneousLocalization

namespace MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

variable {σ : Type*} (A : Type*) [CommRing A]

section Dehomogenize

open scoped Classical in
/-- Dehomogenization at a variable `X a`: the `A`-algebra map `A[X] → A[X_b : b ≠ a]`
substituting `1` for `X a` and `X b` for `X b`, `b ≠ a`. -/
noncomputable def dehomogenize (a : σ) :
    MvPolynomial σ A →ₐ[A] MvPolynomial {b // b ≠ a} A :=
  aeval fun i ↦ if h : i = a then 1 else X ⟨i, h⟩

variable (a : σ)

@[simp]
lemma dehomogenize_X_self : dehomogenize A a (X a) = 1 := by
  simp [dehomogenize]

@[simp]
lemma dehomogenize_X_of_ne {i : σ} (h : i ≠ a) : dehomogenize A a (X i) = X ⟨i, h⟩ := by
  simp [dehomogenize, dif_neg h]

@[simp]
lemma dehomogenize_X (b : {b // b ≠ a}) : dehomogenize A a (X b.1) = X b :=
  dehomogenize_X_of_ne A a b.2

@[simp]
lemma dehomogenize_C (r : A) : dehomogenize A a (C r) = C r := by
  simp [dehomogenize, algebraMap_eq]

end Dehomogenize

section ChartRing

variable (a : σ)

local notation "𝒜" => MvPolynomial.homogeneousSubmodule σ A

local notation "Aₐ" => Localization.Away (MvPolynomial.X a : MvPolynomial σ A)

local notation "invXₐ" =>
  IsLocalization.Away.invSelf (S := Localization.Away (MvPolynomial.X a : MvPolynomial σ A))
    (MvPolynomial.X a : MvPolynomial σ A)

/-- Auxiliary ring homomorphism `A[X] → A[X]_{X a}` sending every variable `X i` to
`X i / X a`; in particular `X a ↦ 1`. -/
private noncomputable def dehomogenizeHom : MvPolynomial σ A →+* Aₐ :=
  eval₂Hom ((algebraMap (MvPolynomial σ A) Aₐ).comp C)
    fun i ↦ algebraMap (MvPolynomial σ A) Aₐ (X i) * invXₐ

private lemma dehomogenizeHom_C (r : A) :
    dehomogenizeHom A a (C r : MvPolynomial σ A) = algebraMap (MvPolynomial σ A) Aₐ (C r) := by
  simp [dehomogenizeHom]

private lemma dehomogenizeHom_X (i : σ) :
    dehomogenizeHom A a (X i : MvPolynomial σ A) =
      algebraMap (MvPolynomial σ A) Aₐ (X i) * invXₐ := by
  simp [dehomogenizeHom]

/-- Multiplying out denominators: a homogeneous polynomial `p` of degree `n` satisfies
`p / (X a) ^ n * (X a) ^ n = p` in `A[X]_{X a}`. -/
private lemma dehomogenizeHom_mul_pow {p : MvPolynomial σ A} {n : ℕ} (hp : p.IsHomogeneous n) :
    dehomogenizeHom A a p * algebraMap (MvPolynomial σ A) Aₐ (X a) ^ n =
      algebraMap (MvPolynomial σ A) Aₐ p := by
  have key : ∀ (ν : σ →₀ ℕ) (c : A), ν.degree = n →
      dehomogenizeHom A a (monomial ν c) * algebraMap (MvPolynomial σ A) Aₐ (X a) ^ n =
        algebraMap (MvPolynomial σ A) Aₐ (monomial ν c) := by
    intro ν c hν
    simp only [dehomogenizeHom, coe_eval₂Hom, eval₂_C, eval₂_X, RingHom.coe_comp,
      Function.comp_apply, monomial_eq, map_mul, Finsupp.prod, map_prod, map_pow, mul_pow,
      Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, ← Finsupp.degree_apply, hν,
      mul_assoc]
    rw [← mul_pow, mul_comm invXₐ, IsLocalization.Away.mul_invSelf, one_pow, mul_one]
  rw [← support_sum_monomial_coeff p, map_sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun ν hν ↦ key ν _ ?_
  by_contra h
  exact (mem_support_iff.mp hν) (hp.coeff_eq_zero h)

private lemma mk_eq_mul_invSelf_pow (p : MvPolynomial σ A) (n : ℕ)
    (q : Submonoid.powers (X a : MvPolynomial σ A))
    (hq : (q : MvPolynomial σ A) = (X a : MvPolynomial σ A) ^ n) :
    Localization.mk p q = algebraMap (MvPolynomial σ A) Aₐ p * invXₐ ^ n := by
  rw [Localization.mk_eq_mk', eq_comm, IsLocalization.eq_mk'_iff_mul_eq, hq, map_pow, mul_assoc,
    ← mul_pow, mul_comm invXₐ, IsLocalization.Away.mul_invSelf, one_pow, mul_one]

/-- The `A`-algebra homomorphism from the polynomial ring in the variables `X b`, `b ≠ a`, to
the degree-zero homogeneous localization of `A[X]` away from `X a`, sending `X b` to the
fraction `X b / X a`. -/
noncomputable def toAwayX : MvPolynomial {b // b ≠ a} A →ₐ[A] Away 𝒜 (X a) :=
  aeval fun b ↦ Away.mk 𝒜 (isHomogeneous_X A a) 1 (X b.1) (isHomogeneous_X A b.1)

@[simp]
lemma toAwayX_X (b : {b // b ≠ a}) :
    toAwayX A a (X b) =
      Away.mk 𝒜 (isHomogeneous_X A a) 1 (X b.1) (isHomogeneous_X A b.1) := by
  simp [toAwayX]

private lemma val_toAwayX_dehomogenize (p : MvPolynomial σ A) :
    (toAwayX A a (dehomogenize A a p)).val = dehomogenizeHom A a p := by
  have H : (algebraMap (Away 𝒜 (X a)) Aₐ).comp
      ((toAwayX A a).toRingHom.comp (dehomogenize A a).toRingHom) = dehomogenizeHom A a := by
    apply ringHom_ext
    · intro r
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
      simp [dehomogenizeHom_C, HomogeneousLocalization.algebraMap_apply, algHom_C,
        IsScalarTower.algebraMap_apply A (MvPolynomial σ A) Aₐ, algebraMap_eq]
    · intro i
      by_cases h : i = a
      · subst h
        simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
        simp [dehomogenizeHom_X, HomogeneousLocalization.algebraMap_apply]
      · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
        rw [dehomogenizeHom_X,
          show dehomogenize A a (X i) = X ⟨i, h⟩ from by simp [dehomogenize, dif_neg h], toAwayX_X,
          HomogeneousLocalization.algebraMap_apply, Away.val_mk,
          mk_eq_mul_invSelf_pow A a _ 1 _ (by simp), pow_one]
  exact DFunLike.congr_fun H p

lemma toAwayX_dehomogenize (n : ℕ) (p : MvPolynomial σ A) (hp : p ∈ 𝒜 (n • 1)) :
    toAwayX A a (dehomogenize A a p) = Away.mk 𝒜 (isHomogeneous_X A a) n p hp := by
  apply HomogeneousLocalization.val_injective
  rw [val_toAwayX_dehomogenize, Away.val_mk, mk_eq_mul_invSelf_pow A a p n _ rfl]
  calc dehomogenizeHom A a p
      = dehomogenizeHom A a p * (algebraMap (MvPolynomial σ A) Aₐ (X a) * invXₐ) ^ n := by
        rw [IsLocalization.Away.mul_invSelf, one_pow, mul_one]
    _ = dehomogenizeHom A a p * algebraMap (MvPolynomial σ A) Aₐ (X a) ^ n * invXₐ ^ n := by
        rw [mul_pow, mul_assoc]
    _ = algebraMap (MvPolynomial σ A) Aₐ p * invXₐ ^ n := by
        rw [dehomogenizeHom_mul_pow A a (by simpa using hp)]

/-- Dehomogenization at `X a`, extended to the localization `A[X]_{X a}` in which `X a` is
invertible: the `A`-algebra map `A[X]_{X a} → A[X_b : b ≠ a]` substituting `1` for `X a`. -/
noncomputable def dehomogenizeAway : Aₐ →ₐ[A] MvPolynomial {b // b ≠ a} A :=
  IsLocalization.Away.liftAlgHom (X a : MvPolynomial σ A) (f := dehomogenize A a) (by simp)

lemma dehomogenizeAway_algebraMap (p : MvPolynomial σ A) :
    dehomogenizeAway A a (algebraMap (MvPolynomial σ A) Aₐ p) = dehomogenize A a p := by
  simp [dehomogenizeAway, IsLocalization.Away.liftAlgHom_apply]

lemma dehomogenizeAway_invSelf : dehomogenizeAway A a invXₐ = 1 := by
  have H : dehomogenizeAway A a (algebraMap (MvPolynomial σ A) Aₐ (X a)) *
      dehomogenizeAway A a invXₐ = 1 := by
    rw [← map_mul, IsLocalization.Away.mul_invSelf, map_one]
  rwa [dehomogenizeAway_algebraMap, dehomogenize_X_self, one_mul] at H

/-- The `A`-algebra homomorphism from the degree-zero homogeneous localization of `A[X]` away
from `X a` to the polynomial ring in the variables `X b`, `b ≠ a`, given by dehomogenization,
i.e. by substituting `1` for `X a`. -/
noncomputable def fromAwayX : Away 𝒜 (X a) →ₐ[A] MvPolynomial {b // b ≠ a} A :=
  (dehomogenizeAway A a).comp (IsScalarTower.toAlgHom A (Away 𝒜 (X a)) Aₐ)

@[simp]
lemma fromAwayX_mk {n : ℕ} (p : MvPolynomial σ A) (hp : p ∈ 𝒜 (n • 1)) :
    fromAwayX A a (Away.mk 𝒜 (isHomogeneous_X A a) n p hp) = dehomogenize A a p := by
  rw [fromAwayX, AlgHom.comp_apply, IsScalarTower.coe_toAlgHom',
    HomogeneousLocalization.algebraMap_apply, Away.val_mk, mk_eq_mul_invSelf_pow A a p n _ rfl,
    map_mul, map_pow, dehomogenizeAway_algebraMap, dehomogenizeAway_invSelf, one_pow, mul_one]

/-- **The chart rings of `Proj` of a polynomial ring are polynomial rings**: the degree-zero
part of the homogeneous localization of `A[X]` away from the variable `X a` is the polynomial
ring over `A` in the fractions `X b / X a`, `b ≠ a`. -/
noncomputable def awayXAlgEquiv : Away 𝒜 (X a) ≃ₐ[A] MvPolynomial {b // b ≠ a} A :=
  AlgEquiv.ofAlgHom (fromAwayX A a) (toAwayX A a)
    (by ext b; simp)
    (AlgHom.ext fun z ↦ by
      obtain ⟨n, p, hp, rfl⟩ := Away.mk_surjective 𝒜 (isHomogeneous_X A a) z
      simpa using toAwayX_dehomogenize A a n p hp)

@[simp]
lemma awayXAlgEquiv_apply (z : Away 𝒜 (X a)) : awayXAlgEquiv A a z = fromAwayX A a z := rfl

@[simp]
lemma awayXAlgEquiv_symm_apply (q : MvPolynomial {b // b ≠ a} A) :
    (awayXAlgEquiv A a).symm q = toAwayX A a q := rfl

@[simp]
lemma awayXAlgEquiv_mk {n : ℕ} (p : MvPolynomial σ A) (hp : p ∈ 𝒜 (n • 1)) :
    awayXAlgEquiv A a (Away.mk 𝒜 (isHomogeneous_X A a) n p hp) = dehomogenize A a p :=
  fromAwayX_mk A a p hp

@[simp]
lemma awayXAlgEquiv_symm_X (b : {b // b ≠ a}) :
    (awayXAlgEquiv A a).symm (X b) =
      Away.mk 𝒜 (isHomogeneous_X A a) 1 (X b.1) (isHomogeneous_X A b.1) :=
  toAwayX_X A a b

end ChartRing

section Overlap

variable {a b : σ}

local notation "𝒜" => MvPolynomial.homogeneousSubmodule σ A

/-- The transition map from the standard chart at `a` to the overlap of the standard charts at
`a` and `b`, i.e. the map `A[X_c : c ≠ a] → (A[X]_{X a X b})₀` induced by
`HomogeneousLocalization.awayMap`. -/
noncomputable def toAwayXMul (a b : σ) {x : MvPolynomial σ A} (hx : x = X a * X b) :
    MvPolynomial {c // c ≠ a} A →ₐ[A] Away 𝒜 x where
  __ := (HomogeneousLocalization.awayMap 𝒜 (isHomogeneous_X A b) hx).comp (toAwayX A a).toRingHom
  commutes' r := by
    change HomogeneousLocalization.awayMap 𝒜 (isHomogeneous_X A b) hx
      (toAwayX A a (algebraMap A _ r)) = _
    rw [AlgHom.commutes, HomogeneousLocalization.algebraMap_eq', RingHom.comp_apply,
      HomogeneousLocalization.awayMap_fromZeroRingHom, HomogeneousLocalization.algebraMap_eq',
      RingHom.comp_apply]

lemma toAwayXMul_apply {x : MvPolynomial σ A} (hx : x = X a * X b)
    (q : MvPolynomial {c // c ≠ a} A) :
    toAwayXMul A a b hx q =
      HomogeneousLocalization.awayMap 𝒜 (isHomogeneous_X A b) hx (toAwayX A a q) :=
  rfl

private lemma toAwayX_X_eq_isLocalizationElem (hab : b ≠ a) :
    toAwayX A a (X (⟨b, hab⟩ : {c // c ≠ a})) =
      Away.isLocalizationElem (isHomogeneous_X A a) (isHomogeneous_X A b) := by
  rw [toAwayX_X]
  apply HomogeneousLocalization.val_injective
  simp

/-- **The overlap of two standard charts**: the degree-zero part of the homogeneous
localization of `A[X]` away from `X a * X b` is the localization of the chart ring
`A[X_c : c ≠ a]` away from the variable `X b`, along the transition map `toAwayXMul`. -/
theorem isLocalization_away_toAwayXMul (hab : b ≠ a) {x : MvPolynomial σ A}
    (hx : x = X a * X b) :
    letI := (toAwayXMul A a b hx).toRingHom.toAlgebra
    IsLocalization.Away (X (⟨b, hab⟩ : {c // c ≠ a}) : MvPolynomial {c // c ≠ a} A)
      (Away 𝒜 x) := by
  let := (toAwayXMul A a b hx).toRingHom.toAlgebra
  let := (HomogeneousLocalization.awayMap 𝒜 (isHomogeneous_X A b) hx).toAlgebra
  have hXa : (X a : MvPolynomial σ A) ∈ 𝒜 1 := isHomogeneous_X A a
  have hXb : (X b : MvPolynomial σ A) ∈ 𝒜 1 := isHomogeneous_X A b
  have := Away.isLocalization_mul hXa hXb hx one_ne_zero
  refine IsLocalization.of_ringEquiv_left (e := (awayXAlgEquiv A a).symm.toRingEquiv)
    (M₁ := Submonoid.powers (Away.isLocalizationElem hXa hXb)) ?_ fun q ↦ rfl
  rw [Submonoid.map_powers]
  exact congrArg _ (toAwayX_X_eq_isLocalizationElem A hab)

/-- The overlap ring of the standard charts at `a` and `b`, identified with the localization
of the chart ring at `a` away from the variable `X b`. -/
noncomputable def awayXMulRingEquiv (hab : b ≠ a) {x : MvPolynomial σ A} (hx : x = X a * X b) :
    Away 𝒜 x ≃+*
      Localization.Away (X (⟨b, hab⟩ : {c // c ≠ a}) : MvPolynomial {c // c ≠ a} A) :=
  letI := (toAwayXMul A a b hx).toRingHom.toAlgebra
  haveI := isLocalization_away_toAwayXMul A hab hx
  (IsLocalization.algEquiv
    (Submonoid.powers (X (⟨b, hab⟩ : {c // c ≠ a}) : MvPolynomial {c // c ≠ a} A))
    (Away 𝒜 x) _).toRingEquiv

/-- Under the identification of the overlap ring with a localization of the chart ring at `a`,
the transition map `toAwayXMul` is the canonical map to the localization. -/
@[simp]
lemma awayXMulRingEquiv_toAwayXMul (hab : b ≠ a) {x : MvPolynomial σ A} (hx : x = X a * X b)
    (q : MvPolynomial {c // c ≠ a} A) :
    awayXMulRingEquiv A hab hx (toAwayXMul A a b hx q) =
      algebraMap (MvPolynomial {c // c ≠ a} A)
        (Localization.Away (X (⟨b, hab⟩ : {c // c ≠ a}) : MvPolynomial {c // c ≠ a} A)) q := by
  let := (toAwayXMul A a b hx).toRingHom.toAlgebra
  have := isLocalization_away_toAwayXMul A hab hx
  exact (IsLocalization.algEquiv _ _ _).commutes q

/-- **The transition between two standard charts inverts the variable**: on the overlap of the
standard charts at `a` and `b`, the images of the variable `X b` of the chart at `a` and of the
variable `X a` of the chart at `b` are inverse to each other. -/
lemma toAwayXMul_X_mul_toAwayXMul_X (hab : b ≠ a) {x : MvPolynomial σ A} (hx : x = X a * X b) :
    toAwayXMul A a b hx (X ⟨b, hab⟩) *
      toAwayXMul A b a (hx.trans (mul_comm _ _)) (X ⟨a, hab.symm⟩) = 1 := by
  apply HomogeneousLocalization.val_injective
  simp only [toAwayXMul_apply, toAwayX_X, HomogeneousLocalization.awayMap_mk,
    HomogeneousLocalization.val_mul, HomogeneousLocalization.val_one, Away.val_mk,
    Localization.mk_mul]
  rw [← Localization.mk_one, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  exact ⟨1, by simp [hx]; ring⟩

end Overlap

end MvPolynomial
