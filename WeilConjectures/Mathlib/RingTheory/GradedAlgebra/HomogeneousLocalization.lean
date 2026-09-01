/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
public import WeilConjectures.Mathlib.RingTheory.GradedAlgebra.RingHom

/-!
# Homogeneous localization of a graded algebra, `HomogeneousLocalization.Away.map`, and the
arithmetic of `HomogeneousLocalization.Away.mk`

If `A` is an `R`-algebra graded by `R`-submodules `𝒜`, the degree-zero part
`HomogeneousLocalization 𝒜 x` of a localization of `A` is an `R`-algebra, via
`R → 𝒜 0 → HomogeneousLocalization 𝒜 x`.

We also show that `HomogeneousLocalization.Away.map` is compatible with the canonical ring
homomorphisms from the degree-zero subrings, and that it is surjective as soon as the
graded ring homomorphism it is built from is.

Finally, we develop the arithmetic of the fractions `HomogeneousLocalization.Away.mk 𝒜 hf n a ha`,
that is, of `a / f ^ n` in `Away 𝒜 f`: units, products, powers and cancellation, together with the
transition cocycle relating the two charts `Away 𝒜 f` and `Away 𝒜 g` inside `Away 𝒜 (f * g)`.

## Main definitions

- `HomogeneousLocalization.algebra` — the `R`-algebra structure on
  `HomogeneousLocalization 𝒜 x` for a graded `R`-algebra `𝒜`.

## Main results

- `HomogeneousLocalization.Away.map_surjective` — `Away.map` of a surjective graded ring
  homomorphism is surjective.
- `HomogeneousLocalization.Away.mk_one`, `HomogeneousLocalization.Away.mk_self` and
  `HomogeneousLocalization.Away.mk_pow_self` — the fractions `1 / f ^ 0`, `f / f` and
  `f ^ n / f ^ n` are the unit of `Away 𝒜 f`.
- `HomogeneousLocalization.Away.mk_mul` and `HomogeneousLocalization.Away.mk_pow` — products and
  powers of fractions.
- `HomogeneousLocalization.Away.mk_mul_pow_cancel` and
  `HomogeneousLocalization.Away.mk_eq_mk_of_mul_pow_eq` — cancelling a power of `f`, and the
  criterion for two fractions to be equal.
- `HomogeneousLocalization.awayMap_mk_one_eq_mul` — the transition cocycle: inside `Away 𝒜 (f * g)`
  the image of `x / g` is the image of `x / f` times the image of `f / g`.
-/

@[expose] public section

namespace HomogeneousLocalization

variable {ι R A : Type*} [CommRing R] [CommRing A] [Algebra R A] [AddCommMonoid ι]
  [DecidableEq ι] {𝒜 : ι → Submodule R A} [GradedAlgebra 𝒜] (x : Submonoid A)

@[simp]
lemma val_fromZeroRingHom (a : 𝒜 0) :
    (fromZeroRingHom 𝒜 x a).val = Localization.mk (a : A) 1 :=
  rfl

/-- If `A` is a graded `R`-algebra, the degree-zero part of a localization of `A` is an
`R`-algebra, via `R → 𝒜 0 → HomogeneousLocalization 𝒜 x`. -/
instance algebra : Algebra R (HomogeneousLocalization 𝒜 x) :=
  { instSMul x with
    algebraMap := (fromZeroRingHom 𝒜 x).comp (algebraMap R (𝒜 0))
    commutes' := fun _ _ ↦ mul_comm _ _
    smul_def' := fun r z ↦ by
      obtain ⟨z, rfl⟩ := mk_surjective z
      ext
      simp only [← mk_smul, val_mk, RingHom.coe_comp, Function.comp_apply, val_mul,
        val_fromZeroRingHom, NumDenSameDeg.num_smul, NumDenSameDeg.den_smul,
        Localization.mk_mul, one_mul, Algebra.smul_def, SetLike.GradeZero.coe_algebraMap] }

instance : IsScalarTower R (𝒜 0) (HomogeneousLocalization 𝒜 x) :=
  .of_algebraMap_eq' rfl

@[simp]
lemma val_algebraMap (r : R) :
    (algebraMap R (HomogeneousLocalization 𝒜 x) r).val = Localization.mk (algebraMap R A r) 1 :=
  rfl

end HomogeneousLocalization

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

namespace HomogeneousLocalization

section Away

variable {ι σ A : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  [AddCommMonoid ι] [DecidableEq ι] (𝒜 : ι → σ) [GradedRing 𝒜] {d : ι} {f : A}

/-- Two fractions `a / f ^ n` and `b / f ^ m` in `Away 𝒜 f` agree as soon as
`a * f ^ m = b * f ^ n`. -/
lemma Away.mk_eq_mk_of_mul_pow_eq (hf : f ∈ 𝒜 d) {n m : ℕ} {a b : A} (ha : a ∈ 𝒜 (n • d))
    (hb : b ∈ 𝒜 (m • d)) (h : a * f ^ m = b * f ^ n) :
    Away.mk 𝒜 hf n a ha = Away.mk 𝒜 hf m b hb := by
  apply val_injective
  rw [Away.val_mk, Away.val_mk, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  exact ⟨1, by simpa [mul_comm] using h⟩

/-- The fraction `f ^ n / f ^ n` is `1` in `Away 𝒜 f`. -/
@[simp]
lemma Away.mk_pow_self (hf : f ∈ 𝒜 d) (n : ℕ) (h : f ^ n ∈ 𝒜 (n • d)) :
    Away.mk 𝒜 hf n (f ^ n) h = 1 := by
  apply val_injective
  rw [Away.val_mk, val_one]
  exact Localization.mk_self (⟨f ^ n, n, rfl⟩ : Submonoid.powers f)

/-- The fraction `f / f` is `1` in `Away 𝒜 f`. -/
@[simp]
lemma Away.mk_self (hf : f ∈ 𝒜 d) (h : f ∈ 𝒜 (1 • d)) :
    Away.mk 𝒜 hf 1 f h = 1 := by
  simpa using Away.mk_pow_self 𝒜 hf 1 (by simpa using h)

/-- The fraction `1 / f ^ 0` is `1` in `Away 𝒜 f`. -/
@[simp]
lemma Away.mk_one (hf : f ∈ 𝒜 d) (h : (1 : A) ∈ 𝒜 (0 • d)) :
    Away.mk 𝒜 hf 0 1 h = 1 := by
  apply val_injective
  rw [Away.val_mk, val_one]
  simp

/-- Multiplying fractions in `Away 𝒜 f`: `(a / f ^ n) * (b / f ^ m) = (a * b) / f ^ (n + m)`. -/
lemma Away.mk_mul (hf : f ∈ 𝒜 d) (n m : ℕ) (a b : A) (ha : a ∈ 𝒜 (n • d)) (hb : b ∈ 𝒜 (m • d)) :
    Away.mk 𝒜 hf n a ha * Away.mk 𝒜 hf m b hb =
      Away.mk 𝒜 hf (n + m) (a * b) (add_smul n m d ▸ SetLike.mul_mem_graded ha hb) := by
  apply val_injective
  rw [val_mul, Away.val_mk, Away.val_mk, Away.val_mk, Localization.mk_mul]
  congr 1
  exact Subtype.ext (pow_add f n m).symm

/-- Powers of a fraction in `Away 𝒜 f`: `(a / f ^ n) ^ k = a ^ k / f ^ (k * n)`. -/
lemma Away.mk_pow (hf : f ∈ 𝒜 d) (n : ℕ) (a : A) (ha : a ∈ 𝒜 (n • d)) (k : ℕ) :
    (Away.mk 𝒜 hf n a ha) ^ k =
      Away.mk 𝒜 hf (k * n) (a ^ k) (mul_smul k n d ▸ SetLike.pow_mem_graded k ha) := by
  apply val_injective
  rw [val_pow, Away.val_mk, Away.val_mk, Localization.mk_pow]
  congr 1
  exact Subtype.ext (by rw [SubmonoidClass.coe_pow, ← pow_mul, mul_comm])

/-- A common factor `f ^ k` cancels in `Away 𝒜 f`:
`(a * f ^ k) / f ^ (n + k) = a / f ^ n`. -/
lemma Away.mk_mul_pow_cancel (hf : f ∈ 𝒜 d) (n k : ℕ) (a : A) (ha : a ∈ 𝒜 (n • d))
    (h : a * f ^ k ∈ 𝒜 ((n + k) • d)) :
    Away.mk 𝒜 hf (n + k) (a * f ^ k) h = Away.mk 𝒜 hf n a ha :=
  Away.mk_eq_mk_of_mul_pow_eq 𝒜 hf h ha (by ring)

end Away

section Cocycle

variable {ι σ A : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  [AddCommMonoid ι] [DecidableEq ι] (𝒜 : ι → σ) [GradedRing 𝒜] {d : ι} {f g x : A}

/-- The transition cocycle relating the two away-charts `Away 𝒜 f` and `Away 𝒜 g` inside
`Away 𝒜 (f * g)`: the image of `x / g` is the image of `x / f` times the image of `f / g`.

Here `awayMap 𝒜 hg rfl : Away 𝒜 f →+* Away 𝒜 (f * g)` and
`awayMap 𝒜 hf (mul_comm f g) : Away 𝒜 g →+* Away 𝒜 (f * g)` are the two canonical maps into the
overlap. The statement is symmetric in `f` and `g`, so it applies to either chart.

Note that `f`, `g` and `x` are necessarily all of the same degree `d`: the fractions `x / f`,
`x / g` and `f / g` are homogeneous of degree zero only then. -/
lemma awayMap_mk_one_eq_mul (hf : f ∈ 𝒜 d) (hg : g ∈ 𝒜 d) (hx : x ∈ 𝒜 (1 • d)) :
    awayMap 𝒜 hf (mul_comm f g) (Away.mk 𝒜 hg 1 x hx) =
      awayMap 𝒜 hg (rfl : f * g = f * g) (Away.mk 𝒜 hf 1 x hx) *
        awayMap 𝒜 hf (mul_comm f g) (Away.mk 𝒜 hg 1 f (by simpa using hf)) := by
  rw [awayMap_mk, awayMap_mk, awayMap_mk, Away.mk_mul]
  refine Away.mk_eq_mk_of_mul_pow_eq 𝒜 _ _ _ ?_
  ring

end Cocycle

end HomogeneousLocalization
