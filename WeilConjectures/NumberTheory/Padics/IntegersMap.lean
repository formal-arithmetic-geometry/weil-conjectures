/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Filtration
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import WeilConjectures.NumberTheory.Padics.Extension
public import WeilConjectures.RingTheory.FrobeniusForm

/-!
# The inclusion of rings of integers `𝒪_E ⟶ 𝒪_L`

Let `E ⊆ L` be extensions of `ℚ_ℓ` inside `ℚ̄_ℓ`. This file defines the inclusion
`𝒪_E ⟶ 𝒪_L` of their rings of integers (`PadicAlgCl.integersMap`) and its copy between the
universe `u + 1` copies `Shrink 𝒪_E ⟶ Shrink 𝒪_L` (`PadicAlgCl.integersShrinkMap`).

## Main results

- `PadicAlgCl.integersMap_finite`, `PadicAlgCl.integersShrinkMap_finite`: if `E` and `L` are
  finite over `ℚ_ℓ`, then `𝒪_L` is a finite `𝒪_E`-module.
- `PadicAlgCl.exists_basis_frobeniusForm_integersShrinkMap`: moreover `𝒪_L` is free over `𝒪_E`
  and has a Frobenius form, so that extension and coextension of scalars along `𝒪_E ⟶ 𝒪_L`
  agree.
- `PadicAlgCl.exists_dvd_pow_of_mem_maximalIdealShrink`: every nonzero element of `𝒪_L` divides
  a power of every element of the maximal ideal of `𝒪_L`.

## Proof of finiteness

The coordinates in an `E`-basis of `L` are continuous linear forms on the finite-dimensional
normed space `L` over the complete field `E`, hence bounded on the unit ball `𝒪_L`. So some
power `ℓⁿ` carries all coordinates of elements of `𝒪_L` into `𝒪_E`, which embeds `𝒪_L` into
`𝒪_Eᵈ`; as `𝒪_E` is noetherian, `𝒪_L` is a finite `𝒪_E`-module.
-/

@[expose] public section

universe w u

namespace PadicAlgCl

variable (l : ℕ) [Fact l.Prime] (E L : Type w) [Field E] [Field L]
  [Algebra E (PadicAlgCl l)] [Algebra L (PadicAlgCl l)] [Algebra E L]
  [IsScalarTower E L (PadicAlgCl l)]

/-- The inclusion `𝒪_E ⟶ 𝒪_L` of rings of integers induced by an embedding `E ⟶ L` over
`ℚ̄_ℓ`. -/
noncomputable def integersMap : integers l E →+* integers l L :=
  (algebraMap E L).restrict (integers l E) (integers l L) fun x hx ↦ by
    rw [mem_integers_iff, ← IsScalarTower.algebraMap_apply]
    exact hx

lemma integersMap_injective : Function.Injective (integersMap l E L) := fun _ _ h ↦
  Subtype.ext ((algebraMap E L).injective (congrArg Subtype.val h))

section Shrink

variable [Small.{u + 1} E] [Small.{u + 1} L]

/-- The inclusion `𝒪_E ⟶ 𝒪_L`, between the universe `u + 1` copies of the rings of integers. -/
noncomputable def integersShrinkMap :
    Shrink.{u + 1} (integers l E) →+* Shrink.{u + 1} (integers l L) :=
  (shrinkRingEquiv l L).toRingHom.comp
    ((integersMap l E L).comp (shrinkRingEquiv l E).symm.toRingHom)

lemma integersShrinkMap_injective : Function.Injective (integersShrinkMap.{w, u} l E L) :=
  (shrinkRingEquiv l L).injective.comp
    ((integersMap_injective l E L).comp (shrinkRingEquiv l E).symm.injective)

/-- The inclusion `𝒪_E ⟶ 𝒪_L` carries nonzerodivisors to nonzerodivisors. -/
lemma integersShrinkMap_mem_nonZeroDivisors {x : Shrink.{u + 1} (integers l E)}
    (hx : x ∈ nonZeroDivisors _) : integersShrinkMap l E L x ∈ nonZeroDivisors _ :=
  mem_nonZeroDivisors_of_ne_zero fun h ↦ nonZeroDivisors.ne_zero hx
    (integersShrinkMap_injective l E L (h.trans (map_zero _).symm))

end Shrink

section Finite

variable [Algebra ℚ_[l] E] [IsScalarTower ℚ_[l] E (PadicAlgCl l)] [FiniteDimensional ℚ_[l] E]
  [Algebra ℚ_[l] L] [IsScalarTower ℚ_[l] L (PadicAlgCl l)] [FiniteDimensional ℚ_[l] L]

/-- If `E ⊆ L` are finite extensions of `ℚ_ℓ` inside `ℚ̄_ℓ`, then `𝒪_L` is a finite
`𝒪_E`-module. -/
theorem integersMap_finite : (integersMap l E L).Finite := by
  let := (integersMap l E L).toAlgebra
  let p : E := algebraMap ℚ_[l] E l
  have hp : ‖algebraMap E (PadicAlgCl l) p‖ = (l : ℝ)⁻¹ := by
    rw [← IsScalarTower.algebraMap_apply, PadicAlgCl.norm_extends, Padic.norm_p]
  have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hp0 : p ≠ 0 := by
    rw [ne_eq, map_eq_zero_iff _ (algebraMap ℚ_[l] E).injective, Nat.cast_eq_zero]
    exact (Fact.out : l.Prime).ne_zero
  let : NontriviallyNormedField E :=
    { normedFieldOfAlgebra l E with
      non_trivial := ⟨p⁻¹, by
        change 1 < ‖algebraMap E (PadicAlgCl l) p⁻¹‖
        rw [map_inv₀, norm_inv, hp, inv_inv]
        exact hl⟩ }
  let := normedFieldOfAlgebra l L
  have := completeSpace_ofAlgebra l E
  let : NormedSpace E L :=
    { norm_smul_le c x := by
        change ‖algebraMap L (PadicAlgCl l) (c • x)‖ ≤
          ‖algebraMap E (PadicAlgCl l) c‖ * ‖algebraMap L (PadicAlgCl l) x‖
        rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply, norm_mul] }
  have : IsScalarTower ℚ_[l] E L := IsScalarTower.of_algebraMap_eq fun q ↦
    (algebraMap L (PadicAlgCl l)).injective (by
      rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply,
        ← IsScalarTower.algebraMap_apply])
  have : FiniteDimensional E L := FiniteDimensional.right ℚ_[l] E L
  let b := Module.finBasis E L
  -- a uniform bound for the coordinates on the unit ball
  let C : ℝ := ∑ i, ‖LinearMap.toContinuousLinearMap (b.coord i)‖
  have hC0 : 0 ≤ C := Finset.sum_nonneg fun _ _ ↦ norm_nonneg _
  have hC (i) (x : L) (hx : ‖x‖ ≤ 1) : ‖b.coord i x‖ ≤ C := by
    calc ‖b.coord i x‖ = ‖LinearMap.toContinuousLinearMap (b.coord i) x‖ := rfl
      _ ≤ ‖LinearMap.toContinuousLinearMap (b.coord i)‖ * ‖x‖ :=
        (LinearMap.toContinuousLinearMap (b.coord i)).le_opNorm x
      _ ≤ ‖LinearMap.toContinuousLinearMap (b.coord i)‖ :=
        mul_le_of_le_one_right (norm_nonneg _) hx
      _ ≤ C := Finset.single_le_sum (f := fun i ↦ ‖LinearMap.toContinuousLinearMap (b.coord i)‖)
        (fun _ _ ↦ norm_nonneg _) (Finset.mem_univ i)
  -- a power of `ℓ` making the coordinates integral
  obtain ⟨n, hn⟩ : ∃ n : ℕ, ((l : ℝ)⁻¹) ^ n * C ≤ 1 := by
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (show (0 : ℝ) < (C + 1)⁻¹ by positivity)
      (inv_lt_one_of_one_lt₀ hl)
    refine ⟨n, ?_⟩
    calc ((l : ℝ)⁻¹) ^ n * C ≤ (C + 1)⁻¹ * C := by gcongr
      _ ≤ 1 := by
        rw [inv_mul_le_iff₀ (by positivity)]
        linarith
  -- the embedding `𝒪_L ⟶ 𝒪_Eᵈ`
  let T : integers l L →ₗ[integers l E] (Fin (Module.finrank E L) → integers l E) :=
    { toFun x i := ⟨p ^ n * b.coord i x, by
        change ‖p ^ n * b.coord i x‖ ≤ 1
        rw [norm_mul, norm_pow]
        change ‖algebraMap E (PadicAlgCl l) p‖ ^ n * _ ≤ 1
        rw [hp]
        exact (mul_le_mul_of_nonneg_left (hC i x x.2) (by positivity)).trans hn⟩
      map_add' x y := funext fun i ↦ Subtype.ext (by
        change p ^ n * b.coord i ((x : L) + y) = p ^ n * b.coord i x + p ^ n * b.coord i y
        rw [map_add, mul_add])
      map_smul' a x := funext fun i ↦ Subtype.ext (by
        change p ^ n * b.coord i (algebraMap E L a * x) = (a : E) * (p ^ n * b.coord i x)
        rw [← Algebra.smul_def, map_smul, smul_eq_mul, mul_left_comm]) }
  have hT : Function.Injective T := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    refine Subtype.ext (b.ext_elem fun i ↦ ?_)
    have := congrArg Subtype.val (congrFun hx i)
    change p ^ n * b.coord i x = 0 at this
    rw [ZeroMemClass.coe_zero, map_zero, Finsupp.zero_apply]
    exact (mul_eq_zero.1 this).resolve_left (pow_ne_zero _ hp0)
  exact Module.Finite.of_injective T hT

variable [Small.{u + 1} E] [Small.{u + 1} L]

/-- If `E ⊆ L` are finite extensions of `ℚ_ℓ` inside `ℚ̄_ℓ`, then `𝒪_L` is a finite
`𝒪_E`-module, for the universe `u + 1` copies of the rings of integers. -/
theorem integersShrinkMap_finite : (integersShrinkMap.{w, u} l E L).Finite :=
  (RingHom.Finite.of_surjective _ (shrinkRingEquiv l L).surjective).comp
    ((integersMap_finite l E L).comp
      (RingHom.Finite.of_surjective _ (shrinkRingEquiv l E).symm.surjective))

/-- If `E ⊆ L` are finite extensions of `ℚ_ℓ` inside `ℚ̄_ℓ`, then `𝒪_L` is a finite free
`𝒪_E`-module (for the universe `u + 1` copies of the rings of integers) with a Frobenius form:
an `𝒪_E`-linear form `φ` on `𝒪_L` such that every `𝒪_E`-linear form on `𝒪_L` is `φ(s * -)` for a
unique `s ∈ 𝒪_L`. -/
theorem exists_basis_frobeniusForm_integersShrinkMap :
    letI := (integersShrinkMap.{w, u} l E L).toAlgebra
    ∃ (n : ℕ) (_ : Module.Basis (Fin n) (Shrink.{u + 1} (integers l E))
        (Shrink.{u + 1} (integers l L)))
      (φ : Shrink.{u + 1} (integers l L) →ₗ[Shrink.{u + 1} (integers l E)]
        Shrink.{u + 1} (integers l E)),
      Function.Bijective fun s ↦ φ ∘ₗ LinearMap.mulLeft _ s := by
  let := (integersShrinkMap.{w, u} l E L).toAlgebra
  have : IsPrincipalIdealRing (Shrink.{u + 1} (integers l E)) :=
    IsPrincipalIdealRing.of_surjective (shrinkRingEquiv l E).toRingHom
      (shrinkRingEquiv l E).surjective
  have : IsPrincipalIdealRing (Shrink.{u + 1} (integers l L)) :=
    IsPrincipalIdealRing.of_surjective (shrinkRingEquiv l L).toRingHom
      (shrinkRingEquiv l L).surjective
  have : Module.Finite (Shrink.{u + 1} (integers l E)) (Shrink.{u + 1} (integers l L)) :=
    integersShrinkMap_finite l E L
  have : FaithfulSMul (Shrink.{u + 1} (integers l E)) (Shrink.{u + 1} (integers l L)) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (integersShrinkMap_injective l E L)
  obtain ⟨φ, hφ⟩ := Module.exists_bijective_comp_mulLeft (Shrink.{u + 1} (integers l E))
    (Shrink.{u + 1} (integers l L))
  exact ⟨_, Module.finBasis _ _, φ, hφ⟩

end Finite

section Divisibility

variable {l} {L}

/-- In the ring of integers of a finite extension of `ℚ_ℓ`, a nonzero element divides a power of
every element of the maximal ideal. -/
lemma exists_dvd_pow_of_mem_maximalIdeal [Algebra ℚ_[l] L] [IsScalarTower ℚ_[l] L (PadicAlgCl l)]
    [FiniteDimensional ℚ_[l] L] {x y : integers l L} (hx : x ≠ 0)
    (hy : y ∈ IsLocalRing.maximalIdeal (integers l L)) : ∃ k : ℕ, x ∣ y ^ k := by
  by_contra! h
  refine hx ((Submodule.mem_bot (integers l L)).1 ?_)
  rw [← Ideal.iInf_pow_eq_bot_of_isLocalRing _ (IsLocalRing.maximalIdeal.isMaximal _).ne_top]
  refine Submodule.mem_iInf _ |>.2 fun k ↦ ?_
  obtain ⟨c, hc⟩ := (ValuationRing.dvd_total x (y ^ k)).resolve_left (h k)
  rw [hc]
  exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hy k)

variable [Small.{u + 1} L]

/-- In the universe `u + 1` copy of the ring of integers of a finite extension of `ℚ_ℓ`, a nonzero
element divides a power of every element of the maximal ideal. -/
lemma exists_dvd_pow_of_mem_maximalIdealShrink [Algebra ℚ_[l] L]
    [IsScalarTower ℚ_[l] L (PadicAlgCl l)] [FiniteDimensional ℚ_[l] L]
    {x y : Shrink.{u + 1} (integers l L)} (hx : x ≠ 0) (hy : y ∈ maximalIdealShrink l L) :
    ∃ k : ℕ, x ∣ y ^ k := by
  let e := shrinkRingEquiv.{w, u} l L
  have hy' : e.symm y ∈ IsLocalRing.maximalIdeal (integers l L) := by
    rw [maximalIdealShrink, Ideal.mem_map_of_equiv] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    rwa [RingEquiv.symm_apply_apply]
  obtain ⟨k, hk⟩ := exists_dvd_pow_of_mem_maximalIdeal (x := e.symm x)
    (by simpa using hx) hy'
  refine ⟨k, ?_⟩
  simpa [map_pow] using map_dvd e hk

end Divisibility

end PadicAlgCl
