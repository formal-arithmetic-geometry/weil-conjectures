/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.RingTheory.Flat.EquationalCriterion
public import Mathlib.RingTheory.Ideal.Maps

/-!
# A basis of a square zero ideal, after a flat base change

Let `B` be a commutative ring, let `𝔪` and `I` be ideals of `B` with `𝔪 * I = 0`, and let
`e : ι → B` be a finite family of elements of `I` such that the only relations between the
`e i` are the ones forced by `𝔪`, i.e. such that `∑ i, c i * e i = 0` implies `c i ∈ 𝔪` for
all `i`. If moreover `e` spans `I`, and `B` is local with maximal ideal `𝔪`, this says exactly
that the classes of the `e i` form a basis of `I` as a vector space over the residue field
`B ⧸ 𝔪` — a structure `I` carries because `𝔪 * I = 0`.

For a flat `B`-algebra `R`, we compute the kernel and the image of the `R`-linear map
`σ : (ι → R) →ₗ[R] R`, `r ↦ ∑ i, r i * e i`: the image is the extension `I R` of `I`, and the
kernel is the `ι`-fold product of the extension `𝔪 R` of `𝔪`. In other words, `e` remains a
basis of `I R` over `R ⧸ 𝔪 R` after the base change.

Flatness enters exactly once, through the equational criterion
`Module.Flat.isTrivialRelation_of_sum_smul_eq_zero`: it turns a relation between the `e i` with
coefficients in `R` into relations with coefficients in `B`, which the hypothesis on `e` then
places in `𝔪`. The computation of the image needs no flatness.

## Main results

- `Module.Flat.mem_ideal_map_of_sum_mul_eq_zero`: a relation `∑ i, r i * e i = 0` with
  coefficients `r i` in a flat `B`-algebra `R` has all its coefficients in `𝔪 R`.
- `Module.Flat.ker_linearCombination`: the kernel of `σ` is the `ι`-fold product of `𝔪 R`.
- `Ideal.range_linearCombination_algebraMap`: the image of `σ` is `I R`.
-/

@[expose] public section

variable {B R ι : Type*} [CommRing B] [CommRing R] [Algebra B R] [Fintype ι]
  {𝔪 I : Ideal B} {e : ι → B}

namespace Module.Flat

/-- If `R` is flat over `B` and the only `B`-linear relations between the `e i` have all their
coefficients in the ideal `𝔪`, then the same holds for `R`-linear relations, with coefficients
in the extension `𝔪 R`. This is the only place where flatness is used. -/
theorem mem_ideal_map_of_sum_mul_eq_zero [Module.Flat B R]
    (he : ∀ c : ι → B, ∑ i, c i * e i = 0 → ∀ i, c i ∈ 𝔪)
    {r : ι → R} (hr : ∑ i, r i * algebraMap B R (e i) = 0) (i : ι) :
    r i ∈ 𝔪.map (algebraMap B R) := by
  have h : ∑ i, e i • r i = 0 := by simpa [Algebra.smul_def, mul_comm] using hr
  obtain ⟨k, a, y, hy, ha⟩ := isTrivialRelation_of_sum_smul_eq_zero h
  rw [hy i]
  refine Submodule.sum_mem _ fun j _ ↦ ?_
  rw [Algebra.smul_def]
  exact Ideal.mul_mem_right _ _
    (Ideal.mem_map_of_mem _ (he _ (by simpa [mul_comm] using ha j) i))

/-- The converse of `Module.Flat.mem_ideal_map_of_sum_mul_eq_zero`, which needs no flatness:
if `𝔪 * I = 0` and the `e i` lie in `I`, every family of coefficients in `𝔪 R` is a relation
between the `e i`. -/
theorem sum_mul_eq_zero_of_forall_mem_ideal_map (hI : 𝔪 * I = ⊥) (heI : ∀ i, e i ∈ I)
    {r : ι → R} (hr : ∀ i, r i ∈ 𝔪.map (algebraMap B R)) :
    ∑ i, r i * algebraMap B R (e i) = 0 := by
  have h : 𝔪.map (algebraMap B R) * I.map (algebraMap B R) = ⊥ := by
    rw [← Ideal.map_mul, hI, Ideal.map_bot]
  refine Finset.sum_eq_zero fun i _ ↦ ?_
  have hmem : r i * algebraMap B R (e i) ∈ (⊥ : Ideal R) :=
    h ▸ Ideal.mul_mem_mul (hr i) (Ideal.mem_map_of_mem _ (heI i))
  simpa using hmem

/-- Membership in the kernel of `r ↦ ∑ i, r i * e i` over a flat `B`-algebra `R`: it is the set
of families of coefficients all of which lie in the extension `𝔪 R` of `𝔪`. -/
theorem mem_ker_linearCombination_iff [Module.Flat B R] (hI : 𝔪 * I = ⊥) (heI : ∀ i, e i ∈ I)
    (he : ∀ c : ι → B, ∑ i, c i * e i = 0 → ∀ i, c i ∈ 𝔪) (r : ι → R) :
    r ∈ LinearMap.ker (Fintype.linearCombination R fun i ↦ algebraMap B R (e i)) ↔
      ∀ i, r i ∈ 𝔪.map (algebraMap B R) := by
  rw [LinearMap.mem_ker, Fintype.linearCombination_apply]
  simp only [smul_eq_mul]
  exact ⟨fun h ↦ mem_ideal_map_of_sum_mul_eq_zero he h,
    fun h ↦ sum_mul_eq_zero_of_forall_mem_ideal_map hI heI h⟩

/-- The kernel of `r ↦ ∑ i, r i * e i` over a flat `B`-algebra `R` is the `ι`-fold product of
the extension `𝔪 R` of `𝔪`. -/
theorem ker_linearCombination [Module.Flat B R] (hI : 𝔪 * I = ⊥) (heI : ∀ i, e i ∈ I)
    (he : ∀ c : ι → B, ∑ i, c i * e i = 0 → ∀ i, c i ∈ 𝔪) :
    LinearMap.ker (Fintype.linearCombination R fun i ↦ algebraMap B R (e i)) =
      Submodule.pi Set.univ fun _ ↦ (𝔪.map (algebraMap B R) : Submodule R R) := by
  ext r
  rw [mem_ker_linearCombination_iff hI heI he, Submodule.mem_pi]
  simp

end Module.Flat

namespace Ideal

/-- If `e` spans the ideal `I` of `B`, the image of `r ↦ ∑ i, r i * e i` over any `B`-algebra `R`
is the extension `I R` of `I`. -/
theorem range_linearCombination_algebraMap (hI : I = Ideal.span (Set.range e)) :
    LinearMap.range (Fintype.linearCombination R fun i ↦ algebraMap B R (e i)) =
      I.map (algebraMap B R) := by
  rw [Fintype.range_linearCombination, hI, Ideal.map_span, ← Set.range_comp]
  rfl

end Ideal
