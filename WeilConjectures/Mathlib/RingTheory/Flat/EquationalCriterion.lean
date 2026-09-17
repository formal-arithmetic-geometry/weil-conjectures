/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.LinearAlgebra.Quotient.Pi
public import Mathlib.RingTheory.Flat.EquationalCriterion
public import WeilConjectures.Mathlib.RingTheory.Ideal.Maps

/-!
# Flat base change of the relations between a finite family

Let `B` be a commutative ring, let `J` be an ideal of `B`, and let `e : ι → B` be a finite
family of elements whose relations are exactly those forced by `J`, i.e. such that

`LinearMap.ker (Fintype.linearCombination B e) = Submodule.pi Set.univ fun _ ↦ J`.

This happens for instance when `J * I = ⊥` for an ideal `I` containing the `e i` and every
relation between the `e i` has all its coefficients in `J`; if moreover `B` is local with
maximal ideal `J` and `e` spans `I`, it says exactly that the classes of the `e i` form a basis
of `I` as a vector space over the residue field `B ⧸ J` — a structure `I` carries because
`J * I = ⊥`.

We show that this description of the relations is preserved by a flat base change
`R` of `B` (`Module.Flat.ker_linearCombination_algebraMap`) and deduce that the extension of
the ideal spanned by `e` along a flat `B`-algebra `R` is `R`-linearly isomorphic to
`(R ⧸ J R) ^ ι` (`Module.Flat.piQuotientEquivIdealMap`).

Flatness enters exactly once, through the equational criterion
`Module.Flat.isTrivialRelation_of_sum_smul_eq_zero`: it turns a relation between the `e i` with
coefficients in a flat module into relations with coefficients in `B`, which the hypothesis on
`e` then places in `J`. Mathlib's `Module.Flat.ker_lTensor_eq` is the abstract form of the same
base-change statement; we argue elementwise instead, because it is the coordinate description
of the kernel that the isomorphism above is built from.

## Main results

- `Module.Flat.mem_smul_top_of_sum_smul_eq_zero`: if the only `B`-linear relations between the
  `e i` have all their coefficients in `J`, then for a flat `B`-module `M` every relation
  `∑ i, e i • x i = 0` with `x i` in `M` has all its coefficients in `J • (⊤ : Submodule B M)`.
  Its specialisation to a flat `B`-algebra `R` is
  `Module.Flat.mem_ideal_map_of_sum_mul_eq_zero`.
- `Module.Flat.ker_linearCombination_algebraMap`: over a flat `B`-algebra `R`, the kernel of
  `r ↦ ∑ i, r i * e i` is the `ι`-fold product of the ideal `J R`.
- `Module.Flat.piQuotientEquivIdealMap`: over a flat `B`-algebra `R`, the extension of the ideal
  spanned by `e` is isomorphic to `(R ⧸ J R) ^ ι` as an `R`-module.
-/

@[expose] public section

variable {B R ι : Type*} [CommRing B] [CommRing R] [Algebra B R] [Fintype ι]
  {J : Ideal B} {e : ι → B}

namespace Module.Flat

/-- If the only `B`-linear relations between the `e i` have all their coefficients in the ideal
`J`, then the same holds for relations in a flat `B`-module `M`, with coefficients in
`J • (⊤ : Submodule B M)`. -/
theorem mem_smul_top_of_sum_smul_eq_zero {M : Type*} [AddCommGroup M] [Module B M] [Flat B M]
    (he : ∀ c : ι → B, ∑ i, c i * e i = 0 → ∀ i, c i ∈ J)
    {x : ι → M} (hx : ∑ i, e i • x i = 0) (i : ι) :
    x i ∈ J • (⊤ : Submodule B M) := by
  obtain ⟨k, a, y, hy, ha⟩ := isTrivialRelation_of_sum_smul_eq_zero hx
  rw [hy i]
  refine Submodule.sum_mem _ fun j _ ↦ Submodule.smul_mem_smul ?_ Submodule.mem_top
  exact he _ (by simpa [mul_comm] using ha j) i

/-- If `R` is flat over `B` and the only `B`-linear relations between the `e i` have all their
coefficients in the ideal `J`, then the same holds for `R`-linear relations, with coefficients
in the extension `J R`. -/
theorem mem_ideal_map_of_sum_mul_eq_zero [Flat B R]
    (he : ∀ c : ι → B, ∑ i, c i * e i = 0 → ∀ i, c i ∈ J)
    {r : ι → R} (hr : ∑ i, r i * algebraMap B R (e i) = 0) (i : ι) :
    r i ∈ J.map (algebraMap B R) := by
  rw [← Submodule.restrictScalars_mem B, ← Ideal.smul_top_eq_map]
  exact mem_smul_top_of_sum_smul_eq_zero he
    (by simpa [Algebra.smul_def, mul_comm] using hr) i

/-- **Flat base change of the relations between a finite family.** If the relations between the
`e i` are exactly those forced by the ideal `J`, the same is true over a flat `B`-algebra `R`,
for the extension `J R` of `J`. -/
theorem ker_linearCombination_algebraMap [Flat B R]
    (hker : LinearMap.ker (Fintype.linearCombination B e) =
      Submodule.pi Set.univ fun _ ↦ J) :
    LinearMap.ker (Fintype.linearCombination R fun i ↦ algebraMap B R (e i)) =
      Submodule.pi Set.univ fun _ ↦ J.map (algebraMap B R) := by
  classical
  -- The two inclusions in `hker`, read off as conditions on the family `e`.
  have he : ∀ c : ι → B, ∑ i, c i * e i = 0 → ∀ i, c i ∈ J := fun c hc i ↦ by
    simpa using Submodule.mem_pi.mp
      (hker.le (by simpa [LinearMap.mem_ker, Fintype.linearCombination_apply] using hc)) i
      (Set.mem_univ i)
  have hJe : ∀ i, ∀ m ∈ J, m * e i = 0 := fun i m hm ↦ by
    have hmem : Pi.single i m ∈ LinearMap.ker (Fintype.linearCombination B e) :=
      hker.ge (Submodule.mem_pi.mpr fun j _ ↦ by
        rcases eq_or_ne j i with rfl | hji
        · simpa using hm
        · simp [Pi.single_eq_of_ne hji])
    simpa [LinearMap.mem_ker, Fintype.linearCombination_apply, Pi.single_apply,
      ite_mul] using hmem
  ext r
  simp only [Submodule.mem_pi, Set.mem_univ, forall_const, LinearMap.mem_ker,
    Fintype.linearCombination_apply, smul_eq_mul]
  exact ⟨mem_ideal_map_of_sum_mul_eq_zero he,
    Ideal.sum_mul_eq_zero_of_forall_mem_map _ hJe⟩

/-- **The extension of an ideal with a basis, after a flat base change.** If the relations
between the `e i` are exactly those forced by the ideal `J` — which for `B` local with maximal
ideal `J` says that the classes of the `e i` form a basis of the ideal they span over the
residue field — then over a flat `B`-algebra `R` the extension of the ideal spanned by the
`e i` is `R`-linearly isomorphic to the `ι`-fold product of `R ⧸ J R`. -/
noncomputable def piQuotientEquivIdealMap [Flat B R]
    (hker : LinearMap.ker (Fintype.linearCombination B e) =
      Submodule.pi Set.univ fun _ ↦ J) :
    (ι → R ⧸ J.map (algebraMap B R)) ≃ₗ[R]
      (Ideal.span (Set.range e)).map (algebraMap B R) :=
  letI := Classical.decEq ι
  (Submodule.quotientPi fun _ : ι ↦ J.map (algebraMap B R)).symm.trans <|
    (Submodule.quotEquivOfEq _ _ (ker_linearCombination_algebraMap hker).symm).trans <|
      (LinearMap.quotKerEquivRange _).trans
        (LinearEquiv.ofEq _ _ Ideal.range_linearCombination_algebraMap)

end Module.Flat
