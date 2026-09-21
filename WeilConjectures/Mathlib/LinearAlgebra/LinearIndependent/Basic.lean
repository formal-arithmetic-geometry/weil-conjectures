/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.LinearAlgebra.LinearIndependent.Basic
public import Mathlib.RingTheory.Ideal.Maps

/-!
# Linear independence over a quotient of the scalars

Let `κ` be an `R`-algebra whose structure map `R → κ` is surjective — a quotient of `R`, up to
isomorphism — and let `M` be an `R`-module carrying a compatible `κ`-action. A finite family in
`M` is `κ`-linearly independent exactly when every `R`-linear relation between its members has
all its coefficients in `RingHom.ker (algebraMap R κ)`: the two statements are the same after
lifting coefficients along the surjection.

## Main results

* `Fintype.linearIndependent_iff_forall_mem_ker_algebraMap`: the criterion above.
* `LinearIndependent.mem_ker_algebraMap_of_sum_mul_eq_zero`: its forward direction for a family
  in an ideal `I` of `R`, where the relations are written multiplicatively.
-/

@[expose] public section

variable {R κ : Type*} [CommRing R] [CommRing κ] [Algebra R κ] {ι : Type*}

/-- **Linear independence over a quotient of the scalars.** If the structure map `R → κ` is
surjective, a finite family in a `κ`-module is `κ`-linearly independent exactly when every
`R`-linear relation between its members has all its coefficients in the kernel of `R → κ`. -/
theorem Fintype.linearIndependent_iff_forall_mem_ker_algebraMap {M : Type*} [AddCommGroup M]
    [Module R M] [Module κ M] [IsScalarTower R κ M] [Fintype ι]
    (hsur : Function.Surjective (algebraMap R κ)) {v : ι → M} :
    LinearIndependent κ v ↔
      ∀ c : ι → R, ∑ i, c i • v i = 0 → ∀ i, c i ∈ RingHom.ker (algebraMap R κ) := by
  rw [Fintype.linearIndependent_iff]
  refine ⟨fun H c hc i ↦ RingHom.mem_ker.mpr
    (H (fun i ↦ algebraMap R κ (c i)) (by simpa only [algebraMap_smul] using hc) i),
    fun H g hg i ↦ ?_⟩
  -- lift the coefficients `g` along the surjection and apply the hypothesis to the lift
  choose c hc using fun i ↦ hsur (g i)
  rw [← hc i]
  exact RingHom.mem_ker.mp (H c (by simpa only [← hc, algebraMap_smul] using hg) i)

/-- **The relations in `R` between the members of a `κ`-linearly independent family in an ideal
`I` of `R` have all their coefficients in the kernel of `R → κ`.** -/
theorem LinearIndependent.mem_ker_algebraMap_of_sum_mul_eq_zero {I : Ideal R} [Module κ I]
    [IsScalarTower R κ I] [Fintype ι] {v : ι → I} (hv : LinearIndependent κ v)
    (hsur : Function.Surjective (algebraMap R κ)) {c : ι → R}
    (hc : ∑ i, c i * (v i : R) = 0) (i : ι) :
    c i ∈ RingHom.ker (algebraMap R κ) := by
  refine (Fintype.linearIndependent_iff_forall_mem_ker_algebraMap hsur).mp hv c ?_ i
  ext
  simpa using hc
