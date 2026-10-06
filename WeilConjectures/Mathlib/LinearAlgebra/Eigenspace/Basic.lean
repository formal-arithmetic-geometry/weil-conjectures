/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Eigenspace.Basic

/-!
# Eigenvalues on a subquotient

The eigenvalues of an endomorphism on any of its invariant subquotients occur among its
eigenvalues on the ambient space.

## Main declarations

* `Module.End.hasEigenvalue_of_subquotient`: a scalar acting on a nonzero invariant subquotient is
  an eigenvalue of the ambient endomorphism.

## Blueprint

`Module.End.hasEigenvalue_of_subquotient` implements part of `sk-p-linear-filtration`.
-/

@[expose] public section

namespace Module.End

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- If a scalar `c` acts on a nonzero invariant subquotient `S ⧸ U` of `V`, then `c` is an
eigenvalue of the endomorphism on all of `V`.
(blueprint: `sk-p-linear-filtration`) -/
theorem hasEigenvalue_of_subquotient (f : Module.End K V) {U S : Submodule K V} (hUS : U < S)
    (hU : U ≤ U.comap f) (hS : S ≤ S.comap f) (c : K) (hc : ∀ x ∈ S, f x - c • x ∈ U) :
    f.HasEigenvalue c := by
  set g : Module.End K V := f - algebraMap K (Module.End K V) c
  have hgS : S ≤ S.comap g := fun x hx ↦ S.sub_mem (hS hx) (S.smul_mem c hx)
  set U' := U.comap S.subtype
  have hgU : U' ≤ U'.comap (g.restrict hgS) := fun x hx ↦
    show f x - c • (x : V) ∈ U from U.sub_mem (hU hx) (U.smul_mem c hx)
  have hzero : U'.mapQ U' (g.restrict hgS) hgU = 0 := by
    ext x
    simpa [Submodule.Quotient.mk_eq_zero, U', g] using hc x x.2
  have : Nontrivial (S ⧸ U') := by
    refine Submodule.Quotient.nontrivial_iff.mpr fun h ↦ hUS.ne ?_
    refine le_antisymm hUS.le fun x hx ↦ ?_
    have : (⟨x, hx⟩ : S) ∈ U' := h ▸ Submodule.mem_top
    exact this
  have hdet : g.det = 0 := by
    rw [LinearMap.det_eq_det_mul_det S g hgS, LinearMap.det_eq_det_mul_det U' _ hgU, hzero,
      LinearMap.det_zero' (Module.Free.chooseBasis K (S ⧸ U')), mul_zero, zero_mul]
  rw [hasEigenvalue_iff, eigenspace_def, ← LinearMap.det_eq_zero_iff_ker_ne_bot]
  exact hdet

end Module.End
