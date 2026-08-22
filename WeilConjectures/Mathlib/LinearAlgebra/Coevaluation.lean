/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.LinearAlgebra.Coevaluation

/-!
# The coevaluation map of a finite basis over a commutative semiring

`Mathlib.LinearAlgebra.Coevaluation` defines the coevaluation map `K →ₗ[K] V ⊗[K] Dual K V`
of a finite-dimensional vector space over a field, together with the two zigzag identities
relating it to the contraction map, which make a finite-dimensional vector space a dualizable
object of the monoidal category of vector spaces. Neither the definition nor the proofs use
anything about fields beyond the existence of a finite basis, so this file generalizes them
to a module with a chosen finite basis over a commutative semiring: for `b : Basis ι R M`
with `ι` finite, we define `b.coevaluation : R →ₗ[R] M ⊗[R] Dual R M` sending `1` to
`∑ i, b i ⊗ₜ b.coord i` and prove the zigzag identities against `contractLeft`.

Consequently a finite free module over a commutative ring is a dualizable object of
`ModuleCat R`; this is recorded in
`WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric`.

## Main declarations

- `Module.Basis.coevaluation`: the coevaluation map of a finite basis.
- `Module.Basis.contractLeft_assoc_coevaluation`,
  `Module.Basis.contractLeft_assoc_coevaluation'`: the zigzag identities, in the same form
  as the field-case `contractLeft_assoc_coevaluation` and `contractLeft_assoc_coevaluation'`.
-/

@[expose] public section

noncomputable section

open TensorProduct Module

universe u v w

namespace Module.Basis

variable {R : Type u} [CommSemiring R]
variable {M : Type v} [AddCommMonoid M] [Module R M]
variable {ι : Type w} [Fintype ι] (b : Basis ι R M)

/-- The coevaluation map of a finite basis `b` of a module `M` over a commutative semiring
`R` sends `1 : R` to `∑ i, b i ⊗ₜ b.coord i`. Together with the contraction map
(`contractLeft`) it satisfies the zigzag identities `b.contractLeft_assoc_coevaluation` and
`b.contractLeft_assoc_coevaluation'`, exhibiting `Dual R M` as a monoidal-categorical dual
of `M`. This generalizes `coevaluation` from finite-dimensional vector spaces over a field
to finite free modules. -/
def coevaluation : R →ₗ[R] M ⊗[R] Module.Dual R M :=
  LinearMap.toSpanSingleton R _ (∑ i, b i ⊗ₜ[R] b.coord i)

theorem coevaluation_apply_one : b.coevaluation (1 : R) = ∑ i, b i ⊗ₜ[R] b.coord i := by
  simp [coevaluation, LinearMap.toSpanSingleton_apply]

/-- This lemma corresponds to one of the coherence laws for duals in rigid categories, see
`CategoryTheory.Monoidal.Rigid`. It generalizes `contractLeft_assoc_coevaluation` from
finite-dimensional vector spaces over a field to finite free modules. -/
theorem contractLeft_assoc_coevaluation :
    (contractLeft R M).rTensor _ ∘ₗ
        (TensorProduct.assoc R _ _ _).symm.toLinearMap ∘ₗ
          b.coevaluation.lTensor (Module.Dual R M) =
      (TensorProduct.lid R _).symm.toLinearMap ∘ₗ (TensorProduct.rid R _).toLinearMap := by
  letI := Classical.decEq ι
  apply TensorProduct.ext
  apply b.dualBasis.ext; intro j; apply LinearMap.ext_ring
  rw [LinearMap.compr₂ₛₗ_apply, LinearMap.compr₂ₛₗ_apply, TensorProduct.mk_apply]
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_toLinearMap]
  rw [rid_tmul, one_smul, lid_symm_apply]
  simp only [LinearMap.lTensor_tmul, coevaluation_apply_one]
  rw [TensorProduct.tmul_sum, map_sum]; simp only [assoc_symm_tmul]
  rw [map_sum]; simp only [LinearMap.rTensor_tmul, contractLeft_apply]
  simp only [coe_dualBasis, coord_apply, repr_self_apply, TensorProduct.ite_tmul]
  rw [Finset.sum_ite_eq']; simp only [Finset.mem_univ, if_true]

/-- This lemma corresponds to one of the coherence laws for duals in rigid categories, see
`CategoryTheory.Monoidal.Rigid`. It generalizes `contractLeft_assoc_coevaluation'` from
finite-dimensional vector spaces over a field to finite free modules. -/
theorem contractLeft_assoc_coevaluation' :
    (contractLeft R M).lTensor _ ∘ₗ
        (TensorProduct.assoc R _ _ _).toLinearMap ∘ₗ b.coevaluation.rTensor M =
      (TensorProduct.rid R _).symm.toLinearMap ∘ₗ (TensorProduct.lid R _).toLinearMap := by
  letI := Classical.decEq ι
  apply TensorProduct.ext
  apply LinearMap.ext_ring; apply b.ext; intro j
  rw [LinearMap.compr₂ₛₗ_apply, LinearMap.compr₂ₛₗ_apply, TensorProduct.mk_apply]
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_toLinearMap]
  rw [lid_tmul, one_smul, rid_symm_apply]
  simp only [LinearMap.rTensor_tmul, coevaluation_apply_one]
  rw [TensorProduct.sum_tmul, map_sum]; simp only [assoc_tmul]
  rw [map_sum]; simp only [LinearMap.lTensor_tmul, contractLeft_apply]
  simp only [coord_apply, repr_self_apply, TensorProduct.tmul_ite]
  rw [Finset.sum_ite_eq]; simp only [Finset.mem_univ, if_true]

end Module.Basis
