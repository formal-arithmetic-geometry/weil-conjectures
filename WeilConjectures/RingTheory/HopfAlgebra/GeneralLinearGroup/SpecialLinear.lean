/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.RingTheory.HopfAlgebra.GeneralLinearGroup
public import WeilConjectures.RingTheory.HopfAlgebra.LaurentPolynomial

/-!
# The determinant on the Hopf algebra of `GL_n`, and the Hopf ideal of `SL_n`

The determinant `det (x_ij)` of the generic matrix is a unit of the coordinate ring
`k[x_ij, det⁻¹]` of `GL_n`; it is group-like: `Δ(det) = det ⊗ det`, `ε(det) = 1`. Hence
`T ↦ det` is a homomorphism of Hopf algebras `k[T;T⁻¹] → k[x_ij, det⁻¹]`, dual to the
determinant `GL_n → 𝔾ₘ`, and the ideal `(det - 1)` is a Hopf ideal, cutting out the special
linear group `SL_n`.

## Main definitions

- `Matrix.GeneralLinearGroup.detUnit`: the determinant of the generic matrix, a unit of the
  coordinate ring of `GL_n`.
- `Matrix.GeneralLinearGroup.detBialgHom`: the bialgebra homomorphism `k[T;T⁻¹] → k[GL_n]`,
  `T ↦ det`.
- `Matrix.GeneralLinearGroup.specialLinearIdeal`: the Hopf ideal `(det - 1)` of `SL_n`.
-/

@[expose] public section

open TensorProduct LaurentPolynomial

namespace Matrix.GeneralLinearGroup

variable (n : Type*) [Fintype n] [DecidableEq n] (k : Type*) [CommRing k]

/-- The determinant `det (x_ij)` of the generic invertible matrix, a unit of the coordinate ring
`k[x_ij, det⁻¹]` of `GL_n`. -/
noncomputable def detUnit : (CoordinateRing n k)ˣ :=
  Matrix.GeneralLinearGroup.det (genericUnit n k)

variable {n k}

/-- Evaluating the determinant of the generic matrix at an invertible matrix `g` gives the
determinant of `g`. -/
theorem evalAlgHom_detUnit {R : Type*} [CommRing R] [Algebra k R] (g : GL n R) :
    evalAlgHom g (detUnit n k : CoordinateRing n k) =
      (Matrix.GeneralLinearGroup.det g : R) := by
  have hg : map (evalAlgHom (k := k) g).toRingHom (genericUnit n k) = g :=
    (algHomMulEquiv n k R).apply_symm_apply g
  conv_rhs => rw [← hg]
  rw [Matrix.GeneralLinearGroup.map_det]
  rfl

theorem counitAlgHom_detUnit : counitAlgHom n k (detUnit n k : CoordinateRing n k) = 1 := by
  rw [counitAlgHom, evalAlgHom_detUnit, map_one, Units.val_one]

@[simp]
theorem counit_detUnit : Coalgebra.counit (R := k) (detUnit n k : CoordinateRing n k) = 1 :=
  counitAlgHom_detUnit

theorem comulAlgHom_detUnit :
    comulAlgHom n k (detUnit n k : CoordinateRing n k) =
      (detUnit n k : CoordinateRing n k) ⊗ₜ[k] (detUnit n k : CoordinateRing n k) := by
  rw [comulAlgHom, evalAlgHom_detUnit, map_mul, Units.val_mul, Matrix.GeneralLinearGroup.map_det,
    Matrix.GeneralLinearGroup.map_det]
  change ((detUnit n k : CoordinateRing n k) ⊗ₜ[k] 1) *
    (1 ⊗ₜ[k] (detUnit n k : CoordinateRing n k)) = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

@[simp]
theorem comul_detUnit :
    Coalgebra.comul (R := k) (detUnit n k : CoordinateRing n k) =
      (detUnit n k : CoordinateRing n k) ⊗ₜ[k] (detUnit n k : CoordinateRing n k) :=
  comulAlgHom_detUnit

theorem antipodeAlgHom_detUnit_mul :
    antipodeAlgHom n k (detUnit n k : CoordinateRing n k) *
      (detUnit n k : CoordinateRing n k) = 1 := by
  rw [antipodeAlgHom, evalAlgHom_detUnit, detUnit, ← Units.val_mul, ← map_mul, inv_mul_cancel,
    map_one, Units.val_one]

theorem antipode_detUnit_mul :
    HopfAlgebra.antipode k (detUnit n k : CoordinateRing n k) *
      (detUnit n k : CoordinateRing n k) = 1 :=
  antipodeAlgHom_detUnit_mul

variable (n k)

/-- The `k`-algebra homomorphism `k[T;T⁻¹] → k[x_ij, det⁻¹]`, `T ↦ det (x_ij)`. -/
noncomputable def detAlgHom : k[T;T⁻¹] →ₐ[k] CoordinateRing n k :=
  evalUnit k (detUnit n k)

@[simp]
theorem detAlgHom_T_one : detAlgHom n k (T 1) = (detUnit n k : CoordinateRing n k) := by
  simp [detAlgHom]

/-- The determinant as a homomorphism of bialgebras `k[T;T⁻¹] → k[x_ij, det⁻¹]`, `T ↦ det`:
the comorphism of the determinant `GL_n → 𝔾ₘ`. -/
noncomputable def detBialgHom : k[T;T⁻¹] →ₐc[k] CoordinateRing n k :=
  BialgHom.ofAlgHom (detAlgHom n k) (algHom_ext_T (by simp)) (algHom_ext_T (by simp))

@[simp]
theorem coe_detBialgHom :
    (detBialgHom n k : k[T;T⁻¹] →ₐ[k] CoordinateRing n k) = detAlgHom n k :=
  rfl

/-- The ideal `(det (x_ij) - 1)` of the coordinate ring of `GL_n`, cutting out the special linear
group `SL_n = Spec k[x_ij] ⧸ (det - 1)`. -/
noncomputable def specialLinearIdeal : Ideal (CoordinateRing n k) :=
  Ideal.span {(detUnit n k : CoordinateRing n k) - 1}

theorem detUnit_sub_one_mem_specialLinearIdeal :
    (detUnit n k : CoordinateRing n k) - 1 ∈ specialLinearIdeal n k :=
  Ideal.subset_span rfl

/-- The ideal `(det - 1)` is a Hopf ideal of the coordinate ring of `GL_n`. -/
instance isHopfIdeal_specialLinearIdeal : (specialLinearIdeal n k).IsHopfIdeal k := by
  refine Ideal.isHopfIdeal_span ?_ ?_ ?_ <;> rintro x rfl
  · rw [map_sub, counit_detUnit, Bialgebra.counit_one, sub_self]
  · have h : Ideal.Quotient.mkₐ k (Ideal.span {(detUnit n k : CoordinateRing n k) - 1})
        (detUnit n k : CoordinateRing n k) = 1 := by
      rw [← map_one (Ideal.Quotient.mkₐ k _), Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq]
      exact detUnit_sub_one_mem_specialLinearIdeal n k
    rw [map_sub, comul_detUnit, Bialgebra.comul_one, map_sub, map_one,
      Algebra.TensorProduct.map_tmul, h, Algebra.TensorProduct.one_def, sub_self]
  · rw [map_sub, HopfAlgebra.antipode_one]
    have : HopfAlgebra.antipode k (detUnit n k : CoordinateRing n k) - 1 =
        -HopfAlgebra.antipode k (detUnit n k : CoordinateRing n k) *
          ((detUnit n k : CoordinateRing n k) - 1) := by
      rw [neg_mul, mul_sub, antipode_detUnit_mul, mul_one, neg_sub]
    rw [this]
    exact Ideal.mul_mem_left _ _ (detUnit_sub_one_mem_specialLinearIdeal n k)

end Matrix.GeneralLinearGroup
