/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Group.Affine
public import WeilConjectures.RingTheory.HopfAlgebra.GeneralLinearGroup

/-!
# The general linear group scheme

The general linear group `GL_n` over a field `k` is the affine group scheme
`Spec k[x_ij, det⁻¹]` over `Spec k`, the spectrum of the Hopf algebra
`Matrix.GeneralLinearGroup.CoordinateRing n k`. Mathlib's `instGrpObjSpecAsOverSpec` makes it a
group object in `Over (Spec k)`. Its points with values in a `k`-algebra `R` are the invertible
`n × n` matrices over `R`, as groups.

## Main definitions

- `Matrix.GeneralLinearGroup.scheme`: `GL_n` as an affine group scheme of finite type over `k`.
- `Matrix.GeneralLinearGroup.algHomMulEquiv`: `k`-algebra homomorphisms out of the coordinate ring
  of `GL_n`, with the convolution product, are the invertible matrices.
- `Matrix.GeneralLinearGroup.homMulEquiv`: the `R`-points of the group scheme `GL_n` are the
  group `GL n R`.

## Blueprint

- `sk-d-geometry`: the ambient group `GL(V)` of the algebraic groups block, as a group scheme.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry
open scoped MonObj

namespace Matrix.GeneralLinearGroup

variable (n : Type) [Fintype n] [DecidableEq n] (k : Type u) [Field k]

section algHomMulEquiv

variable {n k} {R : Type u} [CommRing R] [Algebra k R]

/-- The matrix of values `φ(x_ij)` of a `k`-algebra homomorphism out of the coordinate ring of
`GL_n`. -/
theorem of_ofConv_coord_eq (φ : WithConv (CoordinateRing n k →ₐ[k] R)) :
    (Matrix.of fun i j ↦ φ.ofConv (coord n k i j)) =
      (genericUnit n k : Matrix n n (CoordinateRing n k)).map φ.ofConv := by
  ext i j
  simp

theorem of_ofConv_antipodeAlgHom_coord_eq (φ : WithConv (CoordinateRing n k →ₐ[k] R)) :
    (Matrix.of fun i j ↦ φ.ofConv (antipodeAlgHom n k (coord n k i j))) =
      (((genericUnit n k)⁻¹ : GL n (CoordinateRing n k)) :
        Matrix n n (CoordinateRing n k)).map φ.ofConv := by
  ext i j
  simp

theorem algHomMulEquiv_val_inv (φ : WithConv (CoordinateRing n k →ₐ[k] R)) :
    (Matrix.of fun i j ↦ φ.ofConv (coord n k i j)) *
      (Matrix.of fun i j ↦ φ.ofConv (antipodeAlgHom n k (coord n k i j))) = 1 := by
  rw [of_ofConv_coord_eq, of_ofConv_antipodeAlgHom_coord_eq]
  simp only [← AlgHom.mapMatrix_apply, ← map_mul, Units.mul_inv, map_one]

theorem algHomMulEquiv_inv_val (φ : WithConv (CoordinateRing n k →ₐ[k] R)) :
    (Matrix.of fun i j ↦ φ.ofConv (antipodeAlgHom n k (coord n k i j))) *
      (Matrix.of fun i j ↦ φ.ofConv (coord n k i j)) = 1 := by
  rw [of_ofConv_coord_eq, of_ofConv_antipodeAlgHom_coord_eq]
  simp only [← AlgHom.mapMatrix_apply, ← map_mul, Units.inv_mul, map_one]

/-- The invertible matrix `(φ(x_ij))` of values of a `k`-algebra homomorphism `φ` out of the
coordinate ring of `GL_n`. -/
noncomputable def toGL (φ : WithConv (CoordinateRing n k →ₐ[k] R)) : GL n R :=
  ⟨Matrix.of fun i j ↦ φ.ofConv (coord n k i j),
    Matrix.of fun i j ↦ φ.ofConv (antipodeAlgHom n k (coord n k i j)),
    algHomMulEquiv_val_inv φ, algHomMulEquiv_inv_val φ⟩

@[simp]
theorem coe_toGL_apply (φ : WithConv (CoordinateRing n k →ₐ[k] R)) (i j : n) :
    (toGL φ : Matrix n n R) i j = φ.ofConv (coord n k i j) :=
  rfl

theorem algHomMulEquiv_left_inv (φ : WithConv (CoordinateRing n k →ₐ[k] R)) :
    WithConv.toConv (evalAlgHom (toGL φ)) = φ := by
  ext1
  exact algHom_ext fun i j ↦ by simp

theorem algHomMulEquiv_right_inv (g : GL n R) :
    toGL (WithConv.toConv (evalAlgHom (k := k) g)) = g := by
  ext i j
  simp

theorem algHomMulEquiv_map_mul (φ ψ : WithConv (CoordinateRing n k →ₐ[k] R)) :
    toGL (φ * ψ) = toGL φ * toGL ψ := by
  ext i j
  simp [AlgHom.convMul_apply, Matrix.mul_apply]

variable (n k R)

/-- `k`-algebra homomorphisms from the coordinate ring of `GL_n` to `R`, with the convolution
product, are the invertible `n × n` matrices over `R`. -/
noncomputable def algHomMulEquiv : WithConv (CoordinateRing n k →ₐ[k] R) ≃* GL n R where
  toFun := toGL
  invFun g := WithConv.toConv (evalAlgHom g)
  left_inv := algHomMulEquiv_left_inv
  right_inv := algHomMulEquiv_right_inv
  map_mul' := algHomMulEquiv_map_mul

end algHomMulEquiv

/-- The general linear group `GL_n` as an affine group scheme over `k`: the spectrum of the Hopf
algebra `k[x_ij, det⁻¹]`. (blueprint: `sk-d-geometry`) -/
noncomputable abbrev scheme : Over (Spec (.of k)) :=
  (Spec (.of (CoordinateRing n k))).asOver (Spec (.of k))

noncomputable instance : GrpObj (scheme n k) := inferInstance

instance : IsAffine (scheme n k).left :=
  inferInstanceAs (IsAffine (Spec (.of (CoordinateRing n k))))

instance : LocallyOfFiniteType (scheme n k).hom :=
  locallyOfFiniteType_specOverSpec

/-- The `R`-points of the group scheme `GL_n` are the invertible `n × n` matrices over `R`, as
groups. (blueprint: `sk-d-geometry`) -/
noncomputable def homMulEquiv (R : Type u) [CommRing R] [Algebra k R] :
    ((Spec (.of R)).asOver (Spec (.of k)) ⟶ scheme n k) ≃* GL n R :=
  Spec.mapMulEquiv.symm.trans (algHomMulEquiv n k R)

end Matrix.GeneralLinearGroup
