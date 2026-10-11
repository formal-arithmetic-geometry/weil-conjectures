/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.RingTheory.HopfAlgebra.MonoidAlgebra
public import WeilConjectures.RingTheory.HopfAlgebra.GeneralLinearGroup.HopfIdeal

/-!
# The determinant on the coordinate ring of `GL_n`

The determinant `det = ∑_σ sgn(σ) ∏ᵢ x_{iσ(i)}` of the generic matrix is a group-like element of
the Hopf algebra `k[x_ij, det⁻¹]`: `Δ(det) = det ⊗ det` and `ε(det) = 1`, by multiplicativity of
the determinant. Hence:

- the ideal `(det - 1)` is a Hopf ideal, the ideal of the special linear group `SL_n`, whose
  `R`-points are the matrices of determinant one;
- `t ↦ det` is a bialgebra homomorphism `k[t, t⁻¹] → k[x_ij, det⁻¹]`, dual to the determinant
  homomorphism `GL_n → 𝔾ₘ`.

## Main definitions

- `Matrix.GeneralLinearGroup.detCoord`: the determinant of the generic matrix.
- `Matrix.GeneralLinearGroup.specialLinearIdeal`: the Hopf ideal `(det - 1)`.
- `Matrix.GeneralLinearGroup.specialLinearGroupMulEquiv`: the matrices satisfying the equations
  of `(det - 1)` are the special linear group.
- `Matrix.GeneralLinearGroup.detBialgHom`: the bialgebra homomorphism `t ↦ det`.

## Main results

- `Matrix.GeneralLinearGroup.isGroupLikeElem_detCoord`: the determinant is group-like.
- `Matrix.GeneralLinearGroup.antipode_coord`: the antipode in terms of cofactors,
  `S(x_ij) = det⁻¹ · adj(x)_ij`.

## Blueprint

- `def-sc-general-linear-group`: the antipode `i^*(x_ij) = (-1)^(i+j) M_ji / det`, the special
  linear group `SL_{c,k} = Spec k[x_ij] ⧸ (det - 1)`
  and the determinant `GL_{c,k} → 𝐆_m`, dual to `t ↦ det`.
-/

@[expose] public section

open TensorProduct WithConv LaurentPolynomial

namespace Matrix.GeneralLinearGroup

variable (n : Type*) [Fintype n] [DecidableEq n] (k : Type*) [CommRing k]

/-- The determinant `det = ∑_σ sgn(σ) ∏ᵢ x_{iσ(i)}` of the generic matrix `(x_ij)`, as a function
on `GL_n`. -/
noncomputable def detCoord : CoordinateRing n k :=
  (genericUnit n k : Matrix n n (CoordinateRing n k)).det

/-- The comultiplication of `k[x_ij, det⁻¹]` maps the generic matrix to the product of its two
copies in `k[x_ij, det⁻¹] ⊗ k[x_ij, det⁻¹]`. -/
theorem map_comulAlgHom_genericUnit :
    (genericUnit n k : Matrix n n (CoordinateRing n k)).map (comulAlgHom n k) =
      (genericUnit n k : Matrix n n (CoordinateRing n k)).map
          (Algebra.TensorProduct.includeLeft (S := k) (B := CoordinateRing n k)) *
        (genericUnit n k : Matrix n n (CoordinateRing n k)).map
          (Algebra.TensorProduct.includeRight (A := CoordinateRing n k)) := by
  ext i j
  simp [Matrix.mul_apply, Algebra.TensorProduct.tmul_mul_tmul]

/-- The determinant of the generic matrix is group-like: `Δ(det) = det ⊗ det` and `ε(det) = 1`. -/
theorem isGroupLikeElem_detCoord : IsGroupLikeElem k (detCoord n k) where
  counit_eq_one := by
    change counitAlgHom n k (detCoord n k) = 1
    have h : (counitAlgHom n k).mapMatrix (genericUnit n k : Matrix n n (CoordinateRing n k)) =
        1 := by
      ext i j
      simp
    rw [detCoord, AlgHom.map_det, h, det_one]
  comul_eq_tmul_self := by
    change comulAlgHom n k (detCoord n k) = _
    rw [detCoord, AlgHom.map_det, AlgHom.mapMatrix_apply, map_comulAlgHom_genericUnit, det_mul,
      ← AlgHom.mapMatrix_apply, ← AlgHom.map_det, ← AlgHom.mapMatrix_apply, ← AlgHom.map_det]
    simp [Algebra.TensorProduct.tmul_mul_tmul]

variable {n k}

/-- Evaluating the determinant function at a matrix `g` gives the determinant of `g`. -/
@[simp]
theorem evalAlgHom_detCoord {R : Type*} [CommRing R] [Algebra k R] (g : GL n R) :
    evalAlgHom g (detCoord n k) = (g : Matrix n n R).det := by
  rw [detCoord, AlgHom.map_det]
  congr 1
  ext i j
  simp

variable (n k) in
/-- The antipode of `k[x_ij, det⁻¹]` in terms of cofactors: `S(x_ij) = det⁻¹ · adj(x)_ij`, where
the adjugate `adj(x)_ij = (-1)^(i+j) M_ji` is the signed minor obtained by deleting row `j` and
column `i` of the generic matrix (`Matrix.adjugate_fin_succ_eq_det_submatrix`).
(blueprint: `def-sc-general-linear-group`) -/
theorem antipode_coord (i j : n) :
    HopfAlgebra.antipode k (coord n k i j) =
      Ring.inverse (detCoord n k) *
        (genericUnit n k : Matrix n n (CoordinateRing n k)).adjugate i j := by
  change antipodeAlgHom n k (coord n k i j) = _
  rw [antipodeAlgHom_coord, Matrix.coe_units_inv, Matrix.inv_def, Matrix.smul_apply, smul_eq_mul,
    detCoord]

variable (n k)

/-- The ideal `(det - 1)` of `k[x_ij, det⁻¹]`, a Hopf ideal: the ideal of the special linear
group `SL_n`. (blueprint: `def-sc-general-linear-group`) -/
noncomputable def specialLinearIdeal : Ideal (CoordinateRing n k) :=
  Ideal.span {detCoord n k - 1}

instance : (specialLinearIdeal n k).IsHopfIdeal k :=
  (isGroupLikeElem_detCoord n k).isHopfIdeal_span_sub_one

variable {n k}

/-- A matrix satisfies the equations of `(det - 1)` if and only if it has determinant one. -/
theorem mem_zeroLocus_specialLinearIdeal {R : Type*} [CommRing R] [Algebra k R] {g : GL n R} :
    g ∈ zeroLocus (specialLinearIdeal n k) R ↔ (g : Matrix n n R).det = 1 := by
  rw [mem_zeroLocus]
  constructor
  · intro h
    have := h _ (Ideal.subset_span rfl)
    rwa [map_sub, map_one, evalAlgHom_detCoord, sub_eq_zero] at this
  · intro h a ha
    have : specialLinearIdeal n k ≤ RingHom.ker (evalAlgHom (k := k) g) :=
      Ideal.span_le.2 (by simp [h])
    exact this ha

variable (n k) (R : Type*) [CommRing R] [Algebra k R]

/-- The matrices satisfying the equations of `(det - 1)` are the matrices of determinant one. -/
theorem zeroLocus_specialLinearIdeal :
    zeroLocus (specialLinearIdeal n k) R = (SpecialLinearGroup.toGL (n := n) (R := R)).range := by
  ext g
  rw [mem_zeroLocus_specialLinearIdeal, MonoidHom.mem_range]
  constructor
  · intro h
    exact ⟨⟨g, h⟩, Units.ext rfl⟩
  · rintro ⟨A, rfl⟩
    exact A.2

/-- The group of `R`-points of `SL_n`, cut out in `GL n R` by the equations of `(det - 1)`, is the
special linear group `SL(n, R)`. (blueprint: `def-sc-general-linear-group`) -/
noncomputable def specialLinearGroupMulEquiv :
    SpecialLinearGroup n R ≃* zeroLocus (specialLinearIdeal n k) R :=
  (MonoidHom.ofInjective SpecialLinearGroup.toGL_injective).trans
    (MulEquiv.subgroupCongr (zeroLocus_specialLinearIdeal n k R).symm)

variable {n k R}

@[simp]
theorem coe_specialLinearGroupMulEquiv_apply (A : SpecialLinearGroup n R) :
    ((specialLinearGroupMulEquiv n k R A : GL n R) : Matrix n n R) = A :=
  rfl

variable (n k)

/-- The bialgebra homomorphism `k[t, t⁻¹] → k[x_ij, det⁻¹]`, `t ↦ det`, dual to the determinant
homomorphism `GL_n → 𝔾ₘ`. (blueprint: `def-sc-general-linear-group`) -/
noncomputable def detBialgHom : k[T;T⁻¹] →ₐc[k] CoordinateRing n k :=
  groupLikeBialgHom (isGroupLikeElem_detCoord n k)

@[simp]
theorem detBialgHom_T_one : detBialgHom n k (T 1) = detCoord n k :=
  groupLikeBialgHom_T_one _

variable {n k}

/-- On points, `t ↦ det` is the determinant: evaluation at `g` composed with `t ↦ det` is
evaluation of Laurent polynomials at `det g`. -/
theorem algHomMulEquiv_evalAlgHom_comp_detBialgHom (g : GL n R) :
    LaurentPolynomial.algHomMulEquiv k R
        (toConv ((evalAlgHom g).comp (detBialgHom n k : k[T;T⁻¹] →ₐ[k] CoordinateRing n k))) =
      GeneralLinearGroup.det g := by
  ext
  simp

end Matrix.GeneralLinearGroup
