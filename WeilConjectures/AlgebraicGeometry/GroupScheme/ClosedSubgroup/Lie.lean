/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Lie.Abelian
public import Mathlib.Algebra.Lie.Matrix
public import Mathlib.Algebra.Lie.Subalgebra
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.Tactic.NoncommRing
public import WeilConjectures.AlgebraicGeometry.GroupScheme.ClosedSubgroup
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Lie
public import WeilConjectures.Mathlib.Algebra.DualNumber

/-!
# Lie algebras of closed subgroup schemes of `GL_n` and rational representations

For a closed subgroup scheme `G = V(I)` of `GL_n` over a commutative ring `k`, the Lie algebra
`Lie(G) = T_1 G ⊆ gl_n` is the space of matrices `X` such that `1 + εX` is a point of `G` with
values in the dual numbers `k[ε] = k[ε]/(ε²)`. With the commutator bracket `⁅X, Y⁆ = XY - YX` it
is a Lie subalgebra of `gl_n`. Its additive group is the tangent group
`AlgebraicGeometry.tangentGroup G = ker(G(k[ε]) → G(k))` of the group scheme `G`
(`AlgebraicGeometry.GeneralLinearGroup.tangentGroupMulEquiv`).

A rational representation of `G` on `k^m` is a homomorphism of group schemes `G ⟶ GL_m`, that is
a bialgebra homomorphism `k[GL_m] → k[G]` of coordinate rings. On `R`-points it is a group
homomorphism `G(R) → GL m R`, and its differential `Lie(G) → gl_m` is the `ε`-coefficient of the
image of `1 + εX`. Both closure of `Lie(G)` under the bracket and compatibility of the
differential with it come from the commutator `(1 + εX)(1 + δY)(1 + εX)⁻¹(1 + δY)⁻¹ = 1 + εδ⁅X, Y⁆`
over `k[ε, δ]/(ε², δ²)`, pulled back along the injective map `k[ε] → k[ε, δ]`, `ε ↦ εδ`.

In characteristic zero, a subspace is stable under a connected group if and only if it is stable
under its Lie algebra, and the Lie algebra of the centre is the centre of the Lie algebra.

## Implementation notes

The bracket on `Matrix n n k` is the commutator bracket `LieRing.ofAssociativeRing`, which is
not a global instance; it is activated locally here, as in `Mathlib.Algebra.Lie.Matrix`. Since it
appears in the type `LieSubalgebra k (Matrix n n k)` of
`AlgebraicGeometry.GeneralLinearGroup.lieAlgebra`,
files using the declarations of this file must activate it as well:
`attribute [local instance 100] LieRing.ofAssociativeRing`.

## Main definitions

- `AlgebraicGeometry.GeneralLinearGroup.dualUnit`: the invertible matrix `1 + εX` over the dual
  numbers.
- `AlgebraicGeometry.GeneralLinearGroup.lieAlgebra`: the Lie algebra of the closed subgroup scheme
  `V(I)`.
- `AlgebraicGeometry.GeneralLinearGroup.tangentGroupMulEquiv`: the tangent group of the group
  scheme `V(I)`
  is the additive group of `lieAlgebra I`.
- `AlgebraicGeometry.GeneralLinearGroup.RationalHom`: a rational representation of `V(I)` on `k^m`.
- `AlgebraicGeometry.GeneralLinearGroup.RationalHom.points`: a rational representation on
  `R`-points.
- `AlgebraicGeometry.GeneralLinearGroup.RationalHom.differential`: the differential of a rational
  representation, a homomorphism of Lie algebras.

## Main results

- `AlgebraicGeometry.GeneralLinearGroup.dualUnit_add`: differentiating the multiplication of `GL_n`
  at
  `(1, 1)` gives addition.
- `AlgebraicGeometry.GeneralLinearGroup.lie_mem_lieAlgebra_of_commutator_le`: if the commutators of
  `V(I)`
  lie in `V(J)`, then so do the brackets of their tangent vectors.
- `AlgebraicGeometry.GeneralLinearGroup.lieAlgebra_identityComponent`,
  `AlgebraicGeometry.GeneralLinearGroup.finrank_lieAlgebra_eq_ringKrullDim`: the Lie algebra only
  sees the
  identity component and has the dimension of the group (Cartier's theorem).
- `AlgebraicGeometry.GeneralLinearGroup.invariant_iff_differential_invariant`,
  `AlgebraicGeometry.GeneralLinearGroup.lieAlgebra_center`: the group–Lie comparison.

## Blueprint

- `sk-d-tangent`: the Lie algebra of a matrix algebraic group, rational representations and their
  differentials.
- `sk-i-cartier`: the Lie algebra clauses of Cartier's theorem.
- `sk-p-comparison`: invariant subspaces and the centre, for the group and for its Lie algebra.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry TrivSqZeroExt
open scoped MonObj

namespace AlgebraicGeometry.GeneralLinearGroup

open Matrix.GeneralLinearGroup
open scoped Matrix
open Matrix (map_inr_mul_map_inr eq_one_add_map_inr_of_map_fst_eq_one map_snd_mul_of_map_fst_eq_one)

attribute [local instance 100] LieRing.ofAssociativeRing

section DualUnit

variable {n : Type*} [Fintype n] [DecidableEq n] {k : Type*} [CommRing k]

/-- The invertible matrix `1 + εX` over the dual numbers `k[ε]`, with inverse `1 - εX`.
(blueprint: `sk-d-tangent`) -/
def dualUnit (X : Matrix n n k) : GL n (DualNumber k) :=
  ⟨1 + X.map inr, 1 - X.map inr,
    by rw [add_mul, one_mul, mul_sub, mul_one, map_inr_mul_map_inr, sub_zero, sub_add_cancel],
    by rw [sub_mul, one_mul, mul_add, mul_one, map_inr_mul_map_inr, add_zero, add_sub_cancel_right]⟩

theorem coe_dualUnit (X : Matrix n n k) :
    (dualUnit X : Matrix n n (DualNumber k)) = 1 + X.map inr :=
  rfl

/-- Differentiating the multiplication of `GL_n` at `(1, 1)` gives addition:
`(1 + εX)(1 + εY) = 1 + ε(X + Y)`. (blueprint: `sk-i-cartier`) -/
@[simp]
theorem dualUnit_add (X Y : Matrix n n k) : dualUnit (X + Y) = dualUnit X * dualUnit Y := by
  ext1
  rw [Units.val_mul, coe_dualUnit, coe_dualUnit, coe_dualUnit, add_mul, one_mul, mul_add, mul_one,
    map_inr_mul_map_inr, add_zero, Matrix.map_add _ (inr_add k)]
  abel

@[simp]
theorem dualUnit_zero : dualUnit (0 : Matrix n n k) = 1 := by
  ext1
  simp [coe_dualUnit]

@[simp]
theorem dualUnit_neg (X : Matrix n n k) : dualUnit (-X) = (dualUnit X)⁻¹ :=
  (inv_eq_of_mul_eq_one_right (by rw [← dualUnit_add, add_neg_cancel, dualUnit_zero])).symm

theorem map_snd_coe_dualUnit (X : Matrix n n k) :
    (dualUnit X : Matrix n n (DualNumber k)).map snd = X := by
  ext i j
  simp [coe_dualUnit, Matrix.one_apply, apply_ite snd]

theorem dualUnit_injective : Function.Injective (dualUnit : Matrix n n k → GL n (DualNumber k)) :=
  fun X Y h ↦ by rw [← map_snd_coe_dualUnit X, h, map_snd_coe_dualUnit]

/-- The matrix `1 + εX` reduces to the identity modulo `ε`. -/
@[simp]
theorem map_fstHom_dualUnit (X : Matrix n n k) :
    map (fstHom k k k).toRingHom (dualUnit X) = 1 := by
  refine Units.ext (Matrix.ext fun i j ↦ ?_)
  change ((1 + X.map inr : Matrix n n (DualNumber k)) i j).fst = (1 : Matrix n n k) i j
  rw [Matrix.add_apply, fst_add, Matrix.map_apply, fst_inr, add_zero, Matrix.one_apply,
    Matrix.one_apply]
  split_ifs <;> rfl

/-- An invertible matrix over `k[ε]` reducing to the identity modulo `ε` is `1 + εX`, with `X` its
`ε`-part. -/
theorem dualUnit_map_snd {g : GL n (DualNumber k)} (hg : map (fstHom k k k).toRingHom g = 1) :
    dualUnit ((g : Matrix n n (DualNumber k)).map snd) = g :=
  Units.ext (eq_one_add_map_inr_of_map_fst_eq_one (congrArg Units.val hg)).symm

theorem coe_map_dualUnit {S : Type*} [CommRing S] [Algebra k S] (φ : DualNumber k →ₐ[k] S)
    (X : Matrix n n k) :
    (map φ.toRingHom (dualUnit X) : Matrix n n S) =
      1 + φ DualNumber.eps • X.map (algebraMap k S) := by
  ext i j
  change φ ((1 + X.map inr : Matrix n n (DualNumber k)) i j) = _
  rw [Matrix.add_apply, map_add, Matrix.map_apply, DualNumber.inr_eq_smul_eps, map_smul,
    Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply, Algebra.smul_def, smul_eq_mul, mul_comm,
    Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

theorem map_scale_dualUnit (c : k) (X : Matrix n n k) :
    map (DualNumber.scale c).toRingHom (dualUnit X) = dualUnit (c • X) := by
  refine Units.ext (Matrix.ext fun i j ↦ ?_)
  change DualNumber.scale c ((1 + X.map inr : Matrix n n (DualNumber k)) i j) =
    (1 + (c • X).map inr : Matrix n n (DualNumber k)) i j
  rw [Matrix.add_apply, Matrix.add_apply, map_add, Matrix.map_apply, Matrix.map_apply,
    DualNumber.scale_inr, Matrix.one_apply, Matrix.smul_apply, smul_eq_mul]
  split_ifs <;> simp

private theorem one_add_mul_one_add_mul_one_sub_mul_one_sub {A : Type*} [Ring A] {P Q : A}
    (hP : P * P = 0) (hQ : Q * Q = 0) (hPQP : P * Q * P = 0) (hQPQ : Q * P * Q = 0) :
    (1 + P) * (1 + Q) * (1 - P) * (1 - Q) = 1 + (P * Q - Q * P) := by
  have h : (1 + P) * (1 + Q) * (1 - P) * (1 - Q) = 1 + (P * Q - Q * P) - P * P - Q * Q +
      P * P * Q + Q * P * Q - P * Q * P - P * (Q * Q) + P * Q * P * Q := by
    noncomm_ring
  rw [h, hP, hQ, hPQP, hQPQ]
  simp only [zero_mul, mul_zero, sub_zero, add_zero]

/-- The commutator of `1 + aX` and `1 + bY` is `1 + ab⁅X, Y⁆` when `a² = b² = 0`: for algebra
homomorphisms `φ₁, φ₂, ψ : k[ε] → S` with `ψ(ε) = φ₁(ε)φ₂(ε)`, the commutator of the images of
`1 + εX` under `φ₁` and of `1 + εY` under `φ₂` is the image of `1 + ε⁅X, Y⁆` under `ψ`. -/
theorem map_dualUnit_commutator {S : Type*} [CommRing S] [Algebra k S]
    {φ₁ φ₂ ψ : DualNumber k →ₐ[k] S} (hψ : ψ DualNumber.eps = φ₁ DualNumber.eps * φ₂ DualNumber.eps)
    (X Y : Matrix n n k) :
    map φ₁.toRingHom (dualUnit X) * map φ₂.toRingHom (dualUnit Y) *
        (map φ₁.toRingHom (dualUnit X))⁻¹ * (map φ₂.toRingHom (dualUnit Y))⁻¹ =
      map ψ.toRingHom (dualUnit ⁅X, Y⁆) := by
  have hsq (φ : DualNumber k →ₐ[k] S) : φ DualNumber.eps * φ DualNumber.eps = 0 := by
    rw [← map_mul, DualNumber.eps_mul_eps, map_zero]
  set a := φ₁ DualNumber.eps
  set b := φ₂ DualNumber.eps
  ext1
  simp only [← map_inv, ← dualUnit_neg, Units.val_mul, coe_map_dualUnit, hψ, Ring.lie_def]
  have hneg (Z : Matrix n n k) : (-Z).map (algebraMap k S) = -Z.map (algebraMap k S) := by
    simp only [← RingHom.mapMatrix_apply, map_neg]
  have hsub : (X * Y - Y * X).map (algebraMap k S) =
      X.map (algebraMap k S) * Y.map (algebraMap k S) -
        Y.map (algebraMap k S) * X.map (algebraMap k S) := by
    simp only [← RingHom.mapMatrix_apply, map_sub, map_mul]
  rw [hneg, hneg, hsub, smul_neg, smul_neg, ← sub_eq_add_neg, ← sub_eq_add_neg]
  set X' := X.map (algebraMap k S)
  set Y' := Y.map (algebraMap k S)
  have hab : a * b * a = 0 := by rw [mul_right_comm, hsq, zero_mul]
  have hba : b * a * b = 0 := by rw [mul_right_comm, hsq, zero_mul]
  rw [one_add_mul_one_add_mul_one_sub_mul_one_sub (by rw [smul_mul_smul_comm, hsq, zero_smul])
    (by rw [smul_mul_smul_comm, hsq, zero_smul])
    (by rw [smul_mul_smul_comm, smul_mul_smul_comm, hab, zero_smul])
    (by rw [smul_mul_smul_comm, smul_mul_smul_comm, hba, zero_smul]),
    smul_mul_smul_comm, smul_mul_smul_comm, mul_comm b a, smul_sub]

/-- The map `k[ε] → k[ε, δ] = k[ε][δ]`, `ε ↦ ε`. -/
private def epsLeft : DualNumber k →ₐ[k] DualNumber (DualNumber k) :=
  DualNumber.lift ⟨(Algebra.ofId k _, inl DualNumber.eps),
    by rw [← inl_mul, DualNumber.eps_mul_eps, inl_zero],
    fun _ ↦ Commute.all (S := DualNumber (DualNumber k)) _ _⟩

/-- The map `k[ε] → k[ε, δ]`, `ε ↦ δ`. -/
private def epsRight : DualNumber k →ₐ[k] DualNumber (DualNumber k) :=
  DualNumber.lift ⟨(Algebra.ofId k _, DualNumber.eps), DualNumber.eps_mul_eps,
    fun _ ↦ Commute.all (S := DualNumber (DualNumber k)) _ _⟩

/-- The injective map `k[ε] → k[ε, δ]`, `ε ↦ εδ`. -/
private def epsProd : DualNumber k →ₐ[k] DualNumber (DualNumber k) :=
  DualNumber.lift ⟨(Algebra.ofId k _, inr DualNumber.eps), inr_mul_inr _ _ _,
    fun _ ↦ Commute.all (S := DualNumber (DualNumber k)) _ _⟩

private theorem epsProd_eps :
    epsProd (k := k) DualNumber.eps = epsLeft DualNumber.eps * epsRight DualNumber.eps := by
  rw [epsProd, epsLeft, epsRight, DualNumber.lift_apply_eps, DualNumber.lift_apply_eps,
    DualNumber.lift_apply_eps]
  change inr _ = inl _ * inr 1
  rw [inl_mul_inr, smul_eq_mul, mul_one]

private theorem epsProd_injective : Function.Injective (epsProd (k := k)) := by
  intro x y h
  have h' (z : DualNumber k) : epsProd z = inl (inl z.fst) + inr (inr z.snd) := by
    rw [epsProd, DualNumber.lift_apply_apply]
    ext <;> simp [Algebra.ofId_apply, algebraMap_eq_inl']
  rw [h', h'] at h
  exact TrivSqZeroExt.ext (by simpa using congrArg (fun z ↦ z.fst.fst) h)
    (by simpa using congrArg (fun z ↦ z.snd.snd) h)

end DualUnit

section Lie

variable {n : Type*} [Fintype n] [DecidableEq n] {k : Type*} [CommRing k]
  {I : Ideal (CoordinateRing n k)} [I.IsHopfIdeal k]

theorem dualUnit_add_mem {X Y : Matrix n n k} (hX : dualUnit X ∈ zeroLocus I (DualNumber k))
    (hY : dualUnit Y ∈ zeroLocus I (DualNumber k)) :
    dualUnit (X + Y) ∈ zeroLocus I (DualNumber k) := by
  rw [dualUnit_add]
  exact mul_mem hX hY

theorem dualUnit_zero_mem : dualUnit (0 : Matrix n n k) ∈ zeroLocus I (DualNumber k) := by
  rw [dualUnit_zero]
  exact one_mem _

theorem dualUnit_smul_mem (c : k) {X : Matrix n n k}
    (hX : dualUnit X ∈ zeroLocus I (DualNumber k)) :
    dualUnit (c • X) ∈ zeroLocus I (DualNumber k) := by
  rw [← map_scale_dualUnit]
  exact map_mem_zeroLocus _ hX

/-- The tangent space at the identity of `V(I)` is closed under the commutator bracket: over
`S = k[ε, δ]/(ε², δ²)`, the commutator of the points `1 + εX` and `1 + δY` of `V(I)` is the point
`1 + εδ⁅X, Y⁆` (`map_dualUnit_commutator`), which comes from the point `1 + ε⁅X, Y⁆` along the
injective map `k[ε] → S`, `ε ↦ εδ`. (blueprint: `sk-d-tangent`) -/
theorem dualUnit_bracket_mem {X Y : Matrix n n k}
    (hX : dualUnit X ∈ zeroLocus I (DualNumber k)) (hY : dualUnit Y ∈ zeroLocus I (DualNumber k)) :
    dualUnit ⁅X, Y⁆ ∈ zeroLocus I (DualNumber k) := by
  have hX' := map_mem_zeroLocus (S := DualNumber (DualNumber k)) epsLeft hX
  have hY' := map_mem_zeroLocus (S := DualNumber (DualNumber k)) epsRight hY
  have h := mul_mem (mul_mem (mul_mem hX' hY') (inv_mem hX')) (inv_mem hY')
  rwa [map_dualUnit_commutator epsProd_eps, map_mem_zeroLocus_iff epsProd_injective] at h

/-- If the commutators of `V(I)` lie in `V(J)` on points with values in `k[ε, δ]/(ε², δ²)`, then
the bracket of two tangent vectors of `V(I)` is a tangent vector of `V(J)`, by the same commutator
computation as in `dualUnit_bracket_mem`. -/
theorem dualUnit_bracket_mem_of_commutator_le {J : Ideal (CoordinateRing n k)} [J.IsHopfIdeal k]
    (hIJ : ⁅zeroLocus I (DualNumber (DualNumber k)), zeroLocus I (DualNumber (DualNumber k))⁆ ≤
      zeroLocus J (DualNumber (DualNumber k)))
    {X Y : Matrix n n k} (hX : dualUnit X ∈ zeroLocus I (DualNumber k))
    (hY : dualUnit Y ∈ zeroLocus I (DualNumber k)) :
    dualUnit ⁅X, Y⁆ ∈ zeroLocus J (DualNumber k) := by
  have h := hIJ (Subgroup.commutator_mem_commutator
    (map_mem_zeroLocus (S := DualNumber (DualNumber k)) epsLeft hX)
    (map_mem_zeroLocus (S := DualNumber (DualNumber k)) epsRight hY))
  rwa [commutatorElement_def, map_dualUnit_commutator epsProd_eps,
    map_mem_zeroLocus_iff epsProd_injective] at h

variable (I) in
/-- The Lie algebra `Lie(G) = T_1 G ⊆ gl_n` of the closed subgroup scheme `G = V(I)` of `GL_n`:
the matrices `X` with `1 + εX ∈ G(k[ε])`, with the commutator bracket `⁅X, Y⁆ = XY - YX`.
(blueprint: `sk-d-tangent`) -/
noncomputable def lieAlgebra : LieSubalgebra k (Matrix n n k) where
  carrier := {X | dualUnit X ∈ zeroLocus I (DualNumber k)}
  add_mem' := dualUnit_add_mem
  zero_mem' := dualUnit_zero_mem
  smul_mem' := dualUnit_smul_mem
  lie_mem' := dualUnit_bracket_mem

@[simp]
theorem mem_lieAlgebra {X : Matrix n n k} :
    X ∈ lieAlgebra I ↔ dualUnit X ∈ zeroLocus I (DualNumber k) :=
  Iff.rfl

theorem lieAlgebra_anti {J : Ideal (CoordinateRing n k)} [J.IsHopfIdeal k] (h : I ≤ J) :
    lieAlgebra J ≤ lieAlgebra I :=
  fun _ hX ↦ zeroLocus_anti h hX

/-- If the commutators of `V(I)` lie in `V(J)` on points with values in `k[ε, δ]/(ε², δ²)`, then
`⁅Lie V(I), Lie V(I)⁆ ⊆ Lie V(J)`. -/
theorem lie_mem_lieAlgebra_of_commutator_le {J : Ideal (CoordinateRing n k)} [J.IsHopfIdeal k]
    (hIJ : ⁅zeroLocus I (DualNumber (DualNumber k)), zeroLocus I (DualNumber (DualNumber k))⁆ ≤
      zeroLocus J (DualNumber (DualNumber k)))
    {X Y : Matrix n n k} (hX : X ∈ lieAlgebra I) (hY : Y ∈ lieAlgebra I) :
    ⁅X, Y⁆ ∈ lieAlgebra J :=
  dualUnit_bracket_mem_of_commutator_le hIJ hX hY

theorem lieAlgebra_bot : lieAlgebra (⊥ : Ideal (CoordinateRing n k)) = ⊤ := by
  ext X
  simp only [mem_lieAlgebra, LieSubalgebra.mem_top, iff_true]
  intro a ha
  rw [Ideal.mem_bot.1 ha, map_zero]

theorem map_algebraMap_mul_dualUnit_mul (g : GL n k) (X : Matrix n n k) :
    map (algebraMap k (DualNumber k)) g * dualUnit X * map (algebraMap k (DualNumber k)) g⁻¹ =
      dualUnit ((g : Matrix n n k) * X * ((g⁻¹ : GL n k) : Matrix n n k)) := by
  have hinr (Y : Matrix n n k) : Y.map (inr : k → DualNumber k) =
      (DualNumber.eps : DualNumber k) • Y.map (algebraMap k (DualNumber k)) := by
    ext i j : 1
    rw [Matrix.map_apply, Matrix.smul_apply, Matrix.map_apply, DualNumber.inr_eq_smul_eps,
      Algebra.smul_def, smul_eq_mul, mul_comm]
  have hG (h : GL n k) : ((map (algebraMap k (DualNumber k)) h : GL n (DualNumber k)) :
      Matrix n n (DualNumber k)) = (h : Matrix n n k).map (algebraMap k (DualNumber k)) :=
    rfl
  ext1
  rw [Units.val_mul, Units.val_mul, coe_dualUnit, coe_dualUnit, mul_add, mul_one, add_mul,
    ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one, hG, hG, hinr, hinr,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.map_mul, Matrix.map_mul]

/-- The Lie algebra of `G` is stable under the adjoint action `Ad(g) X = g X g⁻¹` of `G(k)`.
(blueprint: `sk-d-tangent`) -/
theorem conj_mem_lieAlgebra {g : GL n k} (hg : g ∈ zeroLocus I k) {X : Matrix n n k}
    (hX : X ∈ lieAlgebra I) :
    (g : Matrix n n k) * X * ((g⁻¹ : GL n k) : Matrix n n k) ∈ lieAlgebra I := by
  rw [mem_lieAlgebra, ← map_algebraMap_mul_dualUnit_mul]
  have hg' := map_mem_zeroLocus (Algebra.ofId k (DualNumber k)) hg
  have hg'' := map_mem_zeroLocus (Algebra.ofId k (DualNumber k)) (inv_mem hg)
  exact mul_mem (mul_mem hg' hX) hg''

end Lie

section TangentGroup

variable {n : Type u} [Fintype n] [DecidableEq n] {k : Type u} [CommRing k]
  {I : Ideal (CoordinateRing n k)} [I.IsHopfIdeal k]

variable (I) in
/-- The point `1 + εX` of `V(I)` with values in `k[ε]`, for `X ∈ lieAlgebra I`, as a tangent
vector of the group scheme `V(I)`. -/
noncomputable def toTangentGroup :
    Multiplicative (lieAlgebra I) →* tangentGroup (subgroupScheme I) where
  toFun X := ⟨zeroLocusMulEquiv I (DualNumber k) ⟨dualUnit X.toAdd, X.toAdd.2⟩, by
    rw [mem_tangentGroup, pointsMap_apply, ← zeroLocusMulEquiv_map]
    convert (zeroLocusMulEquiv I k).map_one
    exact Subtype.ext (map_fstHom_dualUnit _)⟩
  map_one' := Subtype.ext <|
    (congrArg (zeroLocusMulEquiv I (DualNumber k)) (Subtype.ext dualUnit_zero)).trans
      (zeroLocusMulEquiv I (DualNumber k)).map_one
  map_mul' X Y := by
    refine Subtype.ext ?_
    rw [Subgroup.coe_mul, ← (zeroLocusMulEquiv I (DualNumber k)).map_mul]
    exact congrArg (zeroLocusMulEquiv I (DualNumber k))
      (Subtype.ext (dualUnit_add (X.toAdd : Matrix n n k) Y.toAdd))

theorem coe_toTangentGroup_apply (X : lieAlgebra I) :
    (toTangentGroup I (.ofAdd X) : points (subgroupScheme I) (DualNumber k)) =
      zeroLocusMulEquiv I (DualNumber k) ⟨dualUnit X, X.2⟩ :=
  rfl

theorem bijective_toTangentGroup : Function.Bijective (toTangentGroup I) := by
  refine ⟨fun X Y h ↦ ?_, fun x ↦ ?_⟩
  · have h₁ : zeroLocusMulEquiv I (DualNumber k) ⟨dualUnit X.toAdd, X.toAdd.2⟩ =
        zeroLocusMulEquiv I (DualNumber k) ⟨dualUnit Y.toAdd, Y.toAdd.2⟩ :=
      congrArg Subtype.val h
    have h₂ := congrArg Subtype.val ((zeroLocusMulEquiv I (DualNumber k)).injective h₁)
    exact Multiplicative.toAdd.injective (Subtype.ext (dualUnit_injective h₂))
  · obtain ⟨x, hx⟩ := x
    obtain ⟨g, rfl⟩ := (zeroLocusMulEquiv I (DualNumber k)).surjective x
    have hg : zeroLocus.map I (fstHom k k k) g = 1 := by
      apply (zeroLocusMulEquiv I k).injective
      rw [zeroLocusMulEquiv_map, (zeroLocusMulEquiv I k).map_one, ← pointsMap_apply]
      exact (mem_tangentGroup _).1 hx
    have hg' : dualUnit (((g : GL n (DualNumber k)) : Matrix n n (DualNumber k)).map snd) = g :=
      dualUnit_map_snd (congrArg Subtype.val hg)
    have hX : ((g : GL n (DualNumber k)) : Matrix n n (DualNumber k)).map snd ∈ lieAlgebra I := by
      rw [mem_lieAlgebra, hg']
      exact g.2
    exact ⟨.ofAdd ⟨_, hX⟩,
      Subtype.ext (congrArg (zeroLocusMulEquiv I (DualNumber k)) (Subtype.ext hg'))⟩

variable (I) in
/-- The tangent group of the group scheme `G = V(I)` is the additive group of its Lie algebra
`lieAlgebra I`: a matrix `X ∈ lieAlgebra I` corresponds to the point `φ : Spec k[ε] ⟶ V(I)` of
`zeroLocusMulEquiv` with matrix `1 + εX`, that is the unique `φ` making the diagram
```
Spec k ──(ε ↦ 0)──▶ Spec k[ε] ──φ──▶ V(I) ──ι──▶ GL_n
   ╲                                               ▲
    ╲──────────────────── 1 ──────────────────────╯
```
commute, with `φ ≫ ι` the point `1 + εX` of `GL_n`. (blueprint: `sk-d-tangent`) -/
noncomputable def tangentGroupMulEquiv :
    tangentGroup (subgroupScheme I) ≃* Multiplicative (lieAlgebra I) :=
  (MulEquiv.ofBijective _ bijective_toTangentGroup).symm

@[simp]
theorem coe_tangentGroupMulEquiv_symm_apply (X : lieAlgebra I) :
    ((tangentGroupMulEquiv I).symm (.ofAdd X) : points (subgroupScheme I) (DualNumber k)) =
      zeroLocusMulEquiv I (DualNumber k) ⟨dualUnit X, X.2⟩ :=
  rfl

end TangentGroup

section Cartier

variable {n : Type*} [Fintype n] [DecidableEq n] {k : Type*} [Field k]
  (I : Ideal (CoordinateRing n k)) [I.IsHopfIdeal k]

theorem lieAlgebra_identityComponent_le [IsAlgClosed k] :
    lieAlgebra (identityComponent I) ≤ lieAlgebra I :=
  lieAlgebra_anti (le_identityComponent I)

/-- In characteristic zero, every tangent vector of `G` is tangent to the identity component.

`CharZero` is needed because `identityComponent I` is the ideal of the *reduced* identity
component. Proof sketch (not formalised): by Cartier's theorem `V(I)` is reduced, so the
scheme-theoretic identity component `G°`, an open subgroup scheme with the same tangent space at
`1` as `G`, is cut out by `identityComponent I`. Alternatively, compare dimensions with
`finrank_lieAlgebra_eq_ringKrullDim` for both ideals, using `dim G° = dim G`.
(blueprint: `sk-i-cartier`) -/
theorem lieAlgebra_le_lieAlgebra_identityComponent [IsAlgClosed k] [CharZero k] :
    lieAlgebra I ≤ lieAlgebra (identityComponent I) := by
  sorry

/-- Over an algebraically closed field of characteristic zero, the Lie algebra of an algebraic
group is the Lie algebra of its identity component. (blueprint: `sk-i-cartier`) -/
theorem lieAlgebra_identityComponent [IsAlgClosed k] [CharZero k] :
    lieAlgebra (identityComponent I) = lieAlgebra I :=
  le_antisymm (lieAlgebra_identityComponent_le I) (lieAlgebra_le_lieAlgebra_identityComponent I)

/-- Cartier's theorem, Lie algebra form: over a field of characteristic zero, the Lie algebra of
a closed subgroup scheme `V(I)` has dimension the Krull dimension of its coordinate ring.

Proof sketch (not formalised): `lieAlgebra I` is the tangent space `Hom_k(𝔪/𝔪², k)` at the
identity of `k[GL_n] ⧸ I`, where `𝔪` is the kernel of the counit; in characteristic zero
`V(I)` is smooth (`AlgebraicGeometry.smooth_of_grpObj_of_charZero`), so this tangent space has
the dimension of `V(I)`. (blueprint: `sk-i-cartier`) -/
theorem finrank_lieAlgebra_eq_ringKrullDim [CharZero k] :
    (Module.finrank k (lieAlgebra I) : WithBot ℕ∞) = ringKrullDim (CoordinateRing n k ⧸ I) := by
  sorry

end Cartier

section RationalHom

variable {n : Type u} [Fintype n] [DecidableEq n] {k : Type u} [CommRing k]
  (I : Ideal (CoordinateRing n k)) [I.IsHopfIdeal k]

/-- A rational representation of the closed subgroup scheme `V(I)` of `GL_n` on `k^m`: a
homomorphism of group schemes `V(I) ⟶ GL_m`, given by the bialgebra homomorphism of coordinate
rings `k[GL_m] → k[GL_n] ⧸ I`. (blueprint: `sk-d-tangent`) -/
abbrev RationalHom (m : Type u) [Fintype m] [DecidableEq m] :=
  CoordinateRing m k →ₐc[k] CoordinateRing n k ⧸ I

variable {I} {m : Type u} [Fintype m] [DecidableEq m]

namespace RationalHom

/-- The homomorphism of group schemes `V(I) ⟶ GL_m` of a rational representation `r`: the
morphism `Spec r` in the square
```
Spec (k[GL_n] ⧸ I) ──Spec r──▶ Spec k[GL_m]
          ╲                       ╱
           ╲──▶   Spec k   ◀────╱
```
over `Spec k`. -/
noncomputable def toSchemeHom (r : RationalHom I m) : subgroupScheme I ⟶ GL(m; k) :=
  (Spec.map (CommRingCat.ofHom
    (r : CoordinateRing m k →ₐ[k] CoordinateRing n k ⧸ I).toRingHom)).asOver (Spec (.of k))

instance (r : RationalHom I m) : IsMonHom r.toSchemeHom :=
  inferInstanceAs (IsMonHom ((bialgSpec (.of k)).map (CommBialgCat.ofHom r).op).hom)

/-- A rational representation of `V(I)` on `R`-points: the group homomorphism `G(R) → GL m R`
given by composing points `Spec R ⟶ V(I)` with `r.toSchemeHom`. (blueprint: `sk-d-tangent`) -/
noncomputable def points (r : RationalHom I m) (R : Type u) [CommRing R] [Algebra k R] :
    zeroLocus I R →* GL m R :=
  (GeneralLinearGroup.homMulEquiv m k R).toMonoidHom.comp
    ((IsMonHom.monoidHom r.toSchemeHom _).comp (zeroLocusMulEquiv I R).toMonoidHom)

theorem points_apply (r : RationalHom I m) {R : Type u} [CommRing R] [Algebra k R]
    (g : zeroLocus I R) :
    r.points R g = GeneralLinearGroup.homMulEquiv m k R (zeroLocusMulEquiv I R g ≫ r.toSchemeHom) :=
  rfl

/-- A rational representation commutes with base change of points along `R → S`. -/
theorem map_points (r : RationalHom I m) {R S : Type u} [CommRing R] [Algebra k R] [CommRing S]
    [Algebra k S] (φ : R →ₐ[k] S) (g : zeroLocus I R) :
    map φ.toRingHom (r.points R g) = r.points S (zeroLocus.map I φ g) := by
  rw [points_apply, points_apply, zeroLocusMulEquiv_map, Category.assoc,
    GeneralLinearGroup.homMulEquiv_specMap_comp]

theorem map_fstHom_points_dualUnit (r : RationalHom I m) (X : lieAlgebra I) :
    map (fstHom k k k).toRingHom (r.points (DualNumber k) ⟨dualUnit X, X.2⟩) = 1 := by
  rw [map_points]
  convert map_one (r.points k)
  exact Subtype.ext (map_fstHom_dualUnit _)

theorem map_fst_coe_points_dualUnit (r : RationalHom I m) (X : lieAlgebra I) :
    ((r.points (DualNumber k) ⟨dualUnit X, X.2⟩ : GL m (DualNumber k)) :
      Matrix m m (DualNumber k)).map fst = 1 :=
  congrArg Units.val (map_fstHom_points_dualUnit r X)

/-- The differential `dr : Lie(G) → gl_m` of a rational representation `r`: the `ε`-coefficient
of `r(1 + εX)`. It is a homomorphism of Lie algebras: differentiating the commutator of `1 + εX`
and `1 + δY` over `k[ε, δ]/(ε², δ²)` gives `dr⁅X, Y⁆ = ⁅dr X, dr Y⁆`.
(blueprint: `sk-d-tangent`) -/
noncomputable def differential (r : RationalHom I m) : lieAlgebra I →ₗ⁅k⁆ Matrix m m k where
  toFun X := ((r.points (DualNumber k) ⟨dualUnit X, X.2⟩ : GL m (DualNumber k)) :
    Matrix m m (DualNumber k)).map snd
  map_add' X Y := by
    have h : (⟨dualUnit (X + Y : lieAlgebra I), (X + Y).2⟩ : zeroLocus I (DualNumber k)) =
        ⟨dualUnit X, X.2⟩ * ⟨dualUnit Y, Y.2⟩ := Subtype.ext (dualUnit_add _ _)
    simp only [h, map_mul, Units.val_mul]
    exact map_snd_mul_of_map_fst_eq_one (map_fst_coe_points_dualUnit r X)
      (map_fst_coe_points_dualUnit r Y)
  map_smul' c X := by
    have h : (⟨dualUnit (c • X : lieAlgebra I), (c • X).2⟩ : zeroLocus I (DualNumber k)) =
        zeroLocus.map I (DualNumber.scale c) ⟨dualUnit X, X.2⟩ :=
      Subtype.ext (map_scale_dualUnit c (X : Matrix n n k)).symm
    simp only [h, ← map_points]
    ext i j
    exact DualNumber.snd_scale c _
  map_lie' {X Y} := by
    have hd (Z : lieAlgebra I) : r.points (DualNumber k) ⟨dualUnit Z, Z.2⟩ =
        dualUnit (((r.points (DualNumber k) ⟨dualUnit Z, Z.2⟩ : GL m (DualNumber k)) :
          Matrix m m (DualNumber k)).map snd) :=
      (dualUnit_map_snd (map_fstHom_points_dualUnit r Z)).symm
    have hcomm : zeroLocus.map (S := DualNumber (DualNumber k)) I epsLeft ⟨dualUnit X, X.2⟩ *
        zeroLocus.map (S := DualNumber (DualNumber k)) I epsRight ⟨dualUnit Y, Y.2⟩ *
        (zeroLocus.map (S := DualNumber (DualNumber k)) I epsLeft ⟨dualUnit X, X.2⟩)⁻¹ *
        (zeroLocus.map (S := DualNumber (DualNumber k)) I epsRight ⟨dualUnit Y, Y.2⟩)⁻¹ =
          zeroLocus.map (S := DualNumber (DualNumber k)) I epsProd ⟨dualUnit ⁅X, Y⁆, ⁅X, Y⁆.2⟩ :=
      Subtype.ext (by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, zeroLocus.coe_map_apply]
        exact map_dualUnit_commutator epsProd_eps _ _)
    have h := congrArg (r.points (DualNumber (DualNumber k))) hcomm
    simp only [map_mul, map_inv, ← map_points] at h
    have hinj : Function.Injective
        (map (n := m) (S := DualNumber (DualNumber k)) (epsProd (k := k)).toRingHom) :=
      fun a b hab ↦ Units.ext (Matrix.map_injective epsProd_injective (congrArg Units.val hab))
    apply dualUnit_injective
    apply hinj
    rw [← hd ⁅X, Y⁆, ← map_dualUnit_commutator epsProd_eps, ← hd X, ← hd Y]
    exact h.symm

@[simp]
theorem differential_apply (r : RationalHom I m) (X : lieAlgebra I) :
    r.differential X = ((r.points (DualNumber k) ⟨dualUnit X, X.2⟩ : GL m (DualNumber k)) :
      Matrix m m (DualNumber k)).map snd :=
  rfl

/-- A rational representation maps `1 + εX` to `1 + ε dr(X)`. -/
theorem points_dualUnit (r : RationalHom I m) (X : lieAlgebra I) :
    r.points (DualNumber k) ⟨dualUnit X, X.2⟩ = dualUnit (r.differential X) :=
  (dualUnit_map_snd (map_fstHom_points_dualUnit r X)).symm

/-- The differential of a rational representation `r` is the differential `tangentGroupMap` of
the homomorphism of group schemes `r.toSchemeHom : V(I) ⟶ GL_m`, read through
`tangentGroupMulEquiv` and `GeneralLinearGroup.homMulEquiv`. (blueprint: `sk-d-tangent`) -/
theorem homMulEquiv_tangentGroupMap (r : RationalHom I m) (X : lieAlgebra I) :
    GeneralLinearGroup.homMulEquiv m k (DualNumber k)
        (tangentGroupMap r.toSchemeHom ((tangentGroupMulEquiv I).symm (.ofAdd X))) =
      dualUnit (r.differential X) :=
  points_dualUnit r X

/-- If a subspace `U ⊆ k^m` is stable under the dual-number points of `G` acting by `r`, that is
the `ε`-part of `r(g) v` lies in `U` for `g ∈ G(k[ε])` and `v ∈ U`, then `U` is stable under the
differential of `r`. -/
theorem le_comap_toLin'_differential (r : RationalHom I m) (U : Submodule k (m → k))
    (hU : ∀ g : zeroLocus I (DualNumber k), ∀ v ∈ U,
      snd ∘ ((r.points (DualNumber k) g : Matrix m m (DualNumber k)) *ᵥ (inl ∘ v)) ∈ U)
    (X : lieAlgebra I) : U ≤ U.comap (Matrix.toLin' (r.differential X)) := by
  intro v hv
  have h := hU ⟨dualUnit X, X.2⟩ v hv
  rw [points_dualUnit, coe_dualUnit] at h
  rw [Submodule.mem_comap, Matrix.toLin'_apply]
  convert h using 1
  ext i
  simp [Matrix.add_mulVec, Matrix.mulVec, dotProduct, snd_sum]

end RationalHom

end RationalHom

section Comparison

variable {n : Type u} [Fintype n] [DecidableEq n] {k : Type u} [Field k]
  {I : Ideal (CoordinateRing n k)} [I.IsHopfIdeal k] {m : Type u} [Fintype m] [DecidableEq m]

/-- For a reduced `G` over an algebraically closed field, a subspace stable under `G(k)` is stable
under the points of `G` with values in the dual numbers.

Proof sketch (not formalised): the condition `r(g) U ⊆ U` is cut out by equations on `G`; they
vanish on `G(k)`, which is dense in the reduced `G`, hence they vanish on `G`, so `r(g)` preserves
`U ⊗ k[ε]` for every `g ∈ G(k[ε])`. (blueprint: `sk-p-comparison`) -/
theorem RationalHom.snd_mulVec_mem_of_le_comap [IsAlgClosed k] (hI : I.IsRadical)
    (r : RationalHom I m) (U : Submodule k (m → k))
    (hU : ∀ g : zeroLocus I k, U ≤ U.comap (Matrix.toLin' (r.points k g)))
    (g : zeroLocus I (DualNumber k)) {v : m → k} (hv : v ∈ U) :
    snd ∘ ((r.points (DualNumber k) g : Matrix m m (DualNumber k)) *ᵥ (inl ∘ v)) ∈ U := by
  sorry

/-- Over an algebraically closed field of characteristic zero, a subspace stable under the
differential of a rational representation of a connected group `G` is stable under `G(k)`.

Proof sketch (not formalised): replacing `G` by its image `r(G) ⊆ GL_m` reduces this to the
defining representation, using that `dr` is surjective onto `Lie(r(G))` in characteristic zero;
the stabiliser of `U` in `r(G)` is a closed subgroup whose Lie algebra is all of `Lie(r(G))`, so it
is the whole connected group `r(G)` by `lieAlgebra_identityComponent` and
`finrank_lieAlgebra_eq_ringKrullDim`. (blueprint: `sk-p-comparison`) -/
theorem RationalHom.le_comap_toLin'_points [IsAlgClosed k] [CharZero k] (hconn : IsConnected I)
    (r : RationalHom I m) (U : Submodule k (m → k))
    (hU : ∀ X : lieAlgebra I, U ≤ U.comap (Matrix.toLin' (r.differential X)))
    (g : zeroLocus I k) : U ≤ U.comap (Matrix.toLin' (r.points k g)) := by
  sorry

/-- The group–Lie comparison for invariant subspaces: over an algebraically closed field of
characteristic zero, a subspace is stable under a connected algebraic group acting by a rational
representation if and only if it is stable under the differential of the representation.
(blueprint: `sk-p-comparison`) -/
theorem invariant_iff_differential_invariant [IsAlgClosed k] [CharZero k] (hconn : IsConnected I)
    (r : RationalHom I m) (U : Submodule k (m → k)) :
    (∀ g : zeroLocus I k, U ≤ U.comap (Matrix.toLin' (r.points k g))) ↔
      ∀ X : lieAlgebra I, U ≤ U.comap (Matrix.toLin' (r.differential X)) :=
  ⟨fun h ↦ r.le_comap_toLin'_differential U fun g _ hv ↦
      r.snd_mulVec_mem_of_le_comap hconn.isRadical U h g hv,
    fun h ↦ r.le_comap_toLin'_points hconn U h⟩

/-- The Lie algebra of the centre of a reduced `G` over an algebraically closed field is contained
in the centre of the Lie algebra of `G`.

Proof sketch (not formalised): `G(k)` is dense in `G`, so the reduced centre `Z(G)` centralises
`G` scheme-theoretically. For `Z ∈ Lie(Z(G))` and `Y ∈ Lie(G)`, the point `1 + εZ` therefore
commutes with `1 + δY` over `k[ε, δ]/(ε², δ²)`, so `1 + εδ⁅Z, Y⁆ = 1` by `map_dualUnit_commutator`,
that is `⁅Z, Y⁆ = 0`. (blueprint: `sk-p-comparison`) -/
theorem lieAlgebra_center_le [IsAlgClosed k] (hI : I.IsRadical) :
    lieAlgebra (center I) ≤
      (LieAlgebra.center k (lieAlgebra I) : LieSubalgebra k (lieAlgebra I)).map
        (lieAlgebra I).incl := by
  sorry

/-- In characteristic zero, the centre of the Lie algebra of a connected group `G` is contained
in the Lie algebra of the centre of `G`.

Proof sketch (not formalised): the centre of a connected `G` is the kernel of the adjoint
representation `Ad : G → GL(Lie G)`, whose differential is `ad`; in characteristic zero the Lie
algebra of the kernel is the kernel `𝔷(Lie G)` of the differential. (blueprint: `sk-p-comparison`)
-/
theorem le_lieAlgebra_center [IsAlgClosed k] [CharZero k] (hconn : IsConnected I) :
    (LieAlgebra.center k (lieAlgebra I) : LieSubalgebra k (lieAlgebra I)).map
        (lieAlgebra I).incl ≤
      lieAlgebra (center I) := by
  sorry

/-- The group–Lie comparison for the centre: over an algebraically closed field of characteristic
zero, the Lie algebra of the centre of a connected algebraic group is the centre of its Lie
algebra. (blueprint: `sk-p-comparison`) -/
theorem lieAlgebra_center [IsAlgClosed k] [CharZero k] (hconn : IsConnected I) :
    lieAlgebra (center I) =
      (LieAlgebra.center k (lieAlgebra I) : LieSubalgebra k (lieAlgebra I)).map
        (lieAlgebra I).incl :=
  le_antisymm (lieAlgebra_center_le hconn.isRadical) (le_lieAlgebra_center hconn)

/-- The Lie algebra of the identity component of the centre of a connected algebraic group is the
centre of its Lie algebra, in characteristic zero. (blueprint: `sk-p-comparison`) -/
theorem lieAlgebra_identityComponent_center [IsAlgClosed k] [CharZero k] (hconn : IsConnected I) :
    lieAlgebra (identityComponent (center I)) =
      (LieAlgebra.center k (lieAlgebra I) : LieSubalgebra k (lieAlgebra I)).map
        (lieAlgebra I).incl :=
  (lieAlgebra_identityComponent (center I)).trans (lieAlgebra_center hconn)

end Comparison

end AlgebraicGeometry.GeneralLinearGroup
