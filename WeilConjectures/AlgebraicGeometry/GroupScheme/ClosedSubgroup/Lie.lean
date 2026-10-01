/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Lie.Matrix
public import Mathlib.Algebra.Lie.Subalgebra
public import Mathlib.RingTheory.KrullDimension.Basic
public import WeilConjectures.AlgebraicGeometry.GroupScheme.ClosedSubgroup
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Lie

/-!
# Lie algebras of closed subgroup schemes of `GL_n` and rational representations

For a closed subgroup scheme `G = V(I)` of `GL_n` over a field `k`, the Lie algebra
`Lie(G) = T_1 G ⊆ gl_n` is the space of matrices `X` such that `1 + εX` is a point of `G` with
values in the dual numbers `k[ε] = k[ε]/(ε²)`. With the commutator bracket `⁅X, Y⁆ = XY - YX` it
is a Lie subalgebra of `gl_n`; it is the concrete form of the kernel
`AlgebraicGeometry.GrpObj.lie` of `G(k[ε]) → G(k)`.

A rational representation of `G` on `k^m` is a homomorphism of group schemes `G ⟶ GL_m`, that is
a bialgebra homomorphism `k[GL_m] → k[G]` of coordinate rings. On `R`-points it is a group
homomorphism `G(R) → GL m R`, and its differential `Lie(G) → gl_m` is the `ε`-coefficient of the
image of `1 + εX`.

In characteristic zero, a subspace is stable under a connected group if and only if it is stable
under its Lie algebra, and the Lie algebra of the centre is the centre of the Lie algebra.

## Main definitions

- `Matrix.GeneralLinearGroup.dualUnit`: the invertible matrix `1 + εX` over the dual numbers.
- `Matrix.GeneralLinearGroup.lie`: the Lie algebra of the closed subgroup scheme `V(I)`.
- `Matrix.GeneralLinearGroup.RationalHom`: a rational representation of `V(I)` on `k^m`.
- `Matrix.GeneralLinearGroup.RationalHom.points`: a rational representation on `R`-points.
- `Matrix.GeneralLinearGroup.RationalHom.differential`: the differential of a rational
  representation.

## Main results

- `Matrix.GeneralLinearGroup.dualUnit_add`: differentiating the multiplication of `GL_n` at
  `(1, 1)` gives addition.
- `Matrix.GeneralLinearGroup.lie_identityComponent`,
  `Matrix.GeneralLinearGroup.finrank_lie_eq_ringKrullDim`: the Lie algebra only sees the identity
  component and has the dimension of the group (Cartier's theorem).
- `Matrix.GeneralLinearGroup.invariant_iff_differential_invariant`,
  `Matrix.GeneralLinearGroup.lie_identityComponent_center_eq`: the group–Lie comparison.

## Blueprint

- `sk-d-tangent`: the Lie algebra of a matrix algebraic group, rational representations and their
  differentials.
- `sk-i-cartier`: the Lie algebra clauses of Cartier's theorem.
- `sk-p-comparison`: invariant subspaces and the centre, for the group and for its Lie algebra.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry WithConv
open scoped MonObj

namespace Matrix.GeneralLinearGroup

attribute [local instance 100] LieRing.ofAssociativeRing

variable {n : Type u} [Fintype n] [DecidableEq n] {k : Type u} [Field k]

section DualUnit

omit [DecidableEq n] in
theorem map_inr_mul_map_inr (X Y : Matrix n n k) :
    X.map (TrivSqZeroExt.inr : k → DualNumber k) * Y.map TrivSqZeroExt.inr = 0 := by
  ext i j : 1
  simp [Matrix.mul_apply]

theorem dualUnit_mul_neg (X : Matrix n n k) :
    (1 + X.map (TrivSqZeroExt.inr : k → DualNumber k)) * (1 - X.map TrivSqZeroExt.inr) = 1 := by
  rw [add_mul, one_mul, mul_sub, mul_one, map_inr_mul_map_inr, sub_zero, sub_add_cancel]

theorem neg_mul_dualUnit (X : Matrix n n k) :
    (1 - X.map (TrivSqZeroExt.inr : k → DualNumber k)) * (1 + X.map TrivSqZeroExt.inr) = 1 := by
  rw [sub_mul, one_mul, mul_add, mul_one, map_inr_mul_map_inr, add_zero, add_sub_cancel_right]

/-- The invertible matrix `1 + εX` over the dual numbers `k[ε]`, with inverse `1 - εX`.
(blueprint: `sk-d-tangent`) -/
noncomputable def dualUnit (X : Matrix n n k) : GL n (DualNumber k) :=
  ⟨1 + X.map TrivSqZeroExt.inr, 1 - X.map TrivSqZeroExt.inr, dualUnit_mul_neg X,
    neg_mul_dualUnit X⟩

theorem coe_dualUnit (X : Matrix n n k) :
    (dualUnit X : Matrix n n (DualNumber k)) = 1 + X.map TrivSqZeroExt.inr :=
  rfl

/-- Differentiating the multiplication of `GL_n` at `(1, 1)` gives addition:
`(1 + εX)(1 + εY) = 1 + ε(X + Y)`. (blueprint: `sk-i-cartier`) -/
@[simp]
theorem dualUnit_add (X Y : Matrix n n k) : dualUnit (X + Y) = dualUnit X * dualUnit Y := by
  ext1
  rw [Units.val_mul, coe_dualUnit, coe_dualUnit, coe_dualUnit, add_mul, one_mul, mul_add, mul_one,
    map_inr_mul_map_inr, add_zero, Matrix.map_add _ (TrivSqZeroExt.inr_add k)]
  abel

@[simp]
theorem dualUnit_zero : dualUnit (0 : Matrix n n k) = 1 := by
  ext1
  simp [coe_dualUnit]

theorem map_snd_coe_dualUnit (X : Matrix n n k) :
    (dualUnit X : Matrix n n (DualNumber k)).map TrivSqZeroExt.snd = X := by
  ext i j
  simp [coe_dualUnit, Matrix.one_apply, apply_ite TrivSqZeroExt.snd]

theorem dualUnit_injective : Function.Injective (dualUnit : Matrix n n k → GL n (DualNumber k)) :=
  fun X Y h ↦ by rw [← map_snd_coe_dualUnit X, h, map_snd_coe_dualUnit]

end DualUnit

section Points

variable {R S : Type*} [CommRing R] [Algebra k R] [CommRing S] [Algebra k S]

theorem evalAlgHom_map (φ : R →ₐ[k] S) (g : GL n R) :
    evalAlgHom (k := k) (map φ.toRingHom g) = φ.comp (evalAlgHom g) :=
  algHom_ext fun i j ↦ by simp

/-- An algebra homomorphism `R → S` maps the `R`-points of `V(I)` to its `S`-points. -/
theorem map_mem_zeroLocus {I : Ideal (CoordinateRing n k)} [I.IsHopfIdeal k] (φ : R →ₐ[k] S)
    {g : GL n R} (hg : g ∈ zeroLocus I R) : map φ.toRingHom g ∈ zeroLocus I S := by
  intro a ha
  rw [evalAlgHom_map, AlgHom.comp_apply, hg a ha, map_zero]

end Points

section Lie

variable (I : Ideal (CoordinateRing n k)) [I.IsHopfIdeal k]

/-- The algebra endomorphism `ε ↦ cε` of the dual numbers. -/
noncomputable def dualNumberScale (c : k) : DualNumber k →ₐ[k] DualNumber k :=
  TrivSqZeroExt.map (c • LinearMap.id)

theorem dualNumberScale_inr (c x : k) :
    dualNumberScale c (TrivSqZeroExt.inr x) = TrivSqZeroExt.inr (c * x) := by
  rw [dualNumberScale, TrivSqZeroExt.map_inr]
  rfl

theorem map_dualNumberScale_dualUnit (c : k) (X : Matrix n n k) :
    map (dualNumberScale c).toRingHom (dualUnit X) = dualUnit (c • X) := by
  refine Units.ext (Matrix.ext fun i j ↦ ?_)
  change dualNumberScale c ((1 + X.map TrivSqZeroExt.inr : Matrix n n (DualNumber k)) i j) =
    (1 + (c • X).map TrivSqZeroExt.inr : Matrix n n (DualNumber k)) i j
  rw [Matrix.add_apply, Matrix.add_apply, map_add, Matrix.map_apply, Matrix.map_apply,
    dualNumberScale_inr, Matrix.one_apply, Matrix.smul_apply, smul_eq_mul]
  split_ifs <;> simp

variable {I}

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
  rw [← map_dualNumberScale_dualUnit]
  exact map_mem_zeroLocus _ hX

/-- The tangent space at the identity of `V(I)` is closed under the commutator bracket.
(blueprint: `sk-d-tangent`) -/
theorem dualUnit_lie_mem {X Y : Matrix n n k} (hX : dualUnit X ∈ zeroLocus I (DualNumber k))
    (hY : dualUnit Y ∈ zeroLocus I (DualNumber k)) :
    dualUnit ⁅X, Y⁆ ∈ zeroLocus I (DualNumber k) := by
  sorry

variable (I)

/-- The Lie algebra `Lie(G) = T_1 G ⊆ gl_n` of the closed subgroup scheme `G = V(I)` of `GL_n`:
the matrices `X` with `1 + εX ∈ G(k[ε])`, with the commutator bracket `⁅X, Y⁆ = XY - YX`.
(blueprint: `sk-d-tangent`) -/
noncomputable def lie : LieSubalgebra k (Matrix n n k) where
  carrier := {X | dualUnit X ∈ zeroLocus I (DualNumber k)}
  add_mem' := dualUnit_add_mem
  zero_mem' := dualUnit_zero_mem
  smul_mem' := dualUnit_smul_mem
  lie_mem' := dualUnit_lie_mem

variable {I}

@[simp]
theorem mem_lie {X : Matrix n n k} : X ∈ lie I ↔ dualUnit X ∈ zeroLocus I (DualNumber k) :=
  Iff.rfl

theorem lie_anti {J : Ideal (CoordinateRing n k)} [J.IsHopfIdeal k] (h : I ≤ J) :
    lie J ≤ lie I :=
  fun _ hX ↦ zeroLocus_anti h hX

theorem lie_top : lie (⊥ : Ideal (CoordinateRing n k)) = ⊤ := by
  ext X
  simp only [mem_lie, LieSubalgebra.mem_top, iff_true]
  intro a ha
  rw [Ideal.mem_bot.1 ha, map_zero]

/-- The concrete Lie algebra `lie I` is the Lie algebra `ker(G(k[ε]) → G(k))` of the group scheme
`G = V(I)`, read inside `GL n (k[ε])`. (blueprint: `sk-d-tangent`) -/
theorem mem_lie_iff_dualUnit_mem_lie_subgroupScheme (X : Matrix n n k) :
    X ∈ lie I ↔ ∃ φ ∈ GrpObj.lie (subgroupScheme I),
      homMulEquiv n k (DualNumber k) (φ ≫ subgroupSchemeι I) = dualUnit X := by
  sorry

theorem map_algebraMap_mul_dualUnit_mul (g : GL n k) (X : Matrix n n k) :
    map (algebraMap k (DualNumber k)) g * dualUnit X * map (algebraMap k (DualNumber k)) g⁻¹ =
      dualUnit ((g : Matrix n n k) * X * ((g⁻¹ : GL n k) : Matrix n n k)) := by
  have hinr (Y : Matrix n n k) : Y.map (TrivSqZeroExt.inr : k → DualNumber k) =
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
theorem conj_mem_lie {g : GL n k} (hg : g ∈ zeroLocus I k) {X : Matrix n n k} (hX : X ∈ lie I) :
    (g : Matrix n n k) * X * ((g⁻¹ : GL n k) : Matrix n n k) ∈ lie I := by
  rw [mem_lie, ← map_algebraMap_mul_dualUnit_mul]
  have hg' := map_mem_zeroLocus (Algebra.ofId k (DualNumber k)) hg
  have hg'' := map_mem_zeroLocus (Algebra.ofId k (DualNumber k)) (inv_mem hg)
  exact mul_mem (mul_mem hg' hX) hg''

/-- Over an algebraically closed field of characteristic zero, the Lie algebra of an algebraic
group is the Lie algebra of its identity component. (blueprint: `sk-i-cartier`) -/
theorem lie_identityComponent [IsAlgClosed k] [CharZero k] (I : Ideal (CoordinateRing n k))
    [I.IsHopfIdeal k] : lie (identityComponent I) = lie I := by
  sorry

/-- Cartier's theorem, Lie algebra form: over an algebraically closed field of characteristic
zero, the Lie algebra of a reduced closed subgroup scheme `V(I)` has dimension the Krull dimension
of its coordinate ring. (blueprint: `sk-i-cartier`) -/
theorem finrank_lie_eq_ringKrullDim [IsAlgClosed k] [CharZero k] (hI : I.IsRadical) :
    (Module.finrank k (lie I) : WithBot ℕ∞) = ringKrullDim (CoordinateRing n k ⧸ I) := by
  sorry

end Lie

section RationalHom

variable (I : Ideal (CoordinateRing n k)) [I.IsHopfIdeal k]

/-- A rational representation of the closed subgroup scheme `V(I)` of `GL_n` on `k^m`: a
homomorphism of group schemes `V(I) ⟶ GL_m`, given by the bialgebra homomorphism of coordinate
rings `k[GL_m] → k[GL_n] ⧸ I`. (blueprint: `sk-d-tangent`) -/
abbrev RationalHom (m : Type u) [Fintype m] [DecidableEq m] :=
  CoordinateRing m k →ₐc[k] CoordinateRing n k ⧸ I

variable {I} {m : Type u} [Fintype m] [DecidableEq m]

section Lift

variable {R : Type*} [CommRing R] [Algebra k R]

theorem liftₐ_evalAlgHom_one :
    toConv (Ideal.Quotient.liftₐ I (evalAlgHom (1 : GL n R)) (zeroLocus I R).one_mem) = 1 := by
  ext1
  apply Ideal.Quotient.algHom_ext
  refine AlgHom.ext fun a ↦ ?_
  have h := congr(ofConv $(evalAlgHom_one (n := n) (k := k) (R := R)) a)
  simp only [AlgHom.convOne_apply] at h
  simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.liftₐ_apply,
    Ideal.Quotient.lift_mk, AlgHom.coe_toRingHom, AlgHom.convOne_apply]
  exact h

theorem liftₐ_evalAlgHom_mul (g h : zeroLocus I R) :
    toConv (Ideal.Quotient.liftₐ I (evalAlgHom (g * h : zeroLocus I R).1) (g * h).2) =
      toConv (Ideal.Quotient.liftₐ I (evalAlgHom g.1) g.2) *
        toConv (Ideal.Quotient.liftₐ I (evalAlgHom h.1) h.2) := by
  ext1
  apply Ideal.Quotient.algHom_ext
  refine Eq.trans ?_ (AlgHom.convMul_comp_bialgHom_distrib _ _
    (Bialgebra.Quotient.mkBialgHom (R := k) I)).symm
  exact congrArg ofConv (evalAlgHom_mul (k := k) g.1 h.1)

end Lift

namespace RationalHom

/-- The homomorphism of group schemes `V(I) ⟶ GL_m` of a rational representation. -/
noncomputable def toHom (r : RationalHom I m) : subgroupScheme I ⟶ scheme m k :=
  (Spec.map (CommRingCat.ofHom
    (r : CoordinateRing m k →ₐ[k] CoordinateRing n k ⧸ I).toRingHom)).asOver (Spec (.of k))

instance (r : RationalHom I m) : IsMonHom r.toHom :=
  inferInstanceAs (IsMonHom ((bialgSpec (.of k)).map (CommBialgCat.ofHom r).op).hom)

variable {R S : Type*} [CommRing R] [Algebra k R] [CommRing S] [Algebra k S]

/-- The algebra homomorphism `k[GL_m] → R` giving the image of an `R`-point `g` of `V(I)` under
a rational representation. -/
noncomputable def pointsAlgHom (r : RationalHom I m) (g : zeroLocus I R) :
    CoordinateRing m k →ₐ[k] R :=
  (Ideal.Quotient.liftₐ I (evalAlgHom g.1) g.2).comp
    (r : CoordinateRing m k →ₐ[k] CoordinateRing n k ⧸ I)

theorem pointsAlgHom_one (r : RationalHom I m) :
    toConv (r.pointsAlgHom (1 : zeroLocus I R)) = 1 := by
  ext1
  rw [pointsAlgHom, ofConv_toConv]
  change (ofConv (toConv (Ideal.Quotient.liftₐ I (evalAlgHom (1 : GL n R))
    (zeroLocus I R).one_mem))).comp _ = _
  rw [liftₐ_evalAlgHom_one]
  ext a
  simp [AlgHom.convOne_apply]

theorem pointsAlgHom_mul (r : RationalHom I m) (g h : zeroLocus I R) :
    toConv (r.pointsAlgHom (g * h)) = toConv (r.pointsAlgHom g) * toConv (r.pointsAlgHom h) := by
  ext1
  rw [pointsAlgHom, ofConv_toConv]
  change (ofConv (toConv (Ideal.Quotient.liftₐ I (evalAlgHom (g * h : zeroLocus I R).1)
    (g * h).2))).comp _ = _
  rw [liftₐ_evalAlgHom_mul, AlgHom.convMul_comp_bialgHom_distrib]
  rfl

/-- A rational representation of `V(I)` on `R`-points: the group homomorphism
`G(R) → GL m R`. (blueprint: `sk-d-tangent`) -/
noncomputable def points (r : RationalHom I m) (R : Type*) [CommRing R] [Algebra k R] :
    zeroLocus I R →* GL m R where
  toFun g := algHomMulEquiv m k R (toConv (r.pointsAlgHom g))
  map_one' := by rw [pointsAlgHom_one, map_one]
  map_mul' g h := by rw [pointsAlgHom_mul, map_mul]

theorem pointsAlgHom_map (r : RationalHom I m) (φ : R →ₐ[k] S) (g : zeroLocus I R) :
    r.pointsAlgHom ⟨map φ.toRingHom g, map_mem_zeroLocus φ g.2⟩ = φ.comp (r.pointsAlgHom g) := by
  have h : Ideal.Quotient.liftₐ I (evalAlgHom (map φ.toRingHom g.1)) (map_mem_zeroLocus φ g.2) =
      φ.comp (Ideal.Quotient.liftₐ I (evalAlgHom g.1) g.2) := by
    apply Ideal.Quotient.algHom_ext
    exact evalAlgHom_map φ g.1
  rw [pointsAlgHom, pointsAlgHom, h, AlgHom.comp_assoc]

theorem map_algHomMulEquiv (φ : R →ₐ[k] S) (ψ : CoordinateRing m k →ₐ[k] R) :
    map φ.toRingHom (algHomMulEquiv m k R (toConv ψ)) =
      algHomMulEquiv m k S (toConv (φ.comp ψ)) :=
  Units.ext (Matrix.ext fun _ _ ↦ rfl)

/-- A rational representation commutes with base change of points along `R → S`. -/
theorem map_points (r : RationalHom I m) (φ : R →ₐ[k] S) (g : zeroLocus I R) :
    map φ.toRingHom (r.points R g) = r.points S ⟨map φ.toRingHom g, map_mem_zeroLocus φ g.2⟩ := by
  change map φ.toRingHom (algHomMulEquiv m k R (toConv (r.pointsAlgHom g))) =
    algHomMulEquiv m k S (toConv (r.pointsAlgHom _))
  rw [pointsAlgHom_map, map_algHomMulEquiv]

theorem map_fstHom_dualUnit (X : Matrix n n k) :
    map (TrivSqZeroExt.fstHom k k k).toRingHom (dualUnit X) = 1 := by
  refine Units.ext (Matrix.ext fun i j ↦ ?_)
  change ((1 + X.map TrivSqZeroExt.inr : Matrix n n (DualNumber k)) i j).fst =
    (1 : Matrix n n k) i j
  rw [Matrix.add_apply, TrivSqZeroExt.fst_add, Matrix.map_apply, TrivSqZeroExt.fst_inr, add_zero,
    Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> rfl

theorem map_fst_coe_points_dualUnit (r : RationalHom I m) (X : lie I) :
    ((r.points (DualNumber k) ⟨dualUnit X, X.2⟩ : GL m (DualNumber k)) :
      Matrix m m (DualNumber k)).map TrivSqZeroExt.fst = 1 := by
  have h1 : (⟨map (TrivSqZeroExt.fstHom k k k).toRingHom (dualUnit X),
      map_mem_zeroLocus _ (mem_lie.1 X.2)⟩ : zeroLocus I k) = 1 :=
    Subtype.ext (map_fstHom_dualUnit (X : Matrix n n k))
  have h := r.map_points (TrivSqZeroExt.fstHom k k k) ⟨dualUnit X, X.2⟩
  rw [h1, map_one] at h
  exact congrArg Units.val h

theorem map_snd_mul_of_map_fst_eq_one {A B : Matrix m m (DualNumber k)}
    (hA : A.map TrivSqZeroExt.fst = 1) (hB : B.map TrivSqZeroExt.fst = 1) :
    (A * B).map TrivSqZeroExt.snd = A.map TrivSqZeroExt.snd + B.map TrivSqZeroExt.snd := by
  ext i j
  have hA' (i j) : (A i j).fst = (1 : Matrix m m k) i j := congr_fun₂ hA i j
  have hB' (i j) : (B i j).fst = (1 : Matrix m m k) i j := congr_fun₂ hB i j
  simp [Matrix.mul_apply, TrivSqZeroExt.snd_sum, TrivSqZeroExt.snd_mul, hA', hB',
    Matrix.one_apply, Finset.sum_add_distrib, add_comm]

theorem differential_map_add (r : RationalHom I m) (X Y : lie I) :
    ((r.points (DualNumber k) ⟨dualUnit (X + Y : lie I), (X + Y).2⟩ : GL m (DualNumber k)) :
      Matrix m m (DualNumber k)).map TrivSqZeroExt.snd =
    ((r.points (DualNumber k) ⟨dualUnit X, X.2⟩ : GL m (DualNumber k)) :
      Matrix m m (DualNumber k)).map TrivSqZeroExt.snd +
    ((r.points (DualNumber k) ⟨dualUnit Y, Y.2⟩ : GL m (DualNumber k)) :
      Matrix m m (DualNumber k)).map TrivSqZeroExt.snd := by
  have h : (⟨dualUnit (X + Y : lie I), (X + Y).2⟩ : zeroLocus I (DualNumber k)) =
      ⟨dualUnit X, X.2⟩ * ⟨dualUnit Y, Y.2⟩ := Subtype.ext (dualUnit_add _ _)
  rw [h, map_mul, Units.val_mul]
  exact map_snd_mul_of_map_fst_eq_one (map_fst_coe_points_dualUnit r X)
    (map_fst_coe_points_dualUnit r Y)

theorem differential_map_smul (r : RationalHom I m) (c : k) (X : lie I) :
    ((r.points (DualNumber k) ⟨dualUnit (c • X : lie I), (c • X).2⟩ : GL m (DualNumber k)) :
      Matrix m m (DualNumber k)).map TrivSqZeroExt.snd =
    c • ((r.points (DualNumber k) ⟨dualUnit X, X.2⟩ : GL m (DualNumber k)) :
      Matrix m m (DualNumber k)).map TrivSqZeroExt.snd := by
  have h : (⟨dualUnit (c • X : lie I), (c • X).2⟩ : zeroLocus I (DualNumber k)) =
      ⟨map (dualNumberScale c).toRingHom (dualUnit X),
        map_mem_zeroLocus (dualNumberScale c) (mem_lie.1 X.2)⟩ :=
    Subtype.ext (by
      dsimp only
      rw [SetLike.val_smul]
      exact (map_dualNumberScale_dualUnit c (X : Matrix n n k)).symm)
  rw [h, ← map_points r (dualNumberScale c) ⟨dualUnit X, X.2⟩]
  ext i j
  change (dualNumberScale c _).snd = c • TrivSqZeroExt.snd _
  rw [dualNumberScale, TrivSqZeroExt.snd_map]
  rfl

/-- The differential `dr : Lie(G) → gl_m` of a rational representation `r`: the `ε`-coefficient
of `r(1 + εX)`. (blueprint: `sk-d-tangent`) -/
noncomputable def differential (r : RationalHom I m) : lie I →ₗ[k] Matrix m m k where
  toFun X := ((r.points (DualNumber k) ⟨dualUnit X, X.2⟩ : GL m (DualNumber k)) :
    Matrix m m (DualNumber k)).map TrivSqZeroExt.snd
  map_add' := r.differential_map_add
  map_smul' := r.differential_map_smul

/-- The differential of a rational representation is a homomorphism of Lie algebras.
(blueprint: `sk-d-tangent`) -/
theorem differential_lie (r : RationalHom I m) (X Y : lie I) :
    r.differential ⁅X, Y⁆ = ⁅r.differential X, r.differential Y⁆ := by
  sorry

end RationalHom

/-- The group–Lie comparison for invariant subspaces: over an algebraically closed field of
characteristic zero, a subspace is stable under a connected algebraic group acting by a rational
representation if and only if it is stable under the differential of the representation.
(blueprint: `sk-p-comparison`) -/
theorem invariant_iff_differential_invariant [IsAlgClosed k] [CharZero k] (hI : I.IsRadical)
    (hconn : identityComponent I = I) (r : RationalHom I m) (U : Submodule k (m → k)) :
    (∀ g : zeroLocus I k, ∀ v ∈ U, ((r.points k g : GL m k) : Matrix m m k) *ᵥ v ∈ U) ↔
      ∀ X : lie I, ∀ v ∈ U, r.differential X *ᵥ v ∈ U := by
  sorry

/-- The group–Lie comparison for the centre: over an algebraically closed field of characteristic
zero, the Lie algebra of the identity component of the centre of a connected algebraic group is
the centre of its Lie algebra. (blueprint: `sk-p-comparison`) -/
theorem lie_identityComponent_center_eq [IsAlgClosed k] [CharZero k] (hI : I.IsRadical)
    (hconn : identityComponent I = I) :
    (lie (identityComponent (center I)) : Set (Matrix n n k)) =
      {X ∈ (lie I : Set (Matrix n n k)) | ∀ Y ∈ lie I, ⁅X, Y⁆ = 0} := by
  sorry

end RationalHom

end Matrix.GeneralLinearGroup
