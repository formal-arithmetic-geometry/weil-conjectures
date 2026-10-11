/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Lie.Matrix
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Lie
public import WeilConjectures.Mathlib.Algebra.DualNumber

/-!
# The Lie algebra of `GL_n` and rational representations

The infinitesimal points of the general linear group scheme `𝔾𝕃(n; k)` over a commutative ring `k`
are the invertible matrices `1 + εX` over the dual numbers `k[ε]`, with `X ∈ gl_n = Matrix n n k`;
their group law is `(1 + εX)(1 + εY) = 1 + ε(X + Y)`, and the mixed term of the commutator
`(1 + εX)(1 + δY)(1 - εX)(1 - δY) = 1 + εδ(XY - YX)` is the matrix commutator. Hence
`Lie(GL_n) = gl_n` with the commutator bracket.

A *rational representation* of a group scheme `G` over `k` on `k^m` is a homomorphism of group
schemes `r : G ⟶ GL_m`. Its differential `dr : Lie(G) → gl_m` is the differential of `r` read in
`gl_m` through `Lie(GL_m) = gl_m`. Over an algebraically closed field of characteristic zero, a
subspace of `k^m` is stable under a connected `G` acting through `r` if and only if it is stable
under `dr(Lie G)`: the group–Lie comparison for invariant subspaces.

## Main definitions

- `AlgebraicGeometry.GeneralLinearGroup.dualUnit`: the point `1 + εX` of `GL_n` over `k[ε]`.
- `AlgebraicGeometry.GeneralLinearGroup.toMatrix`: the matrix `X` of a tangent vector `1 + εX`.
- `AlgebraicGeometry.GeneralLinearGroup.lieAlgebraEquivMatrix`: `Lie(GL_n) ≃ₗ⁅k⁆ gl_n`.
- `AlgebraicGeometry.GeneralLinearGroup.RationalHom`: rational representations `G ⟶ GL_m` of a
  group scheme `G` over `k`, with their action on points
  (`AlgebraicGeometry.GeneralLinearGroup.RationalHom.points`) and their differential
  (`AlgebraicGeometry.GeneralLinearGroup.RationalHom.differential`).

## Main results

- `AlgebraicGeometry.GeneralLinearGroup.RationalHom.invariant_iff_differential_invariant`: the
  group–Lie comparison for invariant subspaces.

## Implementation notes

The bracket on `Matrix n n k` is the commutator bracket `LieRing.ofAssociativeRing`, activated
locally as in `Mathlib.Algebra.Lie.Matrix`. The missing proofs are recorded as `sorry`, each with
a proof sketch in its docstring. Following `𝔾𝕃(n; k)`, the base ring is written `k` even when it is
only a commutative ring.

## Blueprint

- `sk-d-tangent`: the Lie algebra of `GL_n` as its tangent space at the identity, rational
  representations and their differentials.
- `sk-p-comparison`: invariant subspaces for the group and for its Lie algebra.
-/

@[expose] public section

universe u

open CategoryTheory TrivSqZeroExt
open scoped MonObj Matrix

attribute [local instance 100] LieRing.ofAssociativeRing

namespace AlgebraicGeometry.GeneralLinearGroup

open Matrix.GeneralLinearGroup

section GeneralLinear

variable (n : Type u) [Fintype n] [DecidableEq n] (k : Type u) [CommRing k]

/-- The invertible matrix `1 + εX` over the dual numbers `k[ε]`, with inverse `1 - εX`: the point
of `GL_n` with values in `k[ε]` corresponding to the tangent vector `X ∈ gl_n`.
(blueprint: `sk-d-tangent`) -/
noncomputable def dualUnit {n : Type*} [Fintype n] [DecidableEq n] {k : Type*} [CommRing k]
    (X : Matrix n n k) : GL n (DualNumber k) :=
  ⟨1 + X.map inr, 1 - X.map inr,
    by rw [add_mul, one_mul, mul_sub, mul_one, Matrix.map_inr_mul_map_inr, sub_zero,
      sub_add_cancel],
    by rw [sub_mul, one_mul, mul_add, mul_one, Matrix.map_inr_mul_map_inr, add_zero,
      add_sub_cancel_right]⟩

theorem coe_dualUnit {n : Type*} [Fintype n] [DecidableEq n] {k : Type*} [CommRing k]
    (X : Matrix n n k) : (dualUnit X : Matrix n n (DualNumber k)) = 1 + X.map inr :=
  rfl

/-- The matrix `1 + εX` reduces to the identity modulo `ε`. -/
@[simp]
theorem map_fstHom_dualUnit {n : Type*} [Fintype n] [DecidableEq n] {k : Type*} [CommRing k]
    (X : Matrix n n k) :
    Matrix.GeneralLinearGroup.map (fstHom k k k).toRingHom (dualUnit X) = 1 := by
  refine Units.ext (Matrix.ext fun i j ↦ ?_)
  change ((1 + X.map inr : Matrix n n (DualNumber k)) i j).fst = (1 : Matrix n n k) i j
  rw [Matrix.add_apply, fst_add, Matrix.map_apply, fst_inr, add_zero, Matrix.one_apply,
    Matrix.one_apply]
  split_ifs <;> rfl

end GeneralLinear

section Commutator

variable {n : Type*} [Fintype n] [DecidableEq n] {R : Type*} [CommRing R]

/-- The commutator of `1 + eX` and `1 + dY` for `e² = d² = 0` is `1 + ed(XY - YX)`. -/
theorem one_add_smul_mul_one_add_smul_mul_one_sub_smul_mul_one_sub_smul (e d : R)
    (he : e * e = 0) (hd : d * d = 0) (X Y : Matrix n n R) :
    (1 + e • X) * (1 + d • Y) * (1 - e • X) * (1 - d • Y) = 1 + (e * d) • (X * Y - Y * X) := by
  set a := e • X
  set b := d • Y
  have haa : a * a = 0 := by simp [a, Matrix.smul_mul, Matrix.mul_smul, smul_smul, he]
  have hbb : b * b = 0 := by simp [b, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hd]
  have haba : a * b * a = 0 := by
    simp only [a, b, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    rw [show e * (d * e) = e * e * d by ring, he, zero_mul, zero_smul]
  have hab : a * b = (e * d) • (X * Y) := by
    simp only [a, b, Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_comm d e]
  have hba : b * a = (e * d) • (Y * X) := by
    simp only [a, b, Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_comm d e]
  have h₁ : (1 + a) * (1 + b) * (1 - a) = 1 + b + a * b - b * a - a * a - a * b * a := by
    noncomm_ring
  have h₂ : (1 + b + a * b - b * a) * (1 - b) =
      1 + a * b - b * a - b * b - a * (b * b) + b * a * b := by
    noncomm_ring
  have hbab : b * a * b = 0 := by
    simp only [a, b, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    rw [show d * (e * d) = d * d * e by ring, hd, zero_mul, zero_smul]
  rw [h₁, haa, haba, sub_zero, sub_zero, h₂, hbb, mul_zero, hbab, sub_zero, sub_zero, add_zero,
    add_sub_assoc, hab, hba, ← smul_sub]

theorem smul_mul_smul_eq_zero (e : R) (he : e * e = 0) (X : Matrix n n R) :
    (e • X) * (e • X) = 0 := by
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, he, zero_smul]

end Commutator

section GeneralLinear

variable (n : Type u) [Fintype n] [DecidableEq n] (k : Type u) [Field k]

/-- The matrix `X` of a tangent vector `1 + εX` of `GL_n`. -/
noncomputable def tangentMatrix (p : GrpObj.pointsKer 𝔾𝕃(n; k) GrpObj.aug₁) : Matrix n n k :=
  ((homMulEquiv n k (DualNumber k) p.1 : GL n (DualNumber k)) : Matrix n n (DualNumber k)).map
    snd

variable {n k}

theorem homMulEquiv_points_map {A B : Type u} [CommRing A] [Algebra k A] [CommRing B]
    [Algebra k B] (ψ : A →ₐ[k] B) (p : points 𝔾𝕃(n; k) A) :
    homMulEquiv n k B (points.map _ ψ p) =
      Matrix.GeneralLinearGroup.map ψ.toRingHom (homMulEquiv n k A p) :=
  homMulEquiv_specMap_comp ψ p

theorem coe_homMulEquiv_tangent (p : GrpObj.pointsKer 𝔾𝕃(n; k) GrpObj.aug₁) :
    ((homMulEquiv n k (DualNumber k) p.1 : GL n (DualNumber k)) : Matrix n n (DualNumber k)) =
      1 + (tangentMatrix n k p).map inr := by
  refine Matrix.eq_one_add_map_inr_of_map_fst_eq_one ?_
  have h := homMulEquiv_points_map (n := n) (fstHom k k k) p.1
  rw [GrpObj.mem_pointsKer.1 p.2, map_one] at h
  exact (congrArg Units.val h).symm

theorem coe_homMulEquiv_tangentMap {A : Type u} [CommRing A] [Algebra k A] [IsLocalRing A]
    {π : A →ₐ[k] k} [IsLocalHom π.toRingHom] (m : A) (hm : m * m = 0) (hπ : π m = 0)
    (p : GrpObj.pointsKer 𝔾𝕃(n; k) GrpObj.aug₁) :
    ((homMulEquiv n k A (GrpObj.tangentMap m hm hπ p).1 : GL n A) : Matrix n n A) =
      1 + m • (tangentMatrix n k p).map (algebraMap k A) := by
  change ((homMulEquiv n k A (points.map _ _ p.1) : GL n A) : Matrix n n A) = _
  rw [homMulEquiv_points_map]
  ext i j
  rw [Matrix.GeneralLinearGroup.map_apply, coe_homMulEquiv_tangent]
  simp [Matrix.one_apply, apply_ite, DualNumber.liftElem_apply, mul_comm]

theorem tangentMatrix_injective : Function.Injective (tangentMatrix n k) := fun p q h ↦ by
  apply Subtype.ext
  apply (homMulEquiv n k (DualNumber k)).injective
  apply Units.ext
  rw [coe_homMulEquiv_tangent, coe_homMulEquiv_tangent, h]

theorem tangentMatrix_mul (p q : GrpObj.pointsKer 𝔾𝕃(n; k) GrpObj.aug₁) :
    tangentMatrix n k (p * q) = tangentMatrix n k p + tangentMatrix n k q := by
  have hfst (r : GrpObj.pointsKer 𝔾𝕃(n; k) GrpObj.aug₁) :
      ((homMulEquiv n k (DualNumber k) r.1 : GL n (DualNumber k)) :
        Matrix n n (DualNumber k)).map fst = 1 := by
    rw [coe_homMulEquiv_tangent]
    ext i j
    simp [Matrix.one_apply, apply_ite]
  rw [tangentMatrix, Subgroup.coe_mul, map_mul, Units.val_mul,
    Matrix.map_snd_mul_of_map_fst_eq_one (hfst p) (hfst q)]
  rfl

theorem tangentMatrix_tangentScale (c : k) (p : GrpObj.pointsKer 𝔾𝕃(n; k) GrpObj.aug₁) :
    tangentMatrix n k (GrpObj.tangentScale c p) = c • tangentMatrix n k p := by
  rw [tangentMatrix, GrpObj.tangentScale, coe_homMulEquiv_tangentMap]
  ext i j
  simp [Matrix.one_apply, apply_ite, algebraMap_eq_inl]

theorem coe_homMulEquiv_inv {A : Type u} [CommRing A] (g : GL n A) (N : Matrix n n A)
    (hN : N * N = 0) (hg : (g : Matrix n n A) = 1 + N) :
    ((g⁻¹ : GL n A) : Matrix n n A) = 1 - N := by
  have h : (g : Matrix n n A) * (1 - N) = 1 := by
    rw [hg, add_mul, one_mul, mul_sub, mul_one, hN, sub_zero, sub_add_cancel]
  calc ((g⁻¹ : GL n A) : Matrix n n A)
      = ((g⁻¹ : GL n A) : Matrix n n A) * ((g : Matrix n n A) * (1 - N)) := by rw [h, mul_one]
    _ = 1 - N := by rw [← mul_assoc, Units.inv_mul, one_mul]

set_option maxHeartbeats 1000000 in
open scoped commutatorElement in
theorem tangentMatrix_tangentBracket (p q : GrpObj.pointsKer 𝔾𝕃(n; k) GrpObj.aug₁) :
    tangentMatrix n k (GrpObj.tangentBracket p q) =
      tangentMatrix n k p * tangentMatrix n k q - tangentMatrix n k q * tangentMatrix n k p := by
  have h := congrArg (fun r : GrpObj.pointsKer 𝔾𝕃(n; k) (GrpObj.aug₂ (k := k)) ↦
    ((homMulEquiv n k _ r.1 : GL n _) : Matrix n n (DualNumber (DualNumber k))))
    (GrpObj.tangentMul_tangentBracket p q)
  rw [GrpObj.tangentMul, coe_homMulEquiv_tangentMap] at h
  obtain ⟨X, hX⟩ : ∃ X : Matrix n n (DualNumber (DualNumber k)),
      X = (tangentMatrix n k p).map (algebraMap k _) := ⟨_, rfl⟩
  obtain ⟨Y, hY⟩ : ∃ Y : Matrix n n (DualNumber (DualNumber k)),
      Y = (tangentMatrix n k q).map (algebraMap k _) := ⟨_, rfl⟩
  obtain ⟨a, ha₀⟩ : ∃ a : GL n (DualNumber (DualNumber k)),
      a = homMulEquiv n k _ (GrpObj.tangentEps p).1 := ⟨_, rfl⟩
  obtain ⟨b, hb₀⟩ : ∃ b : GL n (DualNumber (DualNumber k)),
      b = homMulEquiv n k _ (GrpObj.tangentDel q).1 := ⟨_, rfl⟩
  have ha : (a : Matrix n n (DualNumber (DualNumber k))) = 1 + GrpObj.eps₂ (k := k) • X := by
    rw [ha₀, hX]
    exact coe_homMulEquiv_tangentMap _ _ _ p
  have hb : (b : Matrix n n (DualNumber (DualNumber k))) = 1 + GrpObj.del₂ (k := k) • Y := by
    rw [hb₀, hY]
    exact coe_homMulEquiv_tangentMap _ _ _ q
  have hai := coe_homMulEquiv_inv a _ (smul_mul_smul_eq_zero _ GrpObj.eps₂_mul_self X) ha
  have hbi := coe_homMulEquiv_inv b _ (smul_mul_smul_eq_zero _ GrpObj.del₂_mul_self Y) hb
  have e : homMulEquiv n k _ (⁅GrpObj.tangentEps p, GrpObj.tangentDel q⁆ :
      GrpObj.pointsKer 𝔾𝕃(n; k) (GrpObj.aug₂ (k := k))).1 = a * b * a⁻¹ * b⁻¹ := by
    rw [ha₀, hb₀, commutatorElement_def]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv]
  rw [e, Units.val_mul, Units.val_mul, Units.val_mul, ha, hb, hai, hbi,
    one_add_smul_mul_one_add_smul_mul_one_sub_smul_mul_one_sub_smul _ _ GrpObj.eps₂_mul_self
      GrpObj.del₂_mul_self X Y, hX, hY] at h
  have hm : (tangentMatrix n k p).map (algebraMap k (DualNumber (DualNumber k))) *
        (tangentMatrix n k q).map (algebraMap k _) -
      (tangentMatrix n k q).map (algebraMap k _) * (tangentMatrix n k p).map (algebraMap k _) =
      (tangentMatrix n k p * tangentMatrix n k q - tangentMatrix n k q * tangentMatrix n k p).map
        (algebraMap k (DualNumber (DualNumber k))) := by
    simp only [← RingHom.mapMatrix_apply, map_sub, map_mul]
  rw [hm, add_right_inj] at h
  ext i j
  have hij := congrArg (fun M : Matrix n n (DualNumber (DualNumber k)) ↦ (M i j).snd.snd) h
  simp only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul] at hij
  rwa [mul_comm, GrpObj.snd_snd_algebraMap₂_mul_eps₂_mul_del₂, mul_comm,
    GrpObj.snd_snd_algebraMap₂_mul_eps₂_mul_del₂] at hij

variable (n k)

/-- The matrix of a tangent vector of `GL_n`: the infinitesimal point `1 + εX` goes to `X`. -/
noncomputable def toMatrix (x : GrpObj.Lie 𝔾𝕃(n; k)) : Matrix n n k :=
  tangentMatrix n k (GrpObj.lieEquivTangent 𝔾𝕃(n; k) x)

/-- `Lie(GL_n) → gl_n` as a homomorphism of Lie algebras: the bracket is preserved because the
mixed term of the commutator `(1 + εX)(1 + δY)(1 - εX)(1 - δY) = 1 + εδ(XY - YX)` is the matrix
commutator. -/
noncomputable def toMatrixLieHom : GrpObj.Lie 𝔾𝕃(n; k) →ₗ⁅k⁆ Matrix n n k where
  toFun := toMatrix n k
  map_add' x y := by
    rw [toMatrix, GrpObj.lieEquivTangent_add, tangentMatrix_mul]
    rfl
  map_smul' c x := by
    rw [toMatrix, GrpObj.lieEquivTangent_smul, tangentMatrix_tangentScale]
    rfl
  map_lie' {x y} := by
    rw [toMatrix, GrpObj.lieEquivTangent_lie, tangentMatrix_tangentBracket, Ring.lie_def]
    rfl

/-- `Lie(GL_n) → gl_n` is bijective: every infinitesimal point of `GL_n` is uniquely `1 + εX`. -/
theorem bijective_toMatrixLieHom : Function.Bijective (toMatrixLieHom n k) := by
  refine ⟨fun x y h ↦ (GrpObj.lieEquivTangent _).injective (tangentMatrix_injective h), fun X ↦ ?_⟩
  have hp : (homMulEquiv n k (DualNumber k)).symm (dualUnit X) ∈
      GrpObj.pointsKer 𝔾𝕃(n; k) (GrpObj.aug₁ (k := k)) := by
    rw [GrpObj.mem_pointsKer]
    apply (homMulEquiv n k k).injective
    rw [homMulEquiv_points_map, MulEquiv.apply_symm_apply, map_one]
    exact map_fstHom_dualUnit X
  refine ⟨(GrpObj.lieEquivTangent _).symm ⟨_, hp⟩, ?_⟩
  change tangentMatrix n k (GrpObj.lieEquivTangent _ ((GrpObj.lieEquivTangent _).symm _)) = X
  rw [Equiv.apply_symm_apply, tangentMatrix]
  simp only [MulEquiv.apply_symm_apply, coe_dualUnit]
  ext i j
  simp [Matrix.one_apply, apply_ite]

/-- The Lie algebra of the general linear group is `gl_n`, the matrices with the commutator
bracket: the tangent vector `1 + εX` corresponds to `X`.
(blueprint: `sk-d-tangent`, `def-wf-lie-algebra-derivation`) -/
noncomputable def lieAlgebraEquivMatrix : GrpObj.Lie 𝔾𝕃(n; k) ≃ₗ⁅k⁆ Matrix n n k :=
  LieEquiv.ofBijective _ (bijective_toMatrixLieHom n k)

@[simp]
theorem lieAlgebraEquivMatrix_apply (x : GrpObj.Lie 𝔾𝕃(n; k)) :
    lieAlgebraEquivMatrix n k x = toMatrix n k x :=
  rfl

/-- The tangent vector of `GL_n` corresponding to the matrix `X` is the point `1 + εX`. -/
theorem infPointsEquivTangentGroup_lieAlgebraEquivMatrix_symm (X : Matrix n n k) :
    (GrpObj.infPointsEquivTangentGroup 𝔾𝕃(n; k)
      ((GrpObj.lieEquiv 𝔾𝕃(n; k)).symm ((lieAlgebraEquivMatrix n k).symm X)) :
        points 𝔾𝕃(n; k) (DualNumber k)) = (homMulEquiv n k (DualNumber k)).symm (dualUnit X) := by
  set x := (lieAlgebraEquivMatrix n k).symm X
  have hx : toMatrix n k x = X := (lieAlgebraEquivMatrix n k).apply_symm_apply X
  rw [MulEquiv.eq_symm_apply]
  apply Units.ext
  change ((homMulEquiv n k _ (GrpObj.lieEquivTangent _ x).1 : GL n (DualNumber k)) :
    Matrix n n (DualNumber k)) = _
  rw [coe_homMulEquiv_tangent, coe_dualUnit]
  exact congrArg (fun M : Matrix n n k ↦ 1 + M.map (inr : k → DualNumber k)) hx
end GeneralLinear

/-! ### Rational representations -/

section RationalHom

variable {k : Type u} [CommRing k] (G : Over (Spec (.of k))) [GrpObj G]
  (m : Type u) [Fintype m] [DecidableEq m]

/-- A rational representation of a group scheme `G` over `k` on `k^m`: a morphism of schemes
`G ⟶ GL_m` over `k`, required to be a homomorphism of group schemes through an `IsMonHom`
instance. (blueprint: `sk-d-tangent`, `def-wf-lie-algebra-derivation`) -/
abbrev RationalHom :=
  G ⟶ 𝔾𝕃(m; k)

variable {G m}

namespace RationalHom

/-- A rational representation of `G` on `R`-points: the group homomorphism `G(R) → GL m R` given
by composing points `Spec R ⟶ G` with `r`. (blueprint: `sk-d-tangent`) -/
noncomputable def points (r : RationalHom G m) [IsMonHom r] (R : Type u) [CommRing R]
    [Algebra k R] : AlgebraicGeometry.points G R →* GL m R :=
  (homMulEquiv m k R).toMonoidHom.comp (IsMonHom.monoidHom r _)

theorem points_apply (r : RationalHom G m) [IsMonHom r] {R : Type u} [CommRing R] [Algebra k R]
    (g : AlgebraicGeometry.points G R) : r.points R g = homMulEquiv m k R (g ≫ r) :=
  rfl

/-- A rational representation commutes with base change of points along `R → S`. -/
theorem map_points (r : RationalHom G m) [IsMonHom r] {R S : Type u} [CommRing R] [Algebra k R]
    [CommRing S] [Algebra k S] (φ : R →ₐ[k] S) (g : AlgebraicGeometry.points G R) :
    Matrix.GeneralLinearGroup.map φ.toRingHom (r.points R g) =
      r.points S (AlgebraicGeometry.points.map G φ g) := by
  rw [points_apply, points_apply, AlgebraicGeometry.points.map, Category.assoc,
    homMulEquiv_specMap_comp]

end RationalHom

end RationalHom

section RationalHomField

variable {k : Type u} [Field k] {G : Over (Spec (.of k))} [GrpObj G]
  {m : Type u} [Fintype m] [DecidableEq m]

namespace RationalHom

/-- The differential `dr : Lie(G) → gl_m` of a rational representation `r`: the differential of
the homomorphism of group schemes `G ⟶ GL_m`, read in `gl_m` through `Lie(GL_m) = gl_m`. It is a
homomorphism of Lie algebras. (blueprint: `sk-d-tangent`, `def-wf-lie-algebra-derivation`) -/
noncomputable def differential (r : RationalHom G m) [IsMonHom r] :
    GrpObj.Lie G →ₗ⁅k⁆ Matrix m m k :=
  (lieAlgebraEquivMatrix m k).toLieHom.comp (GrpObj.differential r)

theorem differential_apply (r : RationalHom G m) [IsMonHom r] (x : GrpObj.Lie G) :
    r.differential x = lieAlgebraEquivMatrix m k (GrpObj.differential r x) :=
  rfl

/-- If a subspace `U ⊆ k^m` is stable under the dual-number points of `G` acting by `r`, that is
the `ε`-part of `r(g) v` lies in `U` for `g ∈ G(k[ε])` and `v ∈ U`, then `U` is stable under the
differential of `r`: `dr(X) v` is the `ε`-part of `r(1 + εX) v`. -/
theorem le_comap_toLin'_differential (r : RationalHom G m) [IsMonHom r]
    (U : Submodule k (m → k))
    (hU : ∀ g : AlgebraicGeometry.points G (DualNumber k), ∀ v ∈ U,
      snd ∘ ((r.points (DualNumber k) g : Matrix m m (DualNumber k)) *ᵥ (inl ∘ v)) ∈ U)
    (X : GrpObj.Lie G) : U ≤ U.comap (Matrix.toLin' (r.differential X)) := by
  intro v hv
  have h := hU (GrpObj.lieEquivTangent G X).1 v hv
  rw [points_apply] at h
  have e := coe_homMulEquiv_tangent (GrpObj.kerPost r (GrpObj.lieEquivTangent G X))
  change ((homMulEquiv m k _ ((GrpObj.lieEquivTangent G X).1 ≫ r) : GL m (DualNumber k)) :
    Matrix m m (DualNumber k)) = _ at e
  rw [e] at h
  rw [Submodule.mem_comap, Matrix.toLin'_apply, differential_apply, lieAlgebraEquivMatrix_apply,
    toMatrix, GrpObj.lieEquivTangent_differential]
  convert h using 1
  ext i
  simp [Matrix.mulVec, dotProduct, Matrix.add_apply, Matrix.one_apply, apply_ite,
    TrivSqZeroExt.snd_sum]

end RationalHom

end RationalHomField

/-! ### The group–Lie comparison for invariant subspaces -/

section Comparison

variable {k : Type u} [Field k] {G : Over (Spec (.of k))} [GrpObj G]
  {m : Type u} [Fintype m] [DecidableEq m]

namespace RationalHom

/-- For a reduced group scheme `G` locally of finite type over an algebraically closed field, a
subspace stable under `G(k)` is stable under the points of `G` with values in the dual numbers.

Proof sketch (not formalised): the condition `r(g) U ⊆ U` is cut out by equations on `G`; they
vanish on `G(k)`, which is dense in the reduced `G`, hence they vanish on `G`, so `r(g)` preserves
`U ⊗ k[ε]` for every `g ∈ G(k[ε])`. (blueprint: `sk-p-comparison`) -/
theorem snd_mulVec_mem_of_le_comap [IsAlgClosed k] [IsReduced G.left]
    [LocallyOfFiniteType G.hom] (r : RationalHom G m) [IsMonHom r] (U : Submodule k (m → k))
    (hU : ∀ g : AlgebraicGeometry.points G k, U ≤ U.comap (Matrix.toLin' (r.points k g)))
    (g : AlgebraicGeometry.points G (DualNumber k)) {v : m → k} (hv : v ∈ U) :
    snd ∘ ((r.points (DualNumber k) g : Matrix m m (DualNumber k)) *ᵥ (inl ∘ v)) ∈ U := by
  sorry

/-- Over an algebraically closed field of characteristic zero, a subspace stable under the
differential of a rational representation of a connected group scheme `G` locally of finite type
is stable under `G(k)`.

Proof sketch (not formalised): replacing `G` by its image `r(G) ⊆ GL_m`, which is closed
(`AlgebraicGeometry.isClosed_range_of_isMonHom`), reduces this to the defining representation,
using that `dr` is surjective onto `Lie(r(G))` in characteristic zero; the stabiliser of `U` in
`r(G)` is a closed subgroup scheme whose Lie algebra is all of `Lie(r(G))`, so it has the dimension
of `r(G)` by `AlgebraicGeometry.GrpObj.finrank_lie_eq_topologicalKrullDim` and is the whole
connected group `r(G)` by `AlgebraicGeometry.isIso_left_of_topologicalKrullDim_eq`.
(blueprint: `sk-p-comparison`) -/
theorem le_comap_toLin'_points [IsAlgClosed k] [CharZero k] [ConnectedSpace G.left]
    [LocallyOfFiniteType G.hom] (r : RationalHom G m) [IsMonHom r] (U : Submodule k (m → k))
    (hU : ∀ X : GrpObj.Lie G, U ≤ U.comap (Matrix.toLin' (r.differential X)))
    (g : AlgebraicGeometry.points G k) : U ≤ U.comap (Matrix.toLin' (r.points k g)) := by
  sorry

/-- The group–Lie comparison for invariant subspaces: over an algebraically closed field of
characteristic zero, a subspace is stable under a connected group scheme locally of finite type
acting by a rational representation if and only if it is stable under the differential of the
representation. (blueprint: `sk-p-comparison`) -/
theorem invariant_iff_differential_invariant [IsAlgClosed k] [CharZero k] [ConnectedSpace G.left]
    [LocallyOfFiniteType G.hom] (r : RationalHom G m) [IsMonHom r] (U : Submodule k (m → k)) :
    (∀ g : AlgebraicGeometry.points G k, U ≤ U.comap (Matrix.toLin' (r.points k g))) ↔
      ∀ X : GrpObj.Lie G, U ≤ U.comap (Matrix.toLin' (r.differential X)) :=
  haveI := GrpObj.isReduced_of_charZero G
  ⟨fun h ↦ r.le_comap_toLin'_differential U fun g _ hv ↦ r.snd_mulVec_mem_of_le_comap U h g hv,
    fun h ↦ r.le_comap_toLin'_points U h⟩

end RationalHom

end Comparison

end AlgebraicGeometry.GeneralLinearGroup
