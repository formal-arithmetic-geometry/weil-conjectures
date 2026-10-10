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

theorem coe_dualUnit_inv {n : Type*} [Fintype n] [DecidableEq n] {k : Type*} [CommRing k]
    (X : Matrix n n k) :
    (((dualUnit X)⁻¹ : GL n (DualNumber k)) : Matrix n n (DualNumber k)) = 1 - X.map inr :=
  rfl

/-- The matrix `1 + εX` reduces to the identity modulo `ε`, entrywise. -/
@[simp]
theorem map_fst_dualUnit {n : Type*} [Fintype n] [DecidableEq n] {k : Type*} [CommRing k]
    (X : Matrix n n k) : (dualUnit X : Matrix n n (DualNumber k)).map fst = 1 := by
  ext i j
  simp [coe_dualUnit, Matrix.one_apply, apply_ite fst]

/-- The `ε`-part of `1 + εX` is `X`. -/
@[simp]
theorem map_snd_dualUnit {n : Type*} [Fintype n] [DecidableEq n] {k : Type*} [CommRing k]
    (X : Matrix n n k) : (dualUnit X : Matrix n n (DualNumber k)).map snd = X := by
  ext i j
  simp [coe_dualUnit, Matrix.one_apply, apply_ite snd]

/-- A point of `GL_n` with values in `k[ε]` is in the tangent group if and only if its matrix
reduces to the identity modulo `ε`. -/
theorem mem_tangentGroup_iff {x : points 𝔾𝕃(n; k) (DualNumber k)} :
    x ∈ tangentGroup 𝔾𝕃(n; k) ↔
      ((homMulEquiv n k (DualNumber k) x : GL n (DualNumber k)) :
        Matrix n n (DualNumber k)).map fst = 1 := by
  rw [mem_tangentGroup, points.map, ← (homMulEquiv n k k).injective.eq_iff,
    homMulEquiv_specMap_comp, map_one, Units.ext_iff]
  rfl

/-- The tangent group of `GL_n` is `gl_n`: a point `1 + εX` goes to its `ε`-part `X`. -/
noncomputable def tangentGroupEquivMatrix : tangentGroup 𝔾𝕃(n; k) ≃ Matrix n n k where
  toFun x := ((homMulEquiv n k (DualNumber k) x.1 : GL n (DualNumber k)) :
    Matrix n n (DualNumber k)).map snd
  invFun X := ⟨(homMulEquiv n k (DualNumber k)).symm (dualUnit X), by
    rw [mem_tangentGroup_iff, MulEquiv.apply_symm_apply, map_fst_dualUnit]⟩
  left_inv x := by
    refine Subtype.ext ((MulEquiv.symm_apply_eq _).2 (Units.ext ?_))
    rw [coe_dualUnit]
    exact (Matrix.eq_one_add_map_inr_of_map_fst_eq_one ((mem_tangentGroup_iff n k).1 x.2)).symm
  right_inv X := by
    simp only [MulEquiv.apply_symm_apply, map_snd_dualUnit]

theorem tangentGroupEquivMatrix_apply (x : tangentGroup 𝔾𝕃(n; k)) :
    tangentGroupEquivMatrix n k x = ((homMulEquiv n k (DualNumber k) x.1 : GL n (DualNumber k)) :
      Matrix n n (DualNumber k)).map snd :=
  rfl

theorem tangentGroupEquivMatrix_symm_apply (X : Matrix n n k) :
    ((tangentGroupEquivMatrix n k).symm X : points 𝔾𝕃(n; k) (DualNumber k)) =
      (homMulEquiv n k (DualNumber k)).symm (dualUnit X) :=
  rfl

theorem homMulEquiv_eq_dualUnit (x : tangentGroup 𝔾𝕃(n; k)) :
    homMulEquiv n k (DualNumber k) x.1 = dualUnit (tangentGroupEquivMatrix n k x) := by
  rw [← MulEquiv.eq_symm_apply, ← tangentGroupEquivMatrix_symm_apply, Equiv.symm_apply_apply]

/-- The group law of the tangent group of `GL_n` is the addition of matrices:
`(1 + εX)(1 + εY) = 1 + ε(X + Y)`. -/
theorem tangentGroupEquivMatrix_mul (x y : tangentGroup 𝔾𝕃(n; k)) :
    tangentGroupEquivMatrix n k (x * y) =
      tangentGroupEquivMatrix n k x + tangentGroupEquivMatrix n k y := by
  simp only [tangentGroupEquivMatrix_apply, Subgroup.coe_mul, map_mul, Units.val_mul]
  exact Matrix.map_snd_mul_of_map_fst_eq_one ((mem_tangentGroup_iff n k).1 x.2)
    ((mem_tangentGroup_iff n k).1 y.2)

/-- The matrix of a tangent vector of `GL_n`: the infinitesimal point `1 + εX` goes to `X`. -/
noncomputable def toMatrix (x : GrpObj.Lie 𝔾𝕃(n; k)) : Matrix n n k :=
  ((homMulEquiv n k (DualNumber k)
    (GrpObj.infPointsEquivTangentGroup 𝔾𝕃(n; k) ((GrpObj.lieEquiv 𝔾𝕃(n; k)).symm x)).1 :
      GL n (DualNumber k)) : Matrix n n (DualNumber k)).map snd

theorem toMatrix_eq (x : GrpObj.Lie 𝔾𝕃(n; k)) :
    toMatrix n k x = tangentGroupEquivMatrix n k
      (GrpObj.infPointsEquivTangentGroup 𝔾𝕃(n; k) ((GrpObj.lieEquiv 𝔾𝕃(n; k)).symm x)) :=
  rfl

/-- An infinitesimal point `u` of `GL_n`, pulled back to `Spec k[ε][δ]` along a map
`f : (Spec k)[ε][δ] ⟶ (Spec k)[ε]` coming from `φ : k[ε] → k[ε][δ]`, is the matrix `φ(1 + εX)`. -/
theorem homMulEquiv_inv_dualNumbers₂ToSpecOver_comp
    {f : Scheme.dualNumbers₂Over (Spec (.of k)) ⟶ Scheme.dualNumbersOver (Spec (.of k))}
    {φ : DualNumber k →ₐ[k] DualNumber (DualNumber k)}
    (hf : f ≫ dualNumbersToSpecOver =
      dualNumbers₂ToSpecOver ≫ (Spec.map (CommRingCat.ofHom φ.toRingHom)).asOver _)
    (u : GrpObj.infPoints 𝔾𝕃(n; k)) :
    homMulEquiv n k _ (inv dualNumbers₂ToSpecOver ≫ f ≫ u.1) =
      Matrix.GeneralLinearGroup.map φ.toRingHom (dualUnit (tangentGroupEquivMatrix n k
        (GrpObj.infPointsEquivTangentGroup 𝔾𝕃(n; k) u))) := by
  rw [← homMulEquiv_eq_dualUnit, ← homMulEquiv_specMap_comp,
    GrpObj.coe_infPointsEquivTangentGroup_apply, (IsIso.eq_comp_inv _).2 hf]
  simp only [Category.assoc, IsIso.inv_hom_id_assoc]

/-- The bracket of infinitesimal points of `GL_n` is the commutator of matrices: the mixed term of
`(1 + εX)(1 + δY)(1 - εX)(1 - δY) = 1 + εδ(XY - YX)`. -/
theorem tangentGroupEquivMatrix_infBracket (v w : GrpObj.infPoints 𝔾𝕃(n; k)) :
    tangentGroupEquivMatrix n k
        (GrpObj.infPointsEquivTangentGroup 𝔾𝕃(n; k) (GrpObj.infBracket _ v w)) =
      ⁅tangentGroupEquivMatrix n k (GrpObj.infPointsEquivTangentGroup 𝔾𝕃(n; k) v),
        tangentGroupEquivMatrix n k (GrpObj.infPointsEquivTangentGroup 𝔾𝕃(n; k) w)⁆ := by
  set e := GrpObj.infPointsEquivTangentGroup 𝔾𝕃(n; k)
  set X := tangentGroupEquivMatrix n k (e v)
  set Y := tangentGroupEquivMatrix n k (e w)
  set Z := tangentGroupEquivMatrix n k (e (GrpObj.infBracket _ v w))
  have hmix : Scheme.dualNumbersMulOver _ ≫ (GrpObj.infBracket _ v w).1 =
      GrpObj.toε _ v * GrpObj.toδ _ w * (GrpObj.toε _ v)⁻¹ * (GrpObj.toδ _ w)⁻¹ :=
    congrArg Subtype.val ((GrpObj.mixedEquiv _).apply_symm_apply _)
  have key := congrArg (fun z ↦ homMulEquiv n k _ (inv dualNumbers₂ToSpecOver ≫ z)) hmix
  simp only [MonObj.comp_mul, GrpObj.comp_inv, map_mul, map_inv, GrpObj.toε, GrpObj.toδ] at key
  rw [homMulEquiv_inv_dualNumbers₂ToSpecOver_comp n k
      dualNumbersMulOver_comp_dualNumbersToSpecOver,
    homMulEquiv_inv_dualNumbers₂ToSpecOver_comp n k
      dualNumbersProjεOver_comp_dualNumbersToSpecOver,
    homMulEquiv_inv_dualNumbers₂ToSpecOver_comp n k
      dualNumbersProjδOver_comp_dualNumbersToSpecOver] at key
  have hZ : Z = ((Matrix.GeneralLinearGroup.map (DualNumber.mulAlgHom (R := k)).toRingHom
      (dualUnit Z) : GL n (DualNumber (DualNumber k))) : Matrix n n (DualNumber (DualNumber k))).map
        (fun z ↦ z.snd.snd) := by
    ext i j
    simp [coe_dualUnit, DualNumber.mulAlgHom, DualNumber.mulRingHom, Matrix.one_apply,
      apply_ite, -DualNumber.inr_eq_smul_eps]
  rw [hZ, key, Ring.lie_def, ← Matrix.map_snd_snd_commutator]
  have hcoe (f : DualNumber k →+* DualNumber (DualNumber k)) (A : GL n (DualNumber k)) :
      ((Matrix.GeneralLinearGroup.map f A : GL n _) : Matrix n n (DualNumber (DualNumber k))) =
        (A : Matrix n n (DualNumber k)).map f :=
    rfl
  have hP : ((Matrix.GeneralLinearGroup.map (inlAlgHom k (DualNumber k) (DualNumber k)).toRingHom
      (dualUnit X) : GL n _) : Matrix n n (DualNumber (DualNumber k))) =
        1 + X.map fun a ↦ inl (inr a) := by
    ext i j : 1
    refine TrivSqZeroExt.ext ?_ ?_ <;>
      simp [coe_dualUnit, Matrix.one_apply, apply_ite fst, apply_ite snd,
        -DualNumber.inr_eq_smul_eps]
  have hPi : ((Matrix.GeneralLinearGroup.map (inlAlgHom k (DualNumber k) (DualNumber k)).toRingHom
      (dualUnit X)⁻¹ : GL n _) : Matrix n n (DualNumber (DualNumber k))) =
        1 - X.map fun a ↦ inl (inr a) := by
    rw [hcoe, coe_dualUnit_inv]
    ext i j : 1
    refine TrivSqZeroExt.ext ?_ ?_ <;>
      simp [Matrix.one_apply, apply_ite fst, apply_ite snd,
        -DualNumber.inr_eq_smul_eps]
  have hQ : ((Matrix.GeneralLinearGroup.map (DualNumber.mapInlAlgHom (R := k)).toRingHom
      (dualUnit Y) : GL n _) : Matrix n n (DualNumber (DualNumber k))) =
        1 + Y.map fun b ↦ inr (inl b) := by
    ext i j : 1
    refine TrivSqZeroExt.ext ?_ ?_ <;>
      simp [coe_dualUnit, DualNumber.mapInlAlgHom, Matrix.one_apply, apply_ite fst,
        apply_ite snd, -DualNumber.inr_eq_smul_eps]
  have hQi : ((Matrix.GeneralLinearGroup.map (DualNumber.mapInlAlgHom (R := k)).toRingHom
      (dualUnit Y)⁻¹ : GL n _) : Matrix n n (DualNumber (DualNumber k))) =
        1 - Y.map fun b ↦ inr (inl b) := by
    rw [hcoe, coe_dualUnit_inv]
    ext i j : 1
    refine TrivSqZeroExt.ext ?_ ?_ <;>
      simp [DualNumber.mapInlAlgHom, Matrix.one_apply, apply_ite fst,
        apply_ite snd, -DualNumber.inr_eq_smul_eps]
  rw [Units.val_mul, Units.val_mul, Units.val_mul, ← map_inv, ← map_inv, hP, hQ, hPi, hQi]

/-- `Lie(GL_n) → gl_n` as a homomorphism of Lie algebras: the bracket is preserved because the
mixed term of the commutator `(1 + εX)(1 + δY)(1 - εX)(1 - δY) = 1 + εδ(XY - YX)` is the matrix
commutator. -/
noncomputable def toMatrixLieHom : GrpObj.Lie 𝔾𝕃(n; k) →ₗ⁅k⁆ Matrix n n k where
  toFun := toMatrix n k
  map_add' x y := by
    rw [toMatrix_eq, toMatrix_eq, toMatrix_eq, GrpObj.lieEquiv_symm_add, map_mul,
      tangentGroupEquivMatrix_mul]
  map_smul' c x := by
    rw [toMatrix_eq, toMatrix_eq, RingHom.id_apply,
      show c • x = (Scheme.ΓSpecIso (.of k)).inv.hom c • x from rfl, GrpObj.lieEquiv_symm_smul,
      tangentGroupEquivMatrix_apply, tangentGroupEquivMatrix_apply,
      GrpObj.coe_infPointsEquivTangentGroup_infPointsScale, points.map, homMulEquiv_specMap_comp]
    ext i j
    simp [Matrix.GeneralLinearGroup.map]
  map_lie' {x y} := by
    rw [toMatrix_eq, toMatrix_eq, toMatrix_eq, GrpObj.lie_def, Equiv.symm_apply_apply,
      tangentGroupEquivMatrix_infBracket]

/-- `Lie(GL_n) → gl_n` is bijective: every infinitesimal point of `GL_n` is uniquely `1 + εX`. -/
theorem bijective_toMatrixLieHom : Function.Bijective (toMatrixLieHom n k) :=
  ((tangentGroupEquivMatrix n k).bijective.comp
    (GrpObj.infPointsEquivTangentGroup 𝔾𝕃(n; k)).bijective).comp
      (GrpObj.lieEquiv 𝔾𝕃(n; k)).symm.bijective

/-- The Lie algebra of the general linear group is `gl_n`, the matrices with the commutator
bracket: the tangent vector `1 + εX` corresponds to `X`. (blueprint: `sk-d-tangent`) -/
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
  obtain ⟨x, rfl⟩ : ∃ x, lieAlgebraEquivMatrix n k x = X := (lieAlgebraEquivMatrix n k).surjective X
  rw [LieEquiv.symm_apply_apply, lieAlgebraEquivMatrix_apply, toMatrix_eq,
    ← tangentGroupEquivMatrix_symm_apply, Equiv.symm_apply_apply]

end GeneralLinear

/-! ### Rational representations -/

section RationalHom

variable {k : Type u} [CommRing k] (G : Over (Spec (.of k))) [GrpObj G]
  (m : Type u) [Fintype m] [DecidableEq m]

/-- A rational representation of a group scheme `G` over `k` on `k^m`: a morphism of schemes
`G ⟶ GL_m` over `k`, required to be a homomorphism of group schemes through an `IsMonHom`
instance. (blueprint: `sk-d-tangent`) -/
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

/-- The differential `dr : Lie(G) → gl_m` of a rational representation `r`: the differential of
the homomorphism of group schemes `G ⟶ GL_m`, read in `gl_m` through `Lie(GL_m) = gl_m`. It is a
homomorphism of Lie algebras. (blueprint: `sk-d-tangent`) -/
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
  sorry

end RationalHom

end RationalHom

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
