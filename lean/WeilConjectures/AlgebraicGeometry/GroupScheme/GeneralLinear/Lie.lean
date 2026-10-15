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

/-- The matrix of a tangent vector of `GL_n`: the infinitesimal point `1 + εX` goes to `X`. -/
noncomputable def toMatrix (x : GrpObj.Lie 𝔾𝕃(n; k)) : Matrix n n k :=
  ((homMulEquiv n k (DualNumber k)
    (GrpObj.infPointsEquivTangentGroup 𝔾𝕃(n; k) ((GrpObj.lieEquiv 𝔾𝕃(n; k)).symm x)).1 :
      GL n (DualNumber k)) : Matrix n n (DualNumber k)).map snd

/-- `Lie(GL_n) → gl_n` as a homomorphism of Lie algebras: the bracket is preserved because the
mixed term of the commutator `(1 + εX)(1 + δY)(1 - εX)(1 - δY) = 1 + εδ(XY - YX)` is the matrix
commutator. -/
noncomputable def toMatrixLieHom : GrpObj.Lie 𝔾𝕃(n; k) →ₗ⁅k⁆ Matrix n n k where
  toFun := toMatrix n k
  map_add' := by sorry
  map_smul' := by sorry
  map_lie' := by sorry

/-- `Lie(GL_n) → gl_n` is bijective: every infinitesimal point of `GL_n` is uniquely `1 + εX`. -/
theorem bijective_toMatrixLieHom : Function.Bijective (toMatrixLieHom n k) := by
  sorry

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
  sorry

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
