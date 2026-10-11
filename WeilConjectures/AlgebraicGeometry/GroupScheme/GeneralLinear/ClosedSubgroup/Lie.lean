/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.RepresentationTheory.Semisimple
public import Mathlib.RingTheory.KrullDimension.Basic
public import WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear.ClosedSubgroup
public import WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear.Lie
public import WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear.Representation
public import WeilConjectures.RingTheory.HopfAlgebra.Cartier

/-!
# The Lie algebras of the closed subgroup schemes of `GL_n`

Let `V(I)` be the closed subgroup scheme of `𝔾𝕃(n; k)` cut out by a Hopf ideal `I` of the
coordinate ring `k[GL_n]` (`AlgebraicGeometry.GeneralLinearGroup.subgroupScheme`). This file
specialises the general theory of `WeilConjectures.AlgebraicGeometry.GroupScheme.Lie` and
`WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear.Lie` to these groups, in the language
of Hopf ideals used by the weight arguments: the differentials `Lie(V(J)) → Lie(V(I))` of the
closed immersions, the Lie algebra clauses of Cartier's theorem for the *reduced* identity
component `V(identityComponent I)`, the group–Lie comparison for invariant subspaces on the
matrices `zeroLocus I k`, and the Lie algebra of the *reduced* centre `V(center I)`.

Everything that holds for an arbitrary group scheme is stated there, for an arbitrary group scheme;
what remains here is specific to the reduced identity component and the reduced centre, which this
development only has in Hopf-ideal form, and to the matrix description of the points of `V(I)`.

## Main definitions

- `AlgebraicGeometry.GeneralLinearGroup.lieAlgebraMap`: the differential of the closed immersion
  `V(J) ⟶ V(I)` of closed subgroup schemes of `GL_n`.

## Main results

- `AlgebraicGeometry.GeneralLinearGroup.lie_mem_range_lieAlgebraMap`,
  `AlgebraicGeometry.GeneralLinearGroup.lie_mem_range_lieAlgebraMap_identityComponent`: if the
  closed subgroup `V(J) ⊆ V(I)` contains the commutators of `V(I)`, then the Lie algebra of `V(J)`,
  and of its identity component, contains the brackets of the Lie algebra of `V(I)`, respectively of
  its identity component.
- `AlgebraicGeometry.GeneralLinearGroup.surjective_mulCenterIdentityComponent`,
  `AlgebraicGeometry.GeneralLinearGroup.exists_mul_eq_of_containsCommutators`: the
  central–geometric product `G° = Z(G°)° H°` for such a pair with `G°` acting semisimply on `kⁿ`,
  as a morphism of group schemes and on `k`-points.
- `AlgebraicGeometry.GeneralLinearGroup.lieAlgebraMap_identityComponent_bijective`,
  `AlgebraicGeometry.GeneralLinearGroup.finrank_lie_eq_ringKrullDim`: the Lie algebra only sees
  the reduced identity component and has the dimension of the group (Cartier's theorem).
- `AlgebraicGeometry.GeneralLinearGroup.dualUnit_mem_zeroLocus_identityComponent`,
  `AlgebraicGeometry.GeneralLinearGroup.mem_range_dualCotangentToMatrixₗ`,
  `AlgebraicGeometry.GeneralLinearGroup.finrank_cotangent_eq_finrank_range_dualCotangentToMatrixₗ`:
  the matrix form of these clauses of Cartier's theorem, for the points `1 + εX` of `V(I)` over the
  dual numbers: in characteristic zero they are points of the reduced identity component, and they
  are the dual of the cotangent space `𝔪/𝔪²` of `k[GL_n] ⧸ I` at the identity.
- `AlgebraicGeometry.GeneralLinearGroup.eq_of_le_of_bijective_lieAlgebraMap`: a closed subgroup
  of a connected matrix group with the same Lie algebra is the whole group.
- `AlgebraicGeometry.GeneralLinearGroup.invariant_iff_differential_invariant`,
  `AlgebraicGeometry.GeneralLinearGroup.range_lieAlgebraMap_center`: the group–Lie comparison.

## Blueprint

- `sk-d-tangent`: the Lie algebra of an algebraic group as its tangent space at the identity.
- `sk-i-cartier`: the Lie algebra clauses of Cartier's theorem.
- `sk-p-comparison`: invariant subspaces and the centre, for the group and for its Lie algebra.
- `sk-i-restriction`, `sk-p-product`: pairs `V(J) ⊆ V(I)` with `⁅V(I), V(I)⁆ ⊆ V(J)`, and the
  central–geometric product.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory CartesianMonoidalCategory TrivSqZeroExt
open scoped MonObj Matrix

attribute [local instance 100] LieRing.ofAssociativeRing

namespace AlgebraicGeometry.GeneralLinearGroup

open Matrix.GeneralLinearGroup

section ClosedSubgroup

variable {n : Type u} [Fintype n] [DecidableEq n] {k : Type u} [Field k]
  {I J : Ideal (CoordinateRing n k)} [I.IsHopfIdeal k] [J.IsHopfIdeal k]

/-- The differential `Lie(V(J)) → Lie(V(I))` of the closed immersion `V(J) ⟶ V(I)`, an injective
homomorphism of Lie algebras. (blueprint: `sk-d-tangent`) -/
noncomputable abbrev lieAlgebraMap (h : I ≤ J) :
    GrpObj.Lie (subgroupScheme J) →ₗ⁅k⁆ GrpObj.Lie (subgroupScheme I) :=
  GrpObj.differential (subgroupSchemeHom h)

theorem lieAlgebraMap_injective (h : I ≤ J) : Function.Injective (lieAlgebraMap h) :=
  GrpObj.differential_injective _

/-- If the closed subgroup `V(J) ⊆ V(I)` contains the commutators of `V(I)`, then the bracket of two
tangent vectors of `V(I)` is a tangent vector of `V(J)`: the bracket is the mixed term of the
commutator of the points `1 + εX` and `1 + δY` over `k[ε, δ]/(ε², δ²)`.
(blueprint: `sk-i-restriction`) -/
theorem lie_mem_range_lieAlgebraMap (h : I ≤ J) [IsMonHom.ContainsCommutators (subgroupSchemeHom h)]
    (X Y : GrpObj.Lie (subgroupScheme I)) : ⁅X, Y⁆ ∈ (lieAlgebraMap h).range :=
  GrpObj.lie_mem_range_differential_of_containsCommutators (subgroupSchemeHom h) X Y

end ClosedSubgroup

section Cartier

variable {n : Type u} [Fintype n] [DecidableEq n] {k : Type u} [Field k]
  (I : Ideal (CoordinateRing n k)) [I.IsHopfIdeal k]

/-- The point `1 + εX` of `GL_n` with values in the dual numbers reduces to the identity modulo
`ε`: as an algebra map on the coordinate ring, its reduction is the counit. -/
theorem fst_comp_evalAlgHom_dualUnit (X : Matrix n n k) :
    (fstHom k k k).comp (evalAlgHom (dualUnit X)) =
      Bialgebra.counitAlgHom k (CoordinateRing n k) := by
  rw [← evalAlgHom_map, map_fstHom_dualUnit]
  rfl

/-- In characteristic zero, every tangent vector of `G = V(I)` is tangent to the reduced identity
component, in matrix form: a point `1 + εX` of `V(I)` with values in the dual numbers is a point
of `V(identityComponent I)`.

`identityComponent I` is the ideal of the *reduced* identity component. By Cartier's lemma
(`Bialgebra.isPrime_iInf_pow_ker_counitAlgHom`) the functions on `G` vanishing near the identity
form a prime ideal `P`, so `V(P)` is an irreducible closed subset of `V(I)` through the identity,
contained in the identity component. A function vanishing on the identity component thus lies
in `P`, hence vanishes in the local ring at the identity and on every tangent vector there.
(blueprint: `lem-wf-same-lie-closed-subgroup`, clause (3)) -/
theorem dualUnit_mem_zeroLocus_identityComponent [IsAlgClosed k] [CharZero k] {X : Matrix n n k}
    (hX : dualUnit X ∈ zeroLocus I (DualNumber k)) :
    dualUnit X ∈ zeroLocus (identityComponent I) (DualNumber k) := by
  rw [mem_zeroLocus] at hX ⊢
  intro a ha
  set B := CoordinateRing n k ⧸ I
  set P := ⨅ r : ℕ, RingHom.ker (Bialgebra.counitAlgHom k B) ^ r
  have hP : P.IsPrime := Bialgebra.isPrime_iInf_pow_ker_counitAlgHom k B
  set P' := P.comap (Ideal.Quotient.mk I)
  have hP' : P'.IsPrime := Ideal.IsPrime.comap _ (hK := hP)
  have hIP : I ≤ P' := fun b hb ↦ by
    rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.2 hb]
    exact zero_mem _
  have h1 : toPrimeSpectrum (1 : GL n k) ∈
      PrimeSpectrum.zeroLocus (P' : Set (CoordinateRing n k)) := fun b hb ↦ by
    have hb' : Ideal.Quotient.mk I b ∈ RingHom.ker (Bialgebra.counitAlgHom k B) := by
      have := (Submodule.mem_iInf _).1 (Ideal.mem_comap.1 hb) 1
      rwa [pow_one] at this
    rw [RingHom.mem_ker, Bialgebra.counitAlgHom_apply, Bialgebra.Quotient.counit_mk] at hb'
    exact hb'
  have hsub : PrimeSpectrum.zeroLocus (P' : Set (CoordinateRing n k)) ⊆
      connectedComponentIn (PrimeSpectrum.zeroLocus (I : Set (CoordinateRing n k)))
        (toPrimeSpectrum 1) :=
    (IsPreirreducible.isPreconnected ((PrimeSpectrum.isIrreducible_zeroLocus_iff P').2
      (by rw [hP'.radical]; exact hP')).2).subset_connectedComponentIn h1
        (PrimeSpectrum.zeroLocus_anti_mono hIP)
  have haP : Ideal.Quotient.mk I a ∈ P := by
    have := PrimeSpectrum.vanishingIdeal_anti_mono hsub ha
    rwa [PrimeSpectrum.vanishingIdeal_zeroLocus_eq_radical, hP'.radical] at this
  have := Algebra.FiniteType.isNoetherianRing k (CoordinateRing n k)
  obtain ⟨s, hs, hsa⟩ := AlgHom.mem_iInf_pow_ker_iff.1 haP
  let φ : B →ₐ[k] DualNumber k := Ideal.Quotient.liftₐ I (evalAlgHom (dualUnit X)) hX
  have hφ : (fstHom k k k).comp φ = Bialgebra.counitAlgHom k B := by
    refine Ideal.Quotient.algHom_ext _ ?_
    rw [AlgHom.comp_assoc]
    exact fst_comp_evalAlgHom_dualUnit X
  have hunit : IsUnit (φ s) := by
    rw [TrivSqZeroExt.isUnit_iff_isUnit_fst]
    have := congrArg (· s) hφ
    simp only [AlgHom.comp_apply, fstHom_apply] at this
    rw [this, hs]
    exact isUnit_one
  have h := congrArg φ hsa
  rw [map_mul, map_zero] at h
  exact (hunit.mul_right_eq_zero).1 h

/-- In characteristic zero, every tangent vector of `G = V(I)` is tangent to the reduced identity
component `V(identityComponent I)`: the differential `Lie(G°) → Lie(G)` is bijective.

`CharZero` is needed because `identityComponent I` is the ideal of the *reduced* identity
component. The matrix form, for the points `1 + εX` of `V(I)` over the dual numbers, is
`dualUnit_mem_zeroLocus_identityComponent`. Proof sketch (not formalised): by Cartier's theorem
(`AlgebraicGeometry.GrpObj.isReduced_of_charZero`) `V(I)` is reduced, so the open identity
component `AlgebraicGeometry.GrpObj.identityComponent (subgroupScheme I)`, whose differential is
bijective by `AlgebraicGeometry.GrpObj.differential_identityComponentι_bijective`, is the reduced
closed subscheme on the connected component of the identity, that is `V(identityComponent I)`
(`range_subgroupSchemeHom_le_identityComponent`). (blueprint: `sk-i-cartier`) -/
theorem lieAlgebraMap_identityComponent_bijective [IsAlgClosed k] [CharZero k] :
    Function.Bijective (lieAlgebraMap (le_identityComponent I)) := by
  sorry

/-- Over an algebraically closed field of characteristic zero, the Lie algebra of an algebraic
group is the Lie algebra of its reduced identity component. (blueprint: `sk-i-cartier`) -/
noncomputable def lieAlgebraEquivIdentityComponent [IsAlgClosed k] [CharZero k] :
    GrpObj.Lie (subgroupScheme (identityComponent I)) ≃ₗ⁅k⁆ GrpObj.Lie (subgroupScheme I) :=
  LieEquiv.ofBijective _ (lieAlgebraMap_identityComponent_bijective I)

/-- Cartier's theorem, Lie algebra form: over a field of characteristic zero, the Lie algebra of
a closed subgroup scheme `V(I)` has dimension the Krull dimension of its coordinate ring. This is
`AlgebraicGeometry.GrpObj.finrank_lie_eq_topologicalKrullDim` for the affine scheme
`V(I) = Spec (k[GL_n] ⧸ I)`. (blueprint: `sk-i-cartier`) -/
theorem finrank_lie_eq_ringKrullDim [CharZero k] :
    (Module.finrank k (GrpObj.Lie (subgroupScheme I)) : WithBot ℕ∞) =
      ringKrullDim (CoordinateRing n k ⧸ I) :=
  (GrpObj.finrank_lie_eq_topologicalKrullDim (subgroupScheme I)).trans
    (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim (CoordinateRing n k ⧸ I))

/-- A closed subgroup `V(J)` of a connected matrix group `V(I)` with the same Lie algebra is all of
`V(I)`, in characteristic zero: the Lie algebras have the dimensions of the groups
(`finrank_lie_eq_ringKrullDim`), and `V(I)` is irreducible
(`Matrix.GeneralLinearGroup.IsConnected.isPrime`).
(blueprint: `lem-wf-same-lie-closed-subgroup`, clause (1)) -/
theorem eq_of_le_of_bijective_lieAlgebraMap [IsAlgClosed k] [CharZero k] (hconn : IsConnected I)
    {J : Ideal (CoordinateRing n k)} [J.IsHopfIdeal k] (hIJ : I ≤ J)
    (h : Function.Bijective (lieAlgebraMap hIJ)) : J = I := by
  have := hconn.isPrime
  refine eq_of_le_of_ringKrullDim_eq I hIJ ?_
  rw [← finrank_lie_eq_ringKrullDim J, ← finrank_lie_eq_ringKrullDim I,
    (LieEquiv.ofBijective _ h).toLinearEquiv.finrank_eq]

/-! #### The tangent space at the identity, in matrices

The points `1 + εX` of `V(I)` over the dual numbers are the linear forms on the cotangent space
`𝔪/𝔪²` of the coordinate ring `k[GL_n] ⧸ I` at the identity: `X i j = ψ (x_ij - δ_ij)`. -/

local notation "𝔪" => RingHom.ker (Bialgebra.counitAlgHom k (CoordinateRing n k ⧸ I))

/-- The tangent vector `X ∈ gl_n` of a linear form `ψ` on the cotangent space at the identity of
`V(I)`: `X i j = ψ (x_ij - δ_ij)`. -/
noncomputable def dualCotangentToMatrix (ψ : Module.Dual k (𝔪).Cotangent) : Matrix n n k :=
  Matrix.of fun i j ↦ (Bialgebra.counitAlgHom k (CoordinateRing n k ⧸ I)).cotangentDerivation ψ
    (Ideal.Quotient.mk I (coord n k i j))

/-- The point `1 + εX_ψ` of `V(I)` is the dual-number point of the tangent vector `ψ`. -/
theorem evalAlgHom_dualUnit_dualCotangentToMatrix (ψ : Module.Dual k (𝔪).Cotangent) :
    evalAlgHom (k := k) (R := DualNumber k) (dualUnit (dualCotangentToMatrix I ψ)) =
      ((Bialgebra.counitAlgHom k (CoordinateRing n k ⧸ I)).toDualNumber ψ).comp
        (Ideal.Quotient.mkₐ k I) := by
  refine algHom_ext fun i j ↦ ?_
  rw [evalAlgHom_coord, coe_dualUnit, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk]
  refine TrivSqZeroExt.ext ?_ ?_
  · rw [AlgHom.fst_toDualNumber, Bialgebra.counitAlgHom_apply, Bialgebra.Quotient.counit_mk]
    rw [counit_coord]
    simp [Matrix.one_apply, apply_ite TrivSqZeroExt.fst]
  · rw [AlgHom.snd_toDualNumber]
    simp [Matrix.one_apply, apply_ite TrivSqZeroExt.snd, dualCotangentToMatrix]

theorem dualUnit_dualCotangentToMatrix_mem_zeroLocus (ψ : Module.Dual k (𝔪).Cotangent) :
    dualUnit (dualCotangentToMatrix I ψ) ∈ zeroLocus I (DualNumber k) :=
  mem_zeroLocus.2 fun a ha ↦ by
    rw [evalAlgHom_dualUnit_dualCotangentToMatrix, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk,
      Ideal.Quotient.eq_zero_iff_mem.2 ha, map_zero]

/-- `ψ ↦ X_ψ`, from the dual of the cotangent space of `k[GL_n] ⧸ I` at the identity to `gl_n`,
as a linear map. -/
noncomputable def dualCotangentToMatrixₗ : Module.Dual k (𝔪).Cotangent →ₗ[k] Matrix n n k where
  toFun := dualCotangentToMatrix I
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem dualCotangentToMatrixₗ_apply (ψ : Module.Dual k (𝔪).Cotangent) :
    dualCotangentToMatrixₗ I ψ = dualCotangentToMatrix I ψ :=
  rfl

theorem dualCotangentToMatrixₗ_injective : Function.Injective (dualCotangentToMatrixₗ I) :=
  fun ψ ψ' h ↦ by
    have h' := congrArg (fun X : Matrix n n k ↦
      evalAlgHom (k := k) (R := DualNumber k) (dualUnit X)) h
    simp only [dualCotangentToMatrixₗ_apply, evalAlgHom_dualUnit_dualCotangentToMatrix] at h'
    exact AlgHom.toDualNumber_injective (Ideal.Quotient.algHom_ext k h')

/-- The tangent vectors of `V(I)` at the identity, as matrices, are exactly the `X ∈ gl_n` with
`1 + εX ∈ V(I)`: the range of `ψ ↦ X_ψ`. -/
theorem mem_range_dualCotangentToMatrixₗ {X : Matrix n n k} :
    X ∈ LinearMap.range (dualCotangentToMatrixₗ I) ↔ dualUnit X ∈ zeroLocus I (DualNumber k) := by
  refine ⟨?_, fun hX ↦ ?_⟩
  · rintro ⟨ψ, rfl⟩
    exact dualUnit_dualCotangentToMatrix_mem_zeroLocus I ψ
  · let φ : (CoordinateRing n k ⧸ I) →ₐ[k] DualNumber k :=
      Ideal.Quotient.liftₐ I (evalAlgHom (k := k) (R := DualNumber k) (dualUnit X))
        (mem_zeroLocus.1 hX)
    have hφ : (fstHom k k k).comp φ = Bialgebra.counitAlgHom k _ := by
      refine Ideal.Quotient.algHom_ext _ ?_
      rw [AlgHom.comp_assoc]
      exact fst_comp_evalAlgHom_dualUnit _
    refine ⟨(Bialgebra.counitAlgHom k _).cotangentForm φ hφ, ?_⟩
    ext i j
    change dualCotangentToMatrix I _ i j = _
    rw [dualCotangentToMatrix, Matrix.of_apply]
    rw [← AlgHom.snd_toDualNumber, AlgHom.toDualNumber_cotangentForm]
    simp [φ, coe_dualUnit, Matrix.one_apply, apply_ite TrivSqZeroExt.snd]

/-- The dimension of the cotangent space of `k[GL_n] ⧸ I` at the identity is the dimension of
the space of matrices `X` with `1 + εX ∈ V(I)`. -/
theorem finrank_cotangent_eq_finrank_range_dualCotangentToMatrixₗ :
    Module.finrank k (𝔪).Cotangent =
      Module.finrank k (LinearMap.range (dualCotangentToMatrixₗ I)) := by
  have := Algebra.FiniteType.isNoetherianRing k (CoordinateRing n k)
  have := (Bialgebra.counitAlgHom k (CoordinateRing n k ⧸ I)).finiteDimensional_cotangent
  rw [LinearMap.finrank_range_of_inj (dualCotangentToMatrixₗ_injective I),
    Subspace.dual_finrank_eq]

end Cartier

section Comparison

variable {n : Type u} [Fintype n] [DecidableEq n] {k : Type u} [Field k]
  {I : Ideal (CoordinateRing n k)} [I.IsHopfIdeal k] {m : Type u} [Fintype m] [DecidableEq m]

/-- The group–Lie comparison for invariant subspaces, for a connected closed subgroup `V(I)` of
`GL_n` over an algebraically closed field of characteristic zero, on the matrices of
`zeroLocus I k`: a subspace is stable under `V(I)(k)` acting by a rational representation `r` if
and only if it is stable under the differential of `r`. This is
`AlgebraicGeometry.GeneralLinearGroup.RationalHom.invariant_iff_differential_invariant` for
`V(I)`, which is reduced and connected since `I` is connected. (blueprint: `sk-p-comparison`) -/
theorem invariant_iff_differential_invariant [IsAlgClosed k] [CharZero k] (hconn : IsConnected I)
    (r : RationalHom (subgroupScheme I) m) [IsMonHom r] (U : Submodule k (m → k)) :
    (∀ g : zeroLocus I k,
        U ≤ U.comap (Matrix.toLin' (r.points k (zeroLocusMulEquiv I k g)))) ↔
      ∀ X : GrpObj.Lie (subgroupScheme I), U ≤ U.comap (Matrix.toLin' (r.differential X)) :=
  haveI := isReduced_subgroupScheme I hconn.isRadical
  haveI := connectedSpace_subgroupScheme I hconn
  (zeroLocusMulEquiv I k).surjective.forall.symm.trans
    (r.invariant_iff_differential_invariant U)

/-- The Lie algebra of the reduced centre of a reduced `G = V(I)` over an algebraically closed
field is contained in the centre of the Lie algebra of `G`: the reduced centre is central
scheme-theoretically (`central_subgroupSchemeHom_le_center`), so this is
`AlgebraicGeometry.GrpObj.range_differential_le_center`. (blueprint: `sk-p-comparison`) -/
theorem range_lieAlgebraMap_center_le [IsAlgClosed k] (hI : I.IsRadical) :
    (lieAlgebraMap (le_center I)).range ≤
      (LieAlgebra.center k (GrpObj.Lie (subgroupScheme I)) : LieSubalgebra k _) :=
  GrpObj.range_differential_le_center _ fun _ a b ↦ central_subgroupSchemeHom_le_center I hI a b

/-- In characteristic zero, the centre of the Lie algebra of a connected group `G = V(I)` is
contained in the Lie algebra of the reduced centre `V(center I)`.

Proof sketch (not formalised): the centre of a connected `G` is the kernel of the adjoint
representation `Ad : G → GL(Lie G)`, whose differential is `ad`; in characteristic zero the Lie
algebra of the kernel is the kernel `𝔷(Lie G)` of the differential, and the scheme-theoretic
centre is reduced, hence is `V(center I)`. (blueprint: `sk-p-comparison`) -/
theorem le_range_lieAlgebraMap_center [IsAlgClosed k] [CharZero k] (_hconn : IsConnected I) :
    (LieAlgebra.center k (GrpObj.Lie (subgroupScheme I)) : LieSubalgebra k _) ≤
      (lieAlgebraMap (le_center I)).range := by
  sorry

/-- The group–Lie comparison for the centre: over an algebraically closed field of characteristic
zero, the Lie algebra of the centre of a connected algebraic group is the centre of its Lie
algebra. (blueprint: `sk-p-comparison`) -/
theorem range_lieAlgebraMap_center [IsAlgClosed k] [CharZero k] (hconn : IsConnected I) :
    (lieAlgebraMap (le_center I)).range =
      (LieAlgebra.center k (GrpObj.Lie (subgroupScheme I)) : LieSubalgebra k _) :=
  le_antisymm (range_lieAlgebraMap_center_le hconn.isRadical) (le_range_lieAlgebraMap_center hconn)

/-- The Lie algebra of the identity component of the centre of a connected algebraic group is the
centre of its Lie algebra, in characteristic zero: the differential of `Z(G)° ⟶ G` has as range the
centre of `Lie(G)`. (blueprint: `sk-p-comparison`) -/
theorem range_lieAlgebraMap_identityComponent_center [IsAlgClosed k] [CharZero k]
    (hconn : IsConnected I) :
    (lieAlgebraMap ((le_center I).trans (le_identityComponent (center I)))).range =
      (LieAlgebra.center k (GrpObj.Lie (subgroupScheme I)) : LieSubalgebra k _) := by
  sorry

end Comparison

/-! ### Pairs of closed subgroup schemes with commutative quotient

Let `H = V(J) ⊆ G = V(I)` be closed subgroup schemes of `GL_n`, `I ≤ J`, such that the inclusion
`H ⟶ G` contains the commutators of `G` (`AlgebraicGeometry.IsMonHom.ContainsCommutators`), the
scheme-theoretic form of `⁅G, G⁆ ⊆ H`; then `H` is normal in `G`
(`AlgebraicGeometry.IsMonHom.Normal.of_containsCommutators`). The arithmetic and geometric
monodromy groups of a represented degree datum are such a pair, and the statements of the blueprint
about them are instances of the statements of this section. -/

section Pair

variable {n : Type u} [Fintype n] [DecidableEq n] {k : Type u} [Field k]
  {I J : Ideal (CoordinateRing n k)} [I.IsHopfIdeal k] [J.IsHopfIdeal k]

/-- The brackets of the Lie algebra of `G° = V(identityComponent I)` lie in the Lie algebra of
`H° = V(identityComponent J)`, when `H = V(J) ⊆ G = V(I)` contains the commutators of `G`: in
characteristic zero the identity components have the same Lie algebras as `G` and `H`
(`lieAlgebraEquivIdentityComponent`), and the differentials of `H° ⟶ G° ⟶ G` and `H° ⟶ H ⟶ G`
agree. (blueprint: `sk-i-restriction`) -/
theorem lie_mem_range_lieAlgebraMap_identityComponent [IsAlgClosed k] [CharZero k] (h : I ≤ J)
    [IsMonHom.ContainsCommutators (subgroupSchemeHom h)]
    (X Y : GrpObj.Lie (subgroupScheme (identityComponent I))) :
    ⁅X, Y⁆ ∈ (lieAlgebraMap (identityComponent_mono I h)).range := by
  sorry

/-- The standard representation of the `k`-points of `V(I)` on `kⁿ`: a point `Spec k ⟶ V(I)` acts
through its image in `GL_n(k)` under the closed immersion `V(I) ⟶ GL_n`: the algebraic-group
module of `V(I) ⟶ GL_n`. (blueprint: `sk-d-monodromy`, `def-wf-algebraic-representations`) -/
noncomputable def standardRepresentation (I : Ideal (CoordinateRing n k)) [I.IsHopfIdeal k] :
    Representation k (points (subgroupScheme I) k) (n → k) :=
  RationalHom.representation (subgroupSchemeι I)

variable [IsAlgClosed k]

/-- The multiplication morphism `Z(G°)° × H° ⟶ G°` of group schemes, for closed subgroups
`H = V(J) ⊆ G = V(I)` of `GL_n`: the composite of the closed immersions of the two factors into
`G°` with the multiplication of `G°`. (blueprint: `sk-p-product`) -/
noncomputable def mulCenterIdentityComponent (h : I ≤ J) :
    subgroupScheme (identityComponent (center (identityComponent I))) ⊗
        subgroupScheme (identityComponent J) ⟶
      subgroupScheme (identityComponent I) :=
  (subgroupSchemeHom ((le_center _).trans (le_identityComponent _)) ⊗ₘ
      subgroupSchemeHom (identityComponent_mono I h)) ≫
    μ[subgroupScheme (identityComponent I)]

variable [CharZero k]

/-- **The central–geometric product.** Let `H = V(J) ⊆ G = V(I)` be closed subgroups of `GL_n` over
an algebraically closed field of characteristic zero such that `H` contains the commutators of `G`
and `G°` acts semisimply on `kⁿ`. Then `G° = Z(G°)° H°`: the multiplication morphism
`Z(G°)° × H° ⟶ G°` is surjective.

Proof sketch (not formalised): the Lie algebra `𝔤 = Lie G° ⊆ 𝔤𝔩_n` is a faithful semisimple Lie
representation, so `𝔤 = 𝔷(𝔤) + [𝔤, 𝔤]`; the brackets lie in `Lie H°`
(`lie_mem_range_lieAlgebraMap_identityComponent`) and `𝔷(𝔤) = Lie Z(G°)°`
(`range_lieAlgebraMap_identityComponent_center`), so `𝔤 = Lie Z(G°)° + Lie H°`. The multiplication
morphism is a homomorphism because `Z(G°)°` is central, so its image is closed
(`AlgebraicGeometry.isClosed_range_of_isMonHom`) and connected, and its Lie algebra is `𝔤`; by
Cartier's theorem it has the dimension of `G°`, hence is all of `G°`
(`AlgebraicGeometry.isIso_left_of_topologicalKrullDim_eq`). (blueprint: `sk-p-product`) -/
theorem surjective_mulCenterIdentityComponent (h : I ≤ J)
    [IsMonHom.ContainsCommutators (subgroupSchemeHom h)]
    [Representation.IsSemisimpleRepresentation (standardRepresentation (identityComponent I))] :
    Function.Surjective (mulCenterIdentityComponent h).left.base := by
  sorry

/-- The central–geometric product on `k`-points: every point of `G°` is a product `t h` of a point
`t` of `Z(G°)°` and a point `h` of `H°`. Proof sketch (not formalised): a `k`-point of `G°` lifts
along the surjective multiplication morphism to a `k`-point of `Z(G°)° × H°`
(`AlgebraicGeometry.exists_points_comp_eq_of_surjective`), whose two projections are `t` and `h`.
(blueprint: `sk-p-product`) -/
theorem exists_mul_eq_of_containsCommutators (h : I ≤ J)
    [IsMonHom.ContainsCommutators (subgroupSchemeHom h)]
    [Representation.IsSemisimpleRepresentation (standardRepresentation (identityComponent I))]
    (g : points (subgroupScheme (identityComponent I)) k) :
    ∃ (t : points (subgroupScheme (identityComponent (center (identityComponent I)))) k)
      (x : points (subgroupScheme (identityComponent J)) k),
      t ≫ subgroupSchemeHom ((le_center _).trans (le_identityComponent _)) *
        x ≫ subgroupSchemeHom (identityComponent_mono I h) = g := by
  sorry

end Pair

end AlgebraicGeometry.GeneralLinearGroup
