/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q84
-/
module

public import Sheaf.AlgebraicGeometry.LinearGroupSchemes
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Defs
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Sheaf.AlgebraicGeometry.AffineFiniteTypeAlgebra
import Sheaf.AlgebraicGeometry.RationalRepresentationComoduleDictionary

/-! # Unipotence is invariant under field extension

Source: Milne, Algebraic Groups (2017), Corollary 14.9, p.282, and
Theorem 14.5(a),(b), pp.281--282 (blueprint: lem-sfb-unipotence-field-extension).

A closed group embedding into GL_n satisfying the unitriangular equations on all
algebra-valued points is precisely a closed group embedding into U_n: the equations
cut out U_n as a closed subgroup of GL_n. This formulation includes nonreduced groups.
Scalar extension uses the recorded pullback functor with its induced group law.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- An affine group scheme of finite type admits a closed unitriangular embedding over k
if and only if its scalar extension does over an arbitrary field extension K/k.
No smoothness, connectedness, perfectness or algebraicity of the field extension is assumed.
Source: Milne, Algebraic Groups (2017), Corollary 14.9, p.282, and Theorem 14.5(a),(b),
pp.281--282 (blueprint: lem-sfb-unipotence-field-extension).

Proof:
1. Base change a closed embedding into U_n, using
   lem-weil-pbc-closed-immersion-base-change. The affine fibre-product and tensor-pushout
   lemmas identify its target with U_n over K: K tensor k[x_ij : i < j] is K[x_ij : i < j],
   compatibly with multiplication, identity and inverse.
2. Conversely, a nonzero finite-dimensional rational G-module remains nonzero over K.
   The base-changed group is affine of finite type by lem-pc-affine-finite-type-algebra
   and the affine tensor-product description. Apply
   lem-sfb-unitriangular-subgroup-rational-fixed-vector to its scalar extension.
   The comparison of lem-sfb-rational-fixed-space-base-change identifies the nonzero
   invariant with an element of V^G tensor K. Thus V^G is nonzero: a tensor product of
   the zero space is zero, by def-weil-pbc-module-tensor-product.
3. Induct on positive dimension. Choose a nonzero rational fixed vector and extend it
   to a basis (lem-weil-pbc-vector-space-basis-through-vector). The first column of every
   action matrix is the first standard basis vector. Block multiplication and inversion
   give a natural representation on the quotient by this fixed line; the finite-dimensional
   clause of lem-sfb-rational-representation-comodule-dictionary makes it rational.
4. Apply induction to the quotient, lift its basis, and put the fixed vector first.
   Independence and spanning follow by projection to the quotient. All matrices over every
   test algebra are then upper unitriangular, including the one-dimensional base case.
5. Choose a closed faithful representation by
   lem-sfb-affine-group-faithful-linear-representation and apply the preceding flag argument.
   Conjugation by the resulting constant basis matrix is an automorphism of GL_n and
   preserves closedness (lem-weil-pbc-closed-immersion-affine-cover-criterion).
6. Evaluate at the universal coordinate-valued point. The surjective coordinate map
   k[GL_n] to k[G] kills x_ij for i > j and x_ii - 1. It factors surjectively through
   their quotient k[U_n], since the determinant becomes 1. The affine closed-immersion
   criterion gives a closed immersion into U_n. Its group compatibility follows from
   that of the original representation on every algebra-valued point. -/
theorem unitriangularEmbedding_iff_baseChange
    {k K : Type u} [Field k] [Field K] [Algebra k K]
    (G : Grp (Over (Spec (.of k)))) [IsAffine G.X.left]
    [LocallyOfFiniteType G.X.hom] [QuasiCompact G.X.hom] :
    (∃ n : ℕ, 0 < n ∧
      ∃ r : G.X ⟶ GeneralLinearGroup (ULift.{u} (Fin n)) k,
        IsClosedSubgroupScheme r ∧
        ∀ (R : Type u) [CommRing R] [Algebra k R]
          (x : (Spec (.of R)).asOver (Spec (.of k)) ⟶ G.X),
          (∀ i : Fin n,
            (GeneralLinearGroup.homMulEquiv (ULift.{u} (Fin n)) k R (x ≫ r)).val
              ⟨i⟩ ⟨i⟩ = 1) ∧
          (∀ i j : Fin n, j < i →
            (GeneralLinearGroup.homMulEquiv (ULift.{u} (Fin n)) k R (x ≫ r)).val
              ⟨i⟩ ⟨j⟩ = 0)) ↔
    (∃ n : ℕ, 0 < n ∧
      ∃ r : ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k K)))).mapGrp.obj G).X
        ⟶ GeneralLinearGroup (ULift.{u} (Fin n)) K,
        IsClosedSubgroupScheme r ∧
        ∀ (R : Type u) [CommRing R] [Algebra K R]
          (x : (Spec (.of R)).asOver (Spec (.of K)) ⟶
            ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k K)))).mapGrp.obj G).X),
          (∀ i : Fin n,
            (GeneralLinearGroup.homMulEquiv (ULift.{u} (Fin n)) K R (x ≫ r)).val
              ⟨i⟩ ⟨i⟩ = 1) ∧
          (∀ i j : Fin n, j < i →
            (GeneralLinearGroup.homMulEquiv (ULift.{u} (Fin n)) K R (x ≫ r)).val
              ⟨i⟩ ⟨j⟩ = 0)) := by
  sorry

end AlgebraicGeometry
