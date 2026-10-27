/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q42
-/
module

public import Sheaf.AlgebraicGeometry.LinearGroupSchemes
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs

import Mathlib.RingTheory.TensorProduct.Maps
import Sheaf.LinearAlgebra.CommutingEndomorphismsCommonEigenvector

/-! # An eigenline for a commutative group scheme

Source: Milne, Algebraic Groups (2017), Definition 16.1, printed p.324,
Lemma 16.11, printed p.327, and Corollary 16.14, printed p.329.
(blueprint: lem-sfb-commutative-group-representation-eigenline)

The chosen basis identifies GL(V) with the existing general linear group scheme.
Stability means preservation of the image of A tensor L in A tensor V, over every
commutative test algebra, including nonreduced algebras. The multiplicative group
is GL_1, exactly as in the node. Affineness makes the structure map quasi-compact,
so locally finite type supplies the stated finite-type hypothesis.
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory
open scoped TensorProduct MonObj

namespace AlgebraicGeometry.GeneralLinearGroup

/-- A nonzero finite-dimensional rational module of a commutative affine finite-type
group scheme has a stable line on which the group acts through a regular character.
Source: Milne, Definition 16.1, p.324, and Corollary 16.14, p.329
(blueprint: lem-sfb-commutative-group-representation-eigenline).

Proof, following the five steps of the node:
1. Put B = k[G] and evaluate the representation at the universal B-point. Expand
   its finitely many matrix entries in a basis c_i of their k-linear span. This
   gives a universal matrix sum_i c_i T_i with T_i in End_k(V). Naturality gives
   r_A(g) = sum_i g(c_i) (T_i)_A for every test algebra A and point g.
   Use def-weil-affine-spectrum and def-sc-general-linear-group.
2. The two universal points over B tensor_k B commute because G is commutative.
   Their matrices therefore commute. The coefficient of c_i tensor c_j in the
   commutator is T_i T_j - T_j T_i. Extend the c_i to a basis of B and apply the
   tensor products of coordinate functionals to extract these coefficients.
   Thus all T_i commute. Use lem-weil-pbc-algebra-tensor-pushout-universal-property
   and def-weil-pbc-module-tensor-product; no density of rational points is used.
3. Apply lem-sfb-commuting-endomorphisms-common-eigenvector to obtain x nonzero
   with T_i x = lambda_i x. Set L = k x and a = sum_i lambda_i c_i in B.
   The universal formula gives r_A(g)(1 tensor x) = g(a)(1 tensor x).
   A-linearity proves stability of A tensor L and dim_k L = 1.
4. In a basis beginning with x the universal matrix has first column (a,0,...,0).
   Its inverse preserves the same line, with first coefficient b. Multiplying
   gives ab = 1. Hence a defines a regular map chi : G to G_m = GL_1 by the
   affine-spectrum and general-linear-group point dictionaries.
5. Apply r_A(gh) = r_A(g)r_A(h) to 1 tensor x. Comparing its coordinate in a
   base-changed basis proves chi_A(gh) = chi_A(g)chi_A(h), and the identity law
   follows likewise. Thus chi is a group-scheme homomorphism. Linearity extends
   the displayed formula to every vector of L. This works in every characteristic,
   without smoothness, reducedness or connectedness, and also for the zero algebra.
-/
theorem exists_eigenline_of_isCommMonObj
    {k : Type u} [Field k] [IsAlgClosed k]
    (G : Over (Spec (.of k))) [GrpObj G] [IsCommMonObj G] [IsAffine G.left]
    [LocallyOfFiniteType G.hom]
    {V : Type v} [AddCommGroup V] [Module k V] [FiniteDimensional k V] [Nontrivial V]
    {n : Type u} [Fintype n] [DecidableEq n] (b : Module.Basis n k V)
    (r : G ⟶ GeneralLinearGroup n k) [IsMonHom r] :
    ∃ L : Submodule k V, Module.finrank k L = 1 ∧
      ∃ χ : G ⟶ GeneralLinearGroup (LinearGroupSchemes.Index.{u} 1) k,
        IsMonHom χ ∧
        ∀ (A : Type u) [CommRing A] [Algebra k A]
          (g : (Spec (.of A)).asOver (Spec (.of k)) ⟶ G),
          (∀ z ∈ LinearMap.range (L.subtype.baseChange A),
            (Matrix.GeneralLinearGroup.toLin' (b.baseChange A)
              (homMulEquiv n k A (g ≫ r))).toLinearEquiv z ∈
                LinearMap.range (L.subtype.baseChange A)) ∧
          ∀ x ∈ L,
            (Matrix.GeneralLinearGroup.toLin' (b.baseChange A)
              (homMulEquiv n k A (g ≫ r))).toLinearEquiv (1 ⊗ₜ[k] x) =
                ((homMulEquiv (LinearGroupSchemes.Index.{u} 1) k A (g ≫ χ) :
                  Matrix (LinearGroupSchemes.Index.{u} 1) (LinearGroupSchemes.Index.{u} 1) A)
                    ⟨0⟩ ⟨0⟩) • (1 ⊗ₜ[k] x) := by
  sorry

end AlgebraicGeometry.GeneralLinearGroup
