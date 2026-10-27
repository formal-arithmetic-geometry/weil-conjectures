/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q81
-/
module

public import Sheaf.AlgebraicGeometry.RationalRepresentationComoduleDictionary
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.LinearAlgebra.TensorProduct.Finiteness

import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.AlgebraicGeometry.Group.Affine
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction

/-! # Affine group points from tensor-compatible representation endomorphisms

Source: Milne, Algebraic Groups (2017), Theorem 9.2 and Lemma 9.1, printed pp.164--165.
(blueprint: lem-sfb-affine-group-tensor-reconstruction)

All vector spaces, test algebras and the base field lie in the fixed universe u.
The family of endomorphisms consequently lives in the containing universe u+1.
The tensor and trivial representations are specified by their actions on all test
algebras, as in the existing rational-representation/comodule dictionary.
-/

set_option autoImplicit false

@[expose] public section

universe u

open CategoryTheory
open scoped TensorProduct

namespace AlgebraicGeometry.RationalRepresentation

/-- Every tensor-compatible natural family of linear endomorphisms comes from a unique point.
Source: Milne, Algebraic Groups (2017), Theorem 9.2, printed pp.164--165.
(blueprint: lem-sfb-affine-group-tensor-reconstruction).

Proof (the ten steps of the node):
1. Split each finite-dimensional subspace inclusion by extending a basis
   (lem-weil-pbc-vector-space-basis-through-vector). Tensoring its retraction shows that
   scalar extension is injective over any R. Use the coordinate Hopf algebra A=k[G]
   (lem-sfb-affine-group-coordinate-hopf) and the tensor multiplication
   (lem-weil-pbc-algebra-tensor-pushout-universal-property).
2. The coordinate coaction makes A the regular rational representation by
   lem-sfb-rational-representation-comodule-dictionary. Every finite subset lies in a
   finite subrepresentation by lem-sfb-comodule-finite-subrepresentation; any two such
   subrepresentations lie in a common third one.
3. For f in A choose such a U containing f and set l(f)=i_U(lambda_U(1 tensor f)).
   Naturality for inclusions into a common third subrepresentation makes this independent
   of U and k-linear. Extend to an R-linear L on R tensor A using
   lem-weil-pbc-module-base-change-universal-property. Its restriction to U_R is lambda_U.
4. For finite U,W choose a finite Z containing their products. Multiplication U tensor W
   to Z is equivariant: Delta(uw)=Delta(u)Delta(w), and split inclusions detect equality
   of the coactions. Its domain is finite-dimensional by tensor generators
   (def-weil-finite-dimensional-subspace, def-weil-pbc-module-tensor-product).
5. Tensor compatibility and naturality for this multiplication show L(xy)=L(x)L(y),
   first on pure tensors and then on their finite sums. The equivariant unit k to A,
   with trivial-representation compatibility, gives L(1)=1.
6. Compose L with the scalar-extended counit epsilon_R and restrict along 1 tensor A.
   This is a k-algebra map g*:A to R, hence a point g by def-weil-affine-spectrum.
7. For phi:V to k, the coefficient map f_phi=(phi tensor 1)c_V is equivariant into A
   by coassociativity, and epsilon f_phi=phi by counitality (the dictionary).
8. Its finite-dimensional image lies in a finite subrepresentation U of A. Naturality
   for V to U gives L(f_phi)_R=(f_phi)_R lambda_V; apply epsilon_R to obtain
   epsilon_R L(f_phi)_R=phi_R lambda_V.
9. The dictionary's point-action formula now gives phi_R r_V(g)=phi_R lambda_V.
   Coordinate functionals of a finite basis detect equality over arbitrary R, so
   r_V(g)=lambda_V. The empty basis treats V=0.
10. Any other point h with these actions acts on every finite subrepresentation of A
    as L does, hence on all of A_R as L. Applying epsilon_R recovers h*=g*, so h=g.
    Invertibility of lambda_V follows from the group action; it is never assumed.
-/
theorem affineGroup_tensor_reconstruction
    {k : Type u} [Field k] (G : Scheme.{u}) [G.Over (Spec (.of k))]
    [GrpObj (G.asOver (Spec (.of k)))] [IsAffine G]
    [LocallyOfFiniteType (G ↘ Spec (.of k))] [QuasiCompact (G ↘ Spec (.of k))]
    (R : Type u) [CommRing R] [Algebra k R]
    (lam : ∀ (V : Type u) [AddCommGroup V] [Module k V] [FiniteDimensional k V],
      NaturalRepresentation (k := k) G V → (R ⊗[k] V →ₗ[R] R ⊗[k] V))
    (h_tensor : ∀ (V W : Type u) [AddCommGroup V] [Module k V]
      [FiniteDimensional k V] [AddCommGroup W] [Module k W] [FiniteDimensional k W]
      (r : NaturalRepresentation (k := k) G V)
      (s : NaturalRepresentation (k := k) G W)
      (t : NaturalRepresentation (k := k) G (V ⊗[k] W)),
      (∀ (T : Type u) [CommRing T] [Algebra k T]
        (x : points (G.asOver (Spec (.of k))) T) (z : T ⊗[k] (V ⊗[k] W)),
        TensorProduct.AlgebraTensorModule.distribBaseChange k T V W (t.action T x z) =
          TensorProduct.map (r.action T x).toLinearMap (s.action T x).toLinearMap
            (TensorProduct.AlgebraTensorModule.distribBaseChange k T V W z)) →
      ∀ z : R ⊗[k] (V ⊗[k] W),
        TensorProduct.AlgebraTensorModule.distribBaseChange k R V W (lam (V ⊗[k] W) t z) =
          TensorProduct.map (lam V r) (lam W s)
            (TensorProduct.AlgebraTensorModule.distribBaseChange k R V W z))
    (h_unit : ∀ r : NaturalRepresentation (k := k) G k,
      (∀ (T : Type u) [CommRing T] [Algebra k T]
        (x : points (G.asOver (Spec (.of k))) T), r.action T x = 1) →
      lam k r = LinearMap.id)
    (h_natural : ∀ (V W : Type u) [AddCommGroup V] [Module k V]
      [FiniteDimensional k V] [AddCommGroup W] [Module k W] [FiniteDimensional k W]
      (r : NaturalRepresentation (k := k) G V)
      (s : NaturalRepresentation (k := k) G W) (f : V →ₗ[k] W),
      (∀ (T : Type u) [CommRing T] [Algebra k T]
        (x : points (G.asOver (Spec (.of k))) T),
        f.baseChange T ∘ₗ (r.action T x).toLinearMap =
          (s.action T x).toLinearMap ∘ₗ f.baseChange T) →
      lam W s ∘ₗ f.baseChange R = f.baseChange R ∘ₗ lam V r) :
    ∃! g : points (G.asOver (Spec (.of k))) R,
      ∀ (V : Type u) [AddCommGroup V] [Module k V] [FiniteDimensional k V]
        (r : NaturalRepresentation (k := k) G V),
        (r.action R g).toLinearMap = lam V r := by
  sorry

end AlgebraicGeometry.RationalRepresentation
