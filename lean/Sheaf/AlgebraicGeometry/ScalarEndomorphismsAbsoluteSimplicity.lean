/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q04
-/
module

public import Sheaf.AlgebraicGeometry.RationalRepresentationComoduleDictionary
public import Mathlib.LinearAlgebra.TensorProduct.Tower

import Sheaf.RingTheory.CoalgebraDualActionDetection
import Mathlib.AlgebraicGeometry.Group.Affine
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.TensorProduct.Map

/-! # Scalar endomorphisms and absolute simplicity of rational representations

Source: Milne, Algebraic Groups (2017), Proposition 4.19(b), printed pp.90--91,
and Remark 4.18, printed p.90.
(blueprint: lem-sfb-scalar-endomorphisms-absolute-simplicity)

Subrepresentation stability and equivariance are tested on every algebra-valued point.
For a K-algebra A, the points of H_K over A are canonically the points of H over A.
The action on A tensor_K (K tensor_k V) is the original action on A tensor_k V,
conjugated by Mathlib's canonical cancelBaseChange equivalence. Thus the conclusion
uses the actual scalar extension, including its prescribed action.
-/

set_option autoImplicit false

@[expose] public section

universe u

open CategoryTheory
open scoped TensorProduct

namespace AlgebraicGeometry.RationalRepresentation

/-- A nonzero finite-dimensional simple rational representation with only scalar
equivariant endomorphisms remains simple after every field extension.
Source: Milne, Proposition 4.19(b), printed pp.90--91; equivariance as in Remark 4.18, p.90.
(blueprint: lem-sfb-scalar-endomorphisms-absolute-simplicity)

Proof:
1. Give k[H] its coordinate Hopf structure (lem-sfb-affine-group-coordinate-hopf).
   The rational-representation/comodule dictionary identifies the action with a right
   coaction and equivariant maps with comodule maps. Stable subspaces are precisely
   subcomodules: restrict the natural action, or evaluate the restricted coaction.
2. By lem-sfb-coalgebra-dual-action-detection the convolution dual acts on V.
   Its image B in End_k(V) contains all scalars; B-stable additive subgroups are
   therefore k-subspaces. Simplicity makes V a simple B-module. B-linear additive
   endomorphisms are k-linear and, by the dictionary, equivariant, hence scalar.
3. Choose a basis using lem-weil-pbc-vector-space-free. Finite dimensionality makes
   it finite and nonzeroness makes it nonempty. It also generates V over End_B(V).
   Apply lem-sfb-finite-simple-double-centralizer: every k-linear endomorphism
   commutes with the scalar End_B(V), so is given by an element of B. In particular
   every matrix unit is a convolution-dual operator.
4. For any K/k, affine fibre products identify k[H_K] with K tensor_k k[H]
   (lem-weil-pbc-fibre-product-affine-spectra); finite type survives base change
   (lem-sfb-finite-type-composition-base-change). The dictionary identifies the
   extended coaction by rho_K(a tensor v) = sum (a tensor v_i) tensor (1 tensor c_i).
   Its point action is exactly the conjugation by cancelBaseChange displayed below.
5. Extend a functional f on k[H] by f_K(a tensor c) = a f(c), using the tensor
   universal property (def-weil-pbc-module-tensor-product). Detection over K shows
   that a rational subrepresentation W is stable under T_fK = 1 tensor T_f, hence
   under every extended matrix unit.
6. The original basis extends to a K-basis by the tensor universal property.
   If W is nonzero, choose w with nonzero j-th coordinate a_j. Each matrix unit
   E_ij sends w to a_j times the i-th basis vector. Dividing by a_j puts every
   basis vector in W, so W is the whole space. Otherwise W is zero.
-/
theorem scalar_endomorphisms_absolute_simplicity
    {k : Type u} [Field k] (H : Scheme.{u}) [H.Over (Spec (.of k))]
    [GrpObj (H.asOver (Spec (.of k)))] [IsAffine H]
    [LocallyOfFiniteType (H ↘ Spec (.of k))] [QuasiCompact (H ↘ Spec (.of k))]
    (V : Type u) [AddCommGroup V] [Module k V] [FiniteDimensional k V] [Nontrivial V]
    (r : NaturalRepresentation (k := k) H V)
    (hsimple : ∀ U : Submodule k V,
      (∀ (A : Type u) [CommRing A] [Algebra k A]
        (x : points (H.asOver (Spec (.of k))) A) (z : A ⊗[k] V),
        z ∈ U.baseChange A → r.action A x z ∈ U.baseChange A) → U = ⊥ ∨ U = ⊤)
    (hscalar : ∀ f : Module.End k V,
      (∀ (A : Type u) [CommRing A] [Algebra k A]
        (x : points (H.asOver (Spec (.of k))) A),
        f.baseChange A ∘ₗ (r.action A x).toLinearMap =
          (r.action A x).toLinearMap ∘ₗ f.baseChange A) →
      ∃ a : k, f = a • (LinearMap.id : Module.End k V)) :
    ∀ (K : Type u) [Field K] [Algebra k K] (W : Submodule K (K ⊗[k] V)),
      (∀ (A : Type u) [CommRing A] [Algebra K A] [Algebra k A] [IsScalarTower k K A]
        (x : points (H.asOver (Spec (.of k))) A) (z : A ⊗[K] (K ⊗[k] V)),
        z ∈ W.baseChange A →
          (_root_.TensorProduct.AlgebraTensorModule.cancelBaseChange k K A A V).symm
            (r.action A x
              (_root_.TensorProduct.AlgebraTensorModule.cancelBaseChange k K A A V z)) ∈
            W.baseChange A) → W = ⊥ ∨ W = ⊤ := by
  sorry

end AlgebraicGeometry.RationalRepresentation
