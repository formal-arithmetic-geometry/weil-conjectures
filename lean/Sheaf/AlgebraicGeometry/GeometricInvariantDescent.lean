/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q46
-/
module

public import Sheaf.AlgebraicGeometry.RationalRepresentationComoduleDictionary
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.LinearAlgebra.TensorProduct.Map

import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.RingTheory.TensorProduct.Maps
import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Reduced
import WeilConjectures.Mathlib.RingTheory.Nullstellensatz

/-! # Geometric fixed vectors descend to scheme invariants

Source: Milne, Algebraic Groups (2017), Propositions 4.31--4.33 and Corollary 4.34,
printed pp.96--97; Propositions 1.10, 1.17 and 1.26(b), printed pp.9--13.
(blueprint: lem-sfb-geometric-unipotence-invariant-descent)

The invariant subspace is specified by its defining condition over every test algebra.
This condition determines it uniquely. The scalar-extension map is the tensor of its
actual subtype inclusion, and geometric fixed vectors use the given natural action.
Test algebras, fields, schemes and vector spaces use the fixed universe of the existing
NaturalRepresentation interface; its natural families live in the containing universe.
-/

set_option autoImplicit false

@[expose] public section

universe u

open CategoryTheory
open scoped TensorProduct

namespace AlgebraicGeometry.RationalRepresentation

/-- The universally fixed subspace becomes exactly the geometric fixed space after extension
of scalars to an algebraic closure, and the tensor inclusion is injective.
Source: Milne, Propositions 4.31--4.33 and Corollary 4.34, printed pp.96--97;
Propositions 1.10, 1.17 and 1.26(b), printed pp.9--13.
(blueprint: lem-sfb-geometric-unipotence-invariant-descent).

Proof:
1. Write G=Spec A. The affine-pair finite-type criterion
   (lem-weil-pbc-lft-affine-pairs) makes A a finitely generated k-algebra.
   The universal element u in G(A), corresponding to id_A by def-weil-affine-spectrum,
   determines every action on 1 tensor w by naturality along A to R.
2. Define D(w)=u(1 tensor w)-1 tensor w. Its kernel is exactly the subspace U specified
   below: use the universal point in one direction and naturality in the other.
   After scalar extension to B, evaluation b tensor a to b*g(a) sends D_B(z) to gz-z,
   by lem-weil-pbc-algebra-tensor-pushout-universal-property and B-linearity.
3. Expand z as a finite sum b_i tensor w_i with the coefficients b_i independent over k.
   Extend them to a basis of K and apply coordinate functionals to D_K(z)=0.
   Each w_i lies in ker D=U. Conversely D_K kills every tensor with second factor in U.
   Thus ker D_K is exactly the range of the tensor inclusion.
4. The affine fibre-product dictionary (lem-weil-pbc-fibre-product-affine-spectra)
   identifies G_K with Spec(K tensor A). Smoothness gives geometric reducedness by
   sbc-lem-smooth-geometrically-reduced; def-pc-reduced-scheme makes K tensor A reduced.
   Scalar extensions of finite algebra generators generate K tensor A over K.
5. In a finite basis of W write D_K(z)=sum f_j tensor e_j. If every g in G(K) fixes z,
   every K-algebra map K tensor A to K kills every f_j, by step 2 and independence.
   Clause (2) of lem-wf-affine-nullstellensatz-vanishing gives f_j=0. Conversely step 2
   shows ker D_K consists of geometric fixed vectors. Combine this with step 3.
6. Extend a basis of U to one of W to split its inclusion. Tensoring the retraction
   proves injectivity. A nonzero w in U stays nonzero as 1 tensor w, detected by a
   k-linear functional taking w to 1. If U=0 its tensor product is zero, so step 5
   rules out a nonzero geometric fixed vector. Empty bases include d=0; no step uses
   perfectness of k or connectedness of G.
-/
theorem geometric_invariant_descent
    {k K : Type u} [Field k] [Field K] [Algebra k K] [IsAlgClosure k K]
    (G : Scheme.{u}) [G.Over (Spec (.of k))]
    [GrpObj (G.asOver (Spec (.of k)))] [IsAffine G]
    [Smooth (G ↘ Spec (.of k))]
    [LocallyOfFiniteType (G ↘ Spec (.of k))] [QuasiCompact (G ↘ Spec (.of k))]
    (W : Type u) [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    (d : ℕ) (hd : Module.finrank k W = d)
    (r : NaturalRepresentation (k := k) G W) :
    ∃ U : Submodule k W,
      (∀ w : W, w ∈ U ↔
        ∀ (R : Type u) [CommRing R] [Algebra k R]
          (g : points (G.asOver (Spec (.of k))) R),
          r.action R g ((1 : R) ⊗ₜ[k] w) = (1 : R) ⊗ₜ[k] w) ∧
      Function.Injective (U.subtype.lTensor K) ∧
      Set.range (U.subtype.lTensor K) =
        {z : K ⊗[k] W | ∀ g : points (G.asOver (Spec (.of k))) K, r.action K g z = z} ∧
      ((∃ z : K ⊗[k] W, z ≠ 0 ∧
        ∀ g : points (G.asOver (Spec (.of k))) K, r.action K g z = z) ↔ U ≠ ⊥) := by
  sorry

end AlgebraicGeometry.RationalRepresentation
