/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q52
-/
module

public import Sheaf.AlgebraicGeometry.LinearGroupSchemes
public import Sheaf.AlgebraicGeometry.ReductiveTorusCentralizerTerminology
public import Mathlib.LinearAlgebra.SpecialLinearGroup
public import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.RingTheory.TensorProduct.Maps
import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Reduced
import WeilConjectures.Mathlib.RingTheory.Nullstellensatz

/-! # Special linear groups are reductive in every characteristic

Source: Milne, Algebraic Groups (2017), Section 2.42, printed p.53;
Lemma 19.16, Corollary 19.18 and Example 19.19, printed p.401
(blueprint: lem-sfb-special-linear-reductive).

For an arbitrary finite-dimensional vector space E, the recorded determinant-one
coordinate scheme in dimension finrank E represents SL(E). The point identification
below uses one basis of E and its scalar extensions. We write scalar extension as
R tensor E, canonically identified with E tensor R by tensor symmetry.
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory
open scoped TensorProduct MonObj

namespace AlgebraicGeometry.LinearGroupSchemes

/-- A single basis of E, with the lifted indices of the recorded coordinate scheme.
Source: Milne, Section 2.42 and Example 19.19, choice of matrix coordinates
(blueprint: lem-sfb-special-linear-reductive). -/
noncomputable def specialLinearBasis (k : Type u) [Field k]
    (E : Type v) [AddCommGroup E] [Module k E] [FiniteDimensional k E] :
    Module.Basis (Index.{u} (Module.finrank k E)) k E :=
  (Module.finBasis k E).reindex Equiv.ulift.symm

/-- The actual point isomorphism with determinant-one automorphisms of scalar-extended E.
It composes the recorded coordinate-scheme point isomorphism with Mathlib's basis
identification; it includes all commutative test algebras, even nonreduced ones.
Source: Milne, Section 2.42 and Example 19.19
(blueprint: lem-sfb-special-linear-reductive). -/
noncomputable def specialLinearPointsOn (k : Type u) [Field k]
    (E : Type v) [AddCommGroup E] [Module k E] [FiniteDimensional k E]
    (R : Type u) [CommRing R] [Algebra k R] :
    (StandardGroupSchemes.affine k R ⟶ specialLinear k (Module.finrank k E)) ≃*
      SpecialLinearGroup R (R ⊗[k] E) :=
  (specialPoints k (Module.finrank k E) R).trans
    (Matrix.SpecialLinearGroup.toLin_equiv ((specialLinearBasis k E).baseChange R))

/-- SL(E) is smooth, affine, finite type, geometrically connected and reductive, with
its natural determinant-one functor of points. Positivity of finrank is r >= 1.
The naturality equation on 1 tensor v determines scalar extension on the entire
module by linearity. The predicate IsReductive uses scheme-theoretic triviality
of every smooth connected normal closed unipotent subgroup after algebraic closure.

Source: Milne, Section 2.42, printed p.53; Lemma 19.16, Corollary 19.18 and
Example 19.19, printed p.401 (blueprint: lem-sfb-special-linear-reductive).

Proof plan, following the eight steps of the node:
1. Choose the displayed basis of E. def-sc-general-linear-group identifies the scheme
   with Spec k[x_ij]/(det X - 1). The finitely many generators give finite type;
   the single relation gives finite presentation (def-sbc-locally-finite-presentation).
   In dimension one this is Spec k. The recorded specialPoints and the basis
   identification give specialLinearPointsOn; coordinate evaluation commutes with
   every algebra map, giving precisely the naturality equation below.
2. In the GL coordinate localization, divide the first column by det X. The
   determinant then equals one, so polynomial evaluation and the quotient universal
   property (def-weil-pbc-mv-polynomial-ring, def-weil-pbc-algebra-hom-quotient)
   give q:GL -> SL with qj = id (def-weil-affine-spectrum).
3. GL is smooth by lem-sfb-general-linear-reductive. Extend an infinitesimal lift
   after composing with j, and compose its extension with q. This proves formal
   smoothness; finite presentation proves smoothness (def-sbc-smooth-morphisms).
4. After algebraic closure q is still a retraction, hence surjective. GL is
   connected by lem-sfb-general-linear-reductive, so its image is connected in the
   nonempty sense of def-weil-connected-scheme; the identity supplies a point.
5. Identify the base-changed quotient with K[x_ij]/(det X - 1) using
   lem-weil-pbc-fibre-product-affine-spectra and
   lem-weil-pbc-algebra-tensor-pushout-universal-property. The coordinate formulas
   preserve multiplication, identity and inverse, so this is a group identification.
6. For a smooth connected normal unipotent closed subgroup U, apply
   lem-sfb-unipotent-rational-representation-fixed-vector to its inclusion
   representation. There is a nonzero fixed vector in K^r.
7. Normality (def-sc-group-scheme-subgroup) makes the fixed subspace SL-stable.
   For r > 1, determinant-one transvections applied to a vector with nonzero
   j-coordinate give every basis vector. For r = 1 the conclusion is immediate.
   Thus every K-point of U has identity matrix, also in characteristic two.
8. Smoothness gives reducedness by sbc-lem-smooth-geometrically-reduced. The
   vanishing principle lem-wf-affine-nullstellensatz-vanishing kills every image
   of x_ij - delta_ij in the finite type coordinate algebra of U. Its structure
   map from K is surjective and split by the identity section, hence an isomorphism.
   Thus U is the trivial group scheme, proving the final reductivity clause. -/
theorem specialLinear_reductive (k : Type u) [Field k]
    (E : Type v) [AddCommGroup E] [Module k E] [FiniteDimensional k E]
    (hr : 1 ≤ Module.finrank k E) :
    ReductiveTorusCentralizer.IsReductive
      (Grp.mk (specialLinear k (Module.finrank k E))) ∧
    ∀ (R S : Type u) [CommRing R] [CommRing S] [Algebra k R] [Algebra k S]
      (φ : R →ₐ[k] S)
      (x : StandardGroupSchemes.affine k R ⟶ specialLinear k (Module.finrank k E))
      (v : E),
      TensorProduct.map φ.toLinearMap (LinearMap.id : E →ₗ[k] E)
        (specialLinearPointsOn k E R x (1 ⊗ₜ[k] v)) =
      specialLinearPointsOn k E S (StandardGroupSchemes.map k φ ≫ x) (1 ⊗ₜ[k] v) := by
  sorry

end AlgebraicGeometry.LinearGroupSchemes
