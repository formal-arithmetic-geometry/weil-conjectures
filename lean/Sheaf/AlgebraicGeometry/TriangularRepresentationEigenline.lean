/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q06
-/
module

public import Sheaf.AlgebraicGeometry.RationalRepresentationComoduleDictionary
public import Sheaf.AlgebraicGeometry.StandardGroupSchemes
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

import WeilConjectures.Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.Coalgebra.GroupLike

/-! # An eigenline for a rational representation of a triangular group

Source: Milne, Algebraic Groups (2017), Definition 16.1 and Proposition 16.2(c) implies (a),
printed pp.324--325 (blueprint: lem-sfb-triangular-group-representation-eigenline).

The triangular embedding is a closed group embedding into GL_n with all entries below
its diagonal zero on every algebra-valued point. This is precisely a closed embedding
into the closed upper triangular subgroup. The coaction uses the coordinate Hopf algebra.
-/

set_option autoImplicit false

@[expose] public section

universe u

open CategoryTheory
open scoped TensorProduct MonObj

namespace AlgebraicGeometry.RationalRepresentation

/-- Every nonzero finite-dimensional rational module for a triangular affine group has
an eigenline with a group-scheme character, including its action over every test algebra.
Source: Milne, Definition 16.1 and Proposition 16.2(c) implies (d) implies (a), pp.324--325
(blueprint: lem-sfb-triangular-group-representation-eigenline).

Proof:
1. Take the diagonal morphism to the split torus and its faithfully flat image D
(lem-sfb-affine-homomorphism-flat-image). Its kernel N is the intersection with U_n,
a normal finite-type closed unitriangular subgroup; a section is unnecessary.
2. Restrict the coaction to N using lem-sfb-rational-representation-comodule-dictionary.
The unitriangular fixed-vector theorem (lem-sfb-unitriangular-subgroup-rational-fixed-vector)
makes W = ker(c_N - (v mapping to v tensor 1)) nonzero.
3. Universal points test invariance. A complement of W and injectivity after tensoring
(lem-sfb-vector-space-tensor-family-zero-detection) show that invariants over R are W_R,
without any finiteness requirement on k[N].
4. Normality gives u(gw) = g((g inverse u g)w) = gw after every further algebra extension.
Thus W is a rational J-submodule, and N acts trivially, by the comodule dictionary.
5. Descend its representation through the faithfully flat quotient J to D
(lem-sfb-faithfully-flat-group-quotient-universal). GL(W) is affine finite type by
its determinant localization (def-sc-general-linear-group). Its coaction b pulls back to c.
6. The coordinate algebra of D is a quotient of the Laurent algebra of the split torus.
Images of Laurent monomials are units and group-like (def-sc-gm-ga,
lem-sfb-affine-group-coordinate-hopf). Distinct images form a basis by
lem-sfb-coalgebra-group-like-independent, counting coincident images only once.
7. Expand b(w) = sum w_i tensor e_i for nonzero w. Counitality gives w = sum w_i,
so some w_i is nonzero. Coassociativity and coefficient extraction in the last factor
give b(w_i) = w_i tensor e_i. All sums are finite.
8. The unit group-like e_i defines a character of D by t mapping to e_i; its antipode
is its inverse (lem-sfb-affine-group-coordinate-hopf). Pull back to J and take L = k w_i.
Linearity gives the displayed coaction formula for every v in L. The dictionary evaluates
this formula over every commutative k-algebra, giving the scalar action on all of R tensor L.
No algebraic closedness, smoothness, connectedness, or characteristic restriction is used. -/
theorem triangular_representation_eigenline {k : Type u} [Field k]
    (J : Scheme.{u}) [J.Over (Spec (.of k))]
    [GrpObj (J.asOver (Spec (.of k)))] [IsAffine J]
    [LocallyOfFiniteType (J ↘ Spec (.of k))] [QuasiCompact (J ↘ Spec (.of k))]
    (n : ℕ) (hn : 0 < n)
    (i : J.asOver (Spec (.of k)) ⟶ GeneralLinearGroup (ULift.{u} (Fin n)) k)
    [IsMonHom i] [IsClosedImmersion i.left]
    (htri : ∀ (R : Type u) [CommRing R] [Algebra k R]
      (x : points (J.asOver (Spec (.of k))) R) (a b : Fin n), b < a →
      (GeneralLinearGroup.homMulEquiv (ULift.{u} (Fin n)) k R (x ≫ i)).val ⟨a⟩ ⟨b⟩ = 0)
    (V : Type u) [AddCommGroup V] [Module k V] [FiniteDimensional k V] [Nontrivial V]
    (c : CoordinateComodule (k := k) J V) :
    ∃ (L : Submodule k V) (χ : J.asOver (Spec (.of k)) ⟶
      StandardGroupSchemes.multiplicative k),
      IsMonHom χ ∧ Module.finrank k L = 1 ∧
      (∀ v : L, c.val v = (v : V) ⊗ₜ[k]
        (@id Γ(J, ⊤) (χ.left.appTop ((Scheme.ΓSpecIso (.of (LaurentPolynomial k))).inv
          (LaurentPolynomial.T 1))))) ∧
      ∃ r : NaturalRepresentation (k := k) J V,
        genericCoaction (k := k) J V r = c.val ∧
        ∀ (R : Type u) [CommRing R] [Algebra k R]
          (x : Γ(J, ⊤) →ₐ[k] R) (z : R ⊗[k] L),
          r.action R (coordinatePoint (k := k) J R x) (L.subtype.baseChange R z) =
            x (χ.left.appTop ((Scheme.ΓSpecIso (.of (LaurentPolynomial k))).inv
              (LaurentPolynomial.T 1))) • L.subtype.baseChange R z := by
  sorry

end AlgebraicGeometry.RationalRepresentation
