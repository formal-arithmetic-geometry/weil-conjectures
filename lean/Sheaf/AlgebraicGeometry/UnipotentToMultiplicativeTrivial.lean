/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q141
-/
module

public import Sheaf.AlgebraicGeometry.ToriMultiplicativeType
public import WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Sheaf.AlgebraicGeometry.AlgClosedGroupEmbeddingExistenceDescent
import Mathlib.AlgebraicGeometry.Pullbacks

/-! # Unipotent groups have no characters of multiplicative type

Source: Milne, Algebraic Groups (2017), Corollaries 14.9, 14.12 and 14.18(a),
printed pp.282--284; Definition 12.17 and Theorem 12.23, pp.236, 240
(blueprint: lem-sfb-unipotent-to-multiplicative-trivial).

The geometric embedding definition here includes nonsmooth group schemes. The existing
`SolvableGroupStructure.IsUnipotent` is restricted to smooth groups. Multiplicative type
and scalar extension are the existing constructions in `MultiplicativeType`.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory
open scoped MonObj

namespace AlgebraicGeometry
namespace UnipotentGroup

/-- A closed embedding into the upper unitriangular group, expressed by a closed embedding
into GL whose matrices on every algebra have diagonal 1 and entries below the diagonal 0.
These equations express factorization through its closed unitriangular subgroup, and the
factor is closed because the composite into GL is closed. In particular, this tests the
whole group scheme, including nilpotent points.
Source: Milne, Theorem 14.5(b), pp.281--282
(blueprint: lem-sfb-unipotent-to-multiplicative-trivial). -/
def HasUnitriangularEmbedding {k : Type u} [Field k]
    (G : Grp (Over (Spec (.of k)))) : Prop :=
  ∃ (n : ℕ), 0 < n ∧
    ∃ ρ : G.X ⟶ GeneralLinearGroup (ULift.{u} (Fin n)) k,
      IsClosedSubgroupScheme ρ ∧
      ∀ (A : Type u) [CommRing A] [Algebra k A]
        (x : (Spec (.of A)).asOver (Spec (.of k)) ⟶ G.X),
        (∀ i : ULift.{u} (Fin n),
          (GeneralLinearGroup.homMulEquiv (ULift.{u} (Fin n)) k A (x ≫ ρ)).val i i = 1) ∧
        (∀ i j : ULift.{u} (Fin n), j.down < i.down →
          (GeneralLinearGroup.homMulEquiv (ULift.{u} (Fin n)) k A (x ≫ ρ)).val i j = 0)

/-- Geometric unipotence means a closed unitriangular embedding after algebraic closure;
no smoothness or connectedness is built into this condition.
Source: Milne, Corollaries 14.6 and 14.9, p.282
(blueprint: lem-sfb-unipotent-to-multiplicative-trivial). -/
def IsGeometricallyUnipotent {k : Type u} [Field k]
    (G : Grp (Over (Spec (.of k)))) : Prop :=
  HasUnitriangularEmbedding ((MultiplicativeType.baseChange (K := AlgebraicClosure k)).obj G)

/-- A faithful representation with unipotent geometric points. Faithfulness is injectivity
on every algebra, via the recorded subgroup-scheme predicate; nilpotence is tested on
points over the algebraic closure. Source: Milne, Corollary 14.12, p.283
(blueprint: lem-sfb-unipotent-to-multiplicative-trivial). -/
def HasFaithfulGeometricallyUnipotentRepresentation {k : Type u} [Field k]
    (G : Grp (Over (Spec (.of k)))) : Prop :=
  ∃ (n : ℕ), 0 < n ∧
    ∃ ρ : G.X ⟶ GeneralLinearGroup (ULift.{u} (Fin n)) k,
      IsSubgroupScheme ρ ∧
      ∀ x : (Spec (.of (AlgebraicClosure k))).asOver (Spec (.of k)) ⟶ G.X,
        ∃ N : ℕ, 0 < N ∧
          ((GeneralLinearGroup.homMulEquiv (ULift.{u} (Fin n)) k
            (AlgebraicClosure k) (x ≫ ρ)).val - 1) ^ N = 0

/-- Unipotence is preserved and reflected by arbitrary field extensions.
Source: Milne, Corollary 14.9, p.282
(blueprint: lem-sfb-unipotent-to-multiplicative-trivial).

Proof (node step 1): embed the algebraic closure of k into an algebraic closure of K,
using lem-weil-pbc-algebraic-extension-embeds-algebraically-closed. Tensor associativity
identifies the two scalar extensions (lem-weil-pbc-fibre-product-affine-spectra).
For each positive matrix size, closed-embedding existence over the algebraically closed
base is detected after the extension by lem-sfb-algclosed-group-embedding-existence-descent.
The unitriangular target is affine of finite type, with polynomial coordinates. Taking
the existential quantifier over sizes gives both implications. -/
theorem isGeometricallyUnipotent_baseChange_iff
    {k K : Type u} [Field k] [Field K] [Algebra k K]
    (G : Grp (Over (Spec (.of k)))) [IsAffine G.X.left]
    [LocallyOfFiniteType G.X.hom] [QuasiCompact G.X.hom] :
    IsGeometricallyUnipotent ((MultiplicativeType.baseChange (K := K)).obj G) ↔
      IsGeometricallyUnipotent G := by
  sorry

/-- Multiplicative type is preserved and reflected by arbitrary field extensions.
Source: Milne, Definition 12.17 and Theorem 12.23, pp.236, 240
(blueprint: lem-sfb-unipotent-to-multiplicative-trivial).

Proof (node step 1): use a common algebraically closed extension as in the unipotent
case, with tensor associativity from lem-weil-pbc-fibre-product-affine-spectra. Apply
lem-sfb-algclosed-group-embedding-existence-descent to each split torus target. Its
Laurent polynomial coordinates are of finite type, including the rank-zero trivial
target. Taking the existential quantifier over all ranks proves the equivalence. -/
theorem isMultiplicativeType_baseChange_iff
    {k K : Type u} [Field k] [Field K] [Algebra k K]
    (G : Grp (Over (Spec (.of k)))) [IsAffine G.X.left]
    [LocallyOfFiniteType G.X.hom] [QuasiCompact G.X.hom] :
    MultiplicativeType.IsMultiplicativeType
        ((MultiplicativeType.baseChange (K := K)).obj G) ↔
      MultiplicativeType.IsMultiplicativeType G := by
  sorry

/-- For smooth groups, geometric unipotence is equivalent to unipotence of all geometric
points in a faithful representation. Source: Milne, Corollary 14.12, p.283
(blueprint: lem-sfb-unipotent-to-multiplicative-trivial).

Proof (node step 2): given a faithful representation with unipotent geometric points,
lem-sfb-geometric-unipotence-unitriangular-embedding gives a closed unitriangular
embedding over k, hence over its algebraic closure. Conversely, a unitriangular
embedding makes each geometric matrix unipotent: the nth power of a strictly upper
triangular n-by-n matrix is zero. For any faithful representation over k, apply
lem-sfb-rational-representation-unipotent-point after algebraic closure to transfer
unipotence to that representation. An affine finite-type group has such a faithful
representation. Smoothness is used only in the implication from geometric points. -/
theorem isGeometricallyUnipotent_iff_geometric_points
    {k : Type u} [Field k] (G : Grp (Over (Spec (.of k))))
    [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] [QuasiCompact G.X.hom]
    [Smooth G.X.hom] :
    IsGeometricallyUnipotent G ↔ HasFaithfulGeometricallyUnipotentRepresentation G := by
  sorry

/-- Every group-scheme homomorphism from a unipotent affine group of finite type to a
finite-type affine group of multiplicative type is trivial on all algebra-valued points.
There is no smoothness or connectedness hypothesis on either group.
Source: Milne, Corollary 14.18(a), p.284
(blueprint: lem-sfb-unipotent-to-multiplicative-trivial).

Proof (node steps 3--4): extend to F, the algebraic closure of k, and choose the defining
closed embeddings into a unitriangular group and a rank-r split torus. Each coordinate
character of f has a nonzero fixed vector by lem-sfb-unitriangular-subgroup-rational-fixed-vector
in dimension one. This fixed scalar is invertible over every F-algebra, so each character
is identically 1. The torus embedding is injective on algebra-valued points since its
coordinate map is surjective (def-weil-closed-immersion, def-weil-affine-spectrum).
Thus f over F is the identity-valued morphism, also when r=0. On affine coordinates,
f*(c) - epsilon(c) becomes zero in k[V] tensor F by
lem-weil-pbc-fibre-product-affine-spectra. The map k[V] to this tensor product is injective:
extend 1 to a k-basis of F, and take the linear functional sending 1 to 1 and the other
basis vectors to 0; tensoring it with k[V] is a left inverse. Hence f is the
identity-valued morphism over k. Evaluation over any k-algebra A gives the conclusion,
without any reducedness, smoothness or connectedness assumption. -/
theorem hom_to_multiplicativeType_trivial
    {k : Type u} [Field k] (V D : Grp (Over (Spec (.of k))))
    [IsAffine V.X.left] [IsAffine D.X.left]
    [LocallyOfFiniteType V.X.hom] [QuasiCompact V.X.hom]
    [LocallyOfFiniteType D.X.hom] [QuasiCompact D.X.hom]
    (hV : IsGeometricallyUnipotent V) (hD : MultiplicativeType.IsMultiplicativeType D)
    (f : V ⟶ D) (A : Type u) [CommRing A] [Algebra k A]
    (v : (Spec (.of A)).asOver (Spec (.of k)) ⟶ V.X) :
    v ≫ f.hom.hom = 1 := by
  sorry

end UnipotentGroup
end AlgebraicGeometry
