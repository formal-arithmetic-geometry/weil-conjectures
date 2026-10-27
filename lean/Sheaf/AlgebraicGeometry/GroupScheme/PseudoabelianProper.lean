/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q28
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.FieldTheory.IsAlgClosed.Basic

import Sheaf.AlgebraicGeometry.LocallyAlgebraicGroupIdentityComponent
import WeilConjectures.AlgebraicGeometry.AbelianVariety.Defs
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Proper
import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Reduced

/-!
# Properness of pseudo-abelian group varieties over an algebraically closed field

Source: Milne, Algebraic Groups (2017), Definition 8.3, p.149, and Theorem 8.26, p.154
(blueprint: lem-sfb-pseudoabelian-proper-algclosed).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A smooth connected separated finite-type group scheme over an algebraically closed
field is proper if every smooth connected affine closed normal subgroup scheme is trivial.
Source: Milne, Algebraic Groups (2017), Definition 8.3, p.149, and Theorem 8.26, p.154
(blueprint: lem-sfb-pseudoabelian-proper-algclosed).

Proof:
1. Use strong induction on the finite natural number dim G supplied by
lem-sfb-affine-normal-subgroup-products. By
lem-sfb-general-group-centre-zero-dimension-affine, form the centre Z and its reduced
identity component A, with dim A = dim Z. By
lem-sfb-locally-algebraic-group-identity-component, A is smooth, connected, separated and
of finite type. Its inclusion into G is closed, by composing the reduction, component
and centre inclusions, and it is central.
2. If dim A = 0, the centre has dimension zero, so
lem-sfb-general-group-centre-zero-dimension-affine makes G affine. Apply the hypothesis
to the identity inclusion of G into itself. Its unit section is an isomorphism, with
inverse the structure morphism. Thus the structure morphism is finite, hence proper
by lem-weil-pbc-finite-proper. This includes the induction base dim G = 0.
3. If dim A > 0 and A were not proper, lem-sfb-rosenlicht-nonproper-affine-subgroup
would give a smooth connected affine closed subgroup U of A of positive dimension.
Its composite inclusion in G is closed and normal, since A is central on all algebra
points. The hypothesis makes U trivial, contradicting its positive dimension because
Spec k has one point and dimension zero. Thus A is proper, hence an abelian variety
by def-sc-abelian-variety.
4. Apply lem-sfb-rosenlicht-connected-almost-complement to A in G. This gives a smooth
connected separated finite-type closed normal subgroup N and a faithfully flat
finite-presentation multiplication homomorphism A × N → G with finite kernel and
dim N = dim G - dim A < dim G.
5. Let S be a smooth connected affine closed normal subgroup of N. Its composite
inclusion in G is closed. For any k-algebra B, an element g of G(B) lifts fpqc locally
along A × N → G to an = a n. Centrality of a gives g s g⁻¹ = n s n⁻¹, which lies in S
by normality in N. The local lifts agree on overlaps because S → G is a monomorphism;
lem-weil-pbc-fpqc-representable-descent glues them uniquely. Here
 def-weil-pbc-fpqc-covering and lem-weil-pbc-fpqc-covering-axioms give the covering.
Thus S is normal in G and trivial by hypothesis. Induction makes N proper.
6. The product A × N is proper by lem-weil-pbc-proper-base-change and
lem-weil-pbc-proper-composition. Apply lem-weil-pbc-scheme-theoretic-image-proper to
its multiplication map into the separated finite-type G. The scheme-theoretic image
is proper and has all underlying points by surjectivity. The smooth scheme G is reduced
by sbc-lem-smooth-geometrically-reduced. On each affine open its image ideal lies in
every prime, hence in the zero nilradical. Thus the image equals G and G is proper.
Apply this induction assertion to Q. -/
theorem isProper_of_pseudoabelian
    (k : Type u) [Field k] [IsAlgClosed k]
    (Q : Over (Spec (.of k))) [GrpObj Q]
    [Smooth Q.hom] [ConnectedSpace Q.left] [IsSeparated Q.hom]
    [LocallyOfFiniteType Q.hom] [QuasiCompact Q.hom]
    (hQ : ∀ (S : Over (Spec (.of k))) [GrpObj S] (i : S ⟶ Q),
      IsClosedSubgroupScheme i → IsNormalSubgroupScheme i →
      Smooth S.hom → ConnectedSpace S.left → IsAffine S.left →
      IsIso (MonObj.one (X := S)).left) :
    IsProper Q.hom := by
  sorry

end AlgebraicGeometry
