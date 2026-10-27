/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.GroupScheme.Semisimple
public import Sheaf.AlgebraicGeometry.ReductiveTorusCentralizerTerminology
public import Mathlib.Topology.KrullDimension
import Sheaf.AlgebraicGeometry.GroupScheme.AffineNormalQuotientGeometry
import Sheaf.AlgebraicGeometry.GroupScheme.SmoothConnectedDerivedSubgroup
import Sheaf.AlgebraicGeometry.GroupScheme.HomomorphismFactorization
import WeilConjectures.AlgebraicGeometry.GroupScheme.Separated

/-! # Reductivity from a central torus of codimension three

Source: Conrad, Reductive Group Schemes, proof of Proposition 3.1.9(1), printed p.88.
(blueprint: lem-sfb-nonsolvable-central-torus-corank-three)

The torus may have rank zero. Centrality is tested on all algebra-valued points,
solvability uses the scheme-theoretic derived series, and dimension is topological
Krull dimension. There is no characteristic restriction.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory
open scoped MonObj

namespace AlgebraicGeometry

/-- A nonsolvable smooth connected affine algebraic group with a central torus of
codimension three is reductive.

Source: Conrad, Reductive Group Schemes, proof of Proposition 3.1.9(1), printed p.88;
the expanded proof is in the DAG, using Milne, Algebraic Groups (2017), Chapters 5,
6, 14 and 17. (blueprint: lem-sfb-nonsolvable-central-torus-corank-three)

Proof:
1. Centrality makes Z normal. By lem-sfb-affine-normal-quotient-geometry form the
   affine fppf quotient q : H → Q with kernel Z. It is smooth and connected;
   geometric connectedness comes from lem-sfb-solvable-normal-subgroup-products.
   By lem-sfb-group-hom-dimension-kernel-image, dim H = dim Q + dim Z, so dim Q = 3.
2. Q is nonsolvable. Indeed, by lem-sfb-smooth-connected-derived-subgroup, the
   derived groups of H and Q are smooth and connected. Inductively q maps D^j H
   into D^j Q: compose with the commutative quotient D^j Q / D^(j+1) Q supplied
   by lem-sfb-affine-normal-quotient-geometry. The universal property of the derived
   subgroup kills D^(j+1) H in this quotient. If D^b Q = 1, then D^b H lies in Z,
   and commutativity of Z forces D^(b+1) H = 1, a contradiction.
3. Let N be a nontrivial smooth connected normal unipotent closed subgroup of H.
   Separatedness is lem-sc-group-scheme-separated-field. Factor q restricted to N
   as N → I → Q using lem-sfb-algebraic-group-homomorphism-factorization. I is affine
   since it is closed in Q. Flatness and surjectivity make N → I faithfully flat on
   coordinate algebras. By lem-sfb-unipotent-normal-quotient-image, I is smooth,
   connected, normal and unipotent. If I = 1, N maps into Z, and
   lem-sfb-unipotent-to-multiplicative-trivial makes its inclusion trivial, a
   contradiction. Thus I is nontrivial, and the strict dimension inequality of
   lem-sfb-solvable-normal-subgroup-products gives dim I ≥ 1.
4. Form R = Q/I by lem-sfb-affine-normal-quotient-geometry. It is smooth connected
   affine of finite type. By lem-sfb-group-hom-dimension-kernel-image,
   3 = dim R + dim I, hence dim R ≤ 2. Apply
   lem-sfb-connected-group-dimension-two-solvable to conclude that R is solvable.
5. By lem-sfb-smooth-unipotent-solvable, I has a finite series with commutative
   quotients. Pull back the derived series of R to Q, using the correspondence and
   quotient clauses of lem-sfb-affine-normal-quotient-geometry, and append the series
   for I. Derived groups exist by lem-sfb-smooth-connected-derived-subgroup.
   Minimality of the derived subgroup puts D^j Q in the j-th term of this finite
   series. It terminates at 1, contradicting step 2.
6. Consequently H has no such nontrivial N, which is reductivity. Since k is
   algebraically closed, extension to its fixed algebraic closure is transport
   along a field isomorphism, so the recorded geometric reductivity predicate is
   equivalent to this assertion over k itself. -/
theorem isReductive_of_nonsolvable_central_torus_corank_three
    (k : Type u) [Field k] [IsAlgClosed k]
    (H Z : Grp (Over (Spec (.of k))))
    [Smooth H.X.hom] [ConnectedSpace H.X.left] [IsAffine H.X.left]
    [LocallyOfFiniteType H.X.hom] [QuasiCompact H.X.hom]
    (i : Z ⟶ H) [IsClosedSubgroupScheme i.hom.hom]
    (hZ : ∃ r : ℕ, Nonempty (Z ≅ MultiplicativeType.splitTorus k r))
    (hcentral : ∀ (A : Type u) [CommRing A] [Algebra k A]
      (z : (Spec (.of A)).asOver (Spec (.of k)) ⟶ Z.X)
      (h : (Spec (.of A)).asOver (Spec (.of k)) ⟶ H.X), Commute (z ≫ i.hom.hom) h)
    (hdim : topologicalKrullDim H.X.left = topologicalKrullDim Z.X.left + 3)
    (hnonsolvable : ¬ IsSolvableGroupScheme H.X) :
    ReductiveTorusCentralizer.IsReductive H := by
  sorry

end AlgebraicGeometry
