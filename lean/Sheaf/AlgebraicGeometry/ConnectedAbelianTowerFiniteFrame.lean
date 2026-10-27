/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Z6
-/
module

public import Sheaf.AlgebraicGeometry.ConnectedAbelianTowerNormalizedData

/-! # Finite frames descend along a connected finite étale tower

Source: Bhatt--Scholze, Lemma 5.1.4 and Corollary 5.1.5
(blueprint: lem-sfb-connected-abelian-tower-finite-frame).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale

/-- A finite constant trivialization over the limit exists at an actual tower level.
Source: Bhatt--Scholze, Lemma 5.1.4 and the finite-frame argument of Corollary 5.1.5
(blueprint: lem-sfb-connected-abelian-tower-finite-frame).

Proof: The forward implication restricts a finite-level trivialization along the
limit projection. Object inverse image is sectionwise restriction on the slice,
and restriction of a finite constant sheaf is constant with the same labels.

For the reverse implication fix F and a finite trivialization over X. On the base
site form the sheaf H(V)=Isom(constant A on V, F restricted to V). Morphisms glue,
as do their inverses, so this is a sheaf; the inverse identities follow by the
uniqueness of morphism gluing. Over X, the given trivialization identifies H with
the constant sheaf of permutations of A. To verify this on arbitrary objects,
represent constants by finite coproducts: a map is a finite family of clopen
partitions, and their common refinement records a single permutation locally.
The empty label case gives the singleton symmetric group, so causes no exception.

Constant pro-etale sheaves are classical: comparison inverse image preserves
terminal objects and coproducts, or equivalently commutes with sheafification of
constant presheaves by their two adjunctions. Thus H is locally classical for the
singleton cover X to U. Apply locally-classical continuity to the given small
cofiltered affine finite-etale presentation of X. It identifies H(X) with the
filtered colimit of H(X_i). The frame over X therefore comes from a member of
H(X_i), which is an actual isomorphism with the constant sheaf on A. This gives
finite constancy at that level, without assuming it at the start. -/
theorem abelianTowerFiniteFrame {U : Scheme.{u}} [IsAffine U] {I : Type u}
    [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (T : ConnectedAbelianCoverTower U I)
    (F : Sheaf (Scheme.ProEt.topology U) (Type (u + 1))) :
    T.finiteLevel F ↔ abelianTowerConstantAt F T.cone.pt := by sorry

end AlgebraicGeometry.ProEtale
