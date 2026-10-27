/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q98
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceOpenSubspace
public import Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology
public import Sheaf.AlgebraicGeometry.ReducedClosedSubspaceSupport
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceAbsoluteQuasiSeparated
public import Sheaf.AlgebraicGeometry.AtlasEtaleRestriction
import Sheaf.AlgebraicGeometry.SpaceQuasiCompactAffineTests
import WeilConjectures.AlgebraicGeometry.QuasiCompactOpenInduction
import Sheaf.AlgebraicGeometry.SpaceChangeBase
import Sheaf.AlgebraicGeometry.AlgebraicSpaceEtaleOpenImage

/-! # Induction by elementary distinguished squares for qcqs algebraic spaces

Source: Stacks Project, Derived Categories of Spaces, Tag 08GP
(blueprint: lem-sfb-space-qcqs-distinguished-square-induction).

The values of `P` outside the qcqs chartwise etale objects are never used. An affine
object is specified by an isomorphism of its presheaf with a scheme Yoneda presheaf.
Open immersions are identified with the existing open subfunctors. Reduced complements
are the existing closed subspaces; the distinguished condition is that the actual
sheaf pullback projection over that complement is an isomorphism.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- Induction for all qcqs etale algebraic-space objects, allowing the empty affine scheme.
Source: Stacks Project, Tag 08GP; elementary distinguished squares as in Tag 08JK
(blueprint: lem-sfb-space-qcqs-distinguished-square-induction).

Proof:
1. Fix a qcqs etale object T. Quasi-compact open subspaces are quasi-separated, since
absolute diagonals restrict by base change. Such open inclusions are quasi-compact
by lem-sfb-space-qcqs-permanence. Their pullbacks to affine schemes are quasi-compact
open subschemes by lem-sfb-space-quasicompact-affine-tests. Open inclusions and their
composites with etale maps are etale, so all these objects are in the domain of P.
2. For a qcqs scheme T, apply lem-sc-invert-s-cohomology-induction to its quasi-compact
opens. Affine opens satisfy P by h_affine. For a quasi-compact open A and affine open B,
(A in A union B, B to A union B) is distinguished, with overlap A intersection B.
Its reduced complement lies in B. Thus h_square supplies the union step.
3. For general T use lem-sfb-space-change-base-to-integers, retaining opens, charts,
fibre products, reduced complements and absolute qcqs properties. Apply
lem-sfb-qcqs-space-splitting-filtration and transport back to the original base.
This gives finite quasi-compact opens from empty to T, with etale quasi-compact separated
scheme charts isomorphic over successive reduced complements. Descend along the
filtration. The empty initial object satisfies h_affine. Cover each chart by finitely
many affine opens using lem-weil-pbc-qcqs-finite-affine-open-cover.
4. Adjoin their open images one at a time to the preceding filtration open, using
lem-a1-space-etale-open-image. These are quasi-compact opens, hence qcqs by step 1.
For each newly adjoined affine chart, the reduced complement of the previous open
has support in the filtration complement. Reducedness makes it factor through that
reduced closed subspace, uniquely supplied by lem-sfb-space-reduced-closed-support.
The chart is already an isomorphism there, and the remaining support lies in the chosen
affine chart. By lem-a1-space-point-open-calculus the resulting pair is distinguished.
5. The affine chart satisfies P by h_affine, and its overlap with the preceding open
is a qcqs scheme, so step 2 applies. Repeated h_square proves P on the enlarged opens
and hence on the next filtration open. An empty chart has empty target by surjectivity
and is covered by the empty affine base case. Descending induction gives P(T).
T was arbitrary; take its identity map when T = X. Isomorphism invariance transports
P through the scheme and open-subspace presentations used above. -/
theorem qcqs_etale_distinguishedSquare_induction {S : Scheme.{u}}
    (X : AlgebraicSpace S) (hXqc : CompactSpace (Point X.obj.obj))
    (hXqs : IsAbsolutelyQuasiSeparated X) (P : Over X → Prop)
    (h_iso : ∀ (T T' : Over X),
      IsChartwiseEtale T.hom → CompactSpace (Point T.left.obj.obj) →
      IsAbsolutelyQuasiSeparated T.left →
      IsChartwiseEtale T'.hom → CompactSpace (Point T'.left.obj.obj) →
      IsAbsolutelyQuasiSeparated T'.left → (T ≅ T') → (P T ↔ P T'))
    (h_affine : ∀ (T : Over X), IsChartwiseEtale T.hom →
      (∃ A : Over S, IsAffine A.left ∧ Nonempty (T.left.obj.obj ≅ yoneda.obj A)) → P T)
    (h_square : ∀ (W U V O : Over X),
      IsChartwiseEtale W.hom → CompactSpace (Point W.left.obj.obj) →
      IsAbsolutelyQuasiSeparated W.left →
      IsChartwiseEtale U.hom → CompactSpace (Point U.left.obj.obj) →
      IsAbsolutelyQuasiSeparated U.left →
      IsChartwiseEtale V.hom → CompactSpace (Point V.left.obj.obj) →
      IsAbsolutelyQuasiSeparated V.left →
      IsChartwiseEtale O.hom → CompactSpace (Point O.left.obj.obj) →
      IsAbsolutelyQuasiSeparated O.left →
      ∀ (i : U ⟶ W) (p : V ⟶ W) (a : O ⟶ U) (b : O ⟶ V),
      IsPullback a.left.hom b.left.hom i.left.hom p.left.hom →
      (∃ A : OpenSubspace W.left,
        ∃ e : U.left.obj.obj ≅ A.val.toFunctor, e.hom ≫ A.val.ι = i.left.hom.hom) →
      IsEtale p.left.hom.hom →
      (∃ A : Over S, IsAffine A.left ∧ Nonempty (V.left.obj.obj ≅ yoneda.obj A)) →
      ∀ C : ClosedSubspace W.left,
      IsReduced (C.val : AlgebraicSpace S) →
      pointImage C.val.arrow.hom.hom = (pointImage i.left.hom.hom)ᶜ →
      IsIso (Limits.pullback.snd p.left.hom C.val.arrow.hom) →
      P U → P V → P O → P W) :
    (∀ T : Over X, IsChartwiseEtale T.hom → CompactSpace (Point T.left.obj.obj) →
      IsAbsolutelyQuasiSeparated T.left → P T) ∧ P (Over.mk (𝟙 X)) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
