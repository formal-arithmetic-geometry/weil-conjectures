/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q118
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceAbsoluteQuasiSeparated
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceAffineQuasiFinite
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Limits.IsLimit
import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit
import WeilConjectures.AlgebraicGeometry.DescendClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-! # Eventual separatedness over a fixed algebraic-space base

Source: Stacks Project, Limits of Spaces, Tag 086X, lemma-eventually-separated
(blueprint: lem-sfb-space-fixed-base-eventually-separated).

All spaces are over Spec Z. The cone and its universal property are in the category over Y.
Quasi-compactness is written as the existence of a quasi-compact surjective etale atlas.
Absolute quasi-separatedness uses the shared affine-pair criterion. No finite-presentation
hypothesis or quasi-compactness hypothesis on Y occurs.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- In an affine-transition inverse system of qcqs algebraic spaces over a fixed
quasi-separated base, separatedness of the limit implies eventual separatedness.
Source: Stacks Project, Limits of Spaces, Tag 086X, lemma-eventually-separated;
Tag 084T, lemma-descend-separated
(blueprint: lem-sfb-space-fixed-base-eventually-separated).

Proof:
1. Choose a stage o and an affine surjective etale atlas U_o by
   [lem-trf-space-qc-finite-affine-atlas-refinement]. The relative atlas and relation
   towers of [lem-sfb-space-fixed-base-atlas-relation-tower] give affine U_a with
   limit U, relation schemes R_a with limit R, and qc separated mixed products over Y.
   Quasi-separatedness of Y suffices; its quasi-compactness is not used.
2. The tested relative diagonal j : R → U ×_Y U is closed since the limit map is
   separated. The atlas-relation helper identifies U ×_Y U as the limit of
   U_a ×_Y U over U, with affine transitions and qc stages. Since R → U is finite
   type, [pqf-lem-limit-immersion-descends] makes R → U_a ×_Y U closed at some a.
3. Fix a and view R_b → U_a ×_Y U_b as the base changes of the locally finite type
   map R_a → U_a ×_Y U_a over U_a, using the same helper. The schemes involved are
   qcqs. Apply [lem-weil-pbc-descend-closed-immersion] to obtain b ≥ a for which
   R_b → U_a ×_Y U_b is closed.
4. The map U_b ×_Y U_b → U_a ×_Y U_b is affine by [lem-sfb-space-affine-locality],
   hence separated by [lem-weil-pbc-affine-morphism-permanence]. Its composite
   with j_b is closed. Thus [lem-weil-pbc-closed-immersion-from-composite] makes
   j_b : R_b → U_b ×_Y U_b closed.
5. By [lem-trf-space-fibre-products-etale-covers] and
   [lem-weil-pbc-etale-composition-cancellation], U_b ×_Y U_b → X_b ×_Y X_b is a
   surjective etale scheme atlas. The pullback of the diagonal is j_b: on each
   test scheme both describe pairs of atlas sections with equal image in X_b.
   Apply [lem-sfb-space-closed-immersion-atlas-locality] to deduce that X_b → Y
   is separated. Representable etaleness is tested as in [def-trf-algebraic-space].
6. For c ≥ b the affine transition X_c → X_b is separated by
   [lem-sfb-space-affine-locality]. Composition with X_b → Y is separated by
   [lem-sfb-space-separated-fp-composition], so b is the required eventual bound. -/
theorem eventually_separated_over_fixed_base_of_isLimit
    (Y : AlgebraicSpace (Spec (CommRingCat.of (ULift.{u} ℤ))))
    (hY : IsAbsolutelyQuasiSeparated Y)
    {I : Type u} [PartialOrder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : Iᵒᵖ ⥤ Over Y) (c : Cone D) (hc : IsLimit c)
    (hqc : ∀ i : I, ∃ (U : Over (Spec (CommRingCat.of (ULift.{u} ℤ))))
      (a : yoneda.obj U ⟶ (D.obj (op i)).left.obj.obj),
      CompactSpace U.left ∧ IsEtale a ∧ IsSurjective a)
    (hqs : ∀ i : I, IsAbsolutelyQuasiSeparated (D.obj (op i)).left)
    (haff : ∀ (i j : I) (h : i ≤ j), MapIsAffine (D.map (homOfLE h).op).left)
    (hsep : MapIsSeparated c.pt.hom) :
    ∃ a₀ : I, ∀ a : I, a₀ ≤ a → MapIsSeparated (D.obj (op a)).hom := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
