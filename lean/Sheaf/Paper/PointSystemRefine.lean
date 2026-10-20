/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.CategoryTheory.Limits.FilteredColimitCommutesFiniteLimit

/-!
# One-cover refinement of a pointed inverse system

Source: Stacks Project, Sites, Tag 00YO (Lemma lemma-refine), proof of Tag 00YP
(blueprint: lem-trf-point-system-refine).
-/

@[expose] public section

universe u v w t r

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

set_option autoImplicit false
set_option warn.sorry false

/-- The one-cover refinement lemma for the inverse-system point construction.

The section stalk is the filtered colimit of `F` along `V`, and the functor `u'`
is the filtered colimit of universe-lifted Yoneda representables along the same
inverse system. The index types live in an arbitrary universe `w`, the sheaf
takes values in `Type (max w t)` and the representables are lifted to
`Type (max w v)`, so that the filtered colimits over `J` exist without tying
`J`, `K` or the sheaf to the object universe of `C`. The canonical maps to a
refinement are Mathlib's `colimit.pre`; the factorization clause uses the map
induced by `uliftYoneda.map (wk k)`.

Proof steps from Tag 00YO, postponed at stage 2:
1. Represent `f` at an index of `J`, pass to its directed tail, and pull back the
   finite covering along that representative using the site pullback axiom
   [def-weil-pbc-sites-and-cohomology].
2. Apply the sheaf equalizer to obtain an injection into the finite product of
   sections on the pullbacks, and use filtered-colimit commutation with finite
   limits [lem-weil-pbc-filtered-colimits-commute-finite-limits] to choose a
   cover member preserving the distinct images of `s` and `s'`.
3. Form the disjoint-union refinement of the original index poset and its tail,
   with the pullback objects and transition maps from the proof of Tag 00YO.
4. The tail copy is cofinal, so distinctness survives under `colimit.pre`, and
   the pullback square gives the required factorization through `W_k`.
The equality `h` is retained explicitly so that both canonical maps remain
well-typed for arbitrary index and sheaf universes.

Source: Stacks Project, Sites, Tag 00YO (Lemma lemma-refine), proof of Tag 00YP
(blueprint: lem-trf-point-system-refine).
-/
theorem pointSystemRefine
    {C : Type u} [Category.{v} C]
    (P : Precoverage C) (hP : P.IsSiteForCoverings)
    {J : Type w} [Preorder J] [Nonempty J] [IsDirected J (· ≤ ·)]
    (V : Jᵒᵖ ⥤ C)
    (F : Sheaf P.toGrothendieck (Type (max w t)))
    {K : Type r} [Finite K]
    {W : C} (Wk : K → C) (wk : ∀ k, Wk k ⟶ W)
    (hcover : Presieve.ofArrows Wk wk ∈ P W)
    (s s' : colimit (V.rightOp ⋙ F.1)) (hs : s ≠ s')
    (f : colimit (V.rightOp ⋙ uliftYoneda.{w}.obj W)) :
    ∃ (I : Type w) (_ : Preorder I) (_ : Nonempty I)
      (_ : IsDirected I (· ≤ ·)) (U : Iᵒᵖ ⥤ C) (e : J ↪o I)
      (h : e.toOrderHom.toFunctor ⋙ U.rightOp = V.rightOp),
      (((eqToHom (congrArg (fun X : J ⥤ Cᵒᵖ => colimit (X ⋙ F.1)) h).symm) ≫
          colimit.pre (U.rightOp ⋙ F.1) e.toOrderHom.toFunctor) s ≠
        ((eqToHom (congrArg (fun X : J ⥤ Cᵒᵖ => colimit (X ⋙ F.1)) h).symm) ≫
          colimit.pre (U.rightOp ⋙ F.1) e.toOrderHom.toFunctor) s') ∧
      (∃ k : K,
        ∃ g : colimit (U.rightOp ⋙ uliftYoneda.{w}.obj (Wk k)),
          colimMap (U.rightOp.whiskerLeft (uliftYoneda.map (wk k))) g =
            ((eqToHom (congrArg
                (fun X : J ⥤ Cᵒᵖ => colimit (X ⋙ uliftYoneda.{w}.obj W)) h).symm) ≫
              colimit.pre (U.rightOp ⋙ uliftYoneda.{w}.obj W) e.toOrderHom.toFunctor) f) := by
  sorry

end CategoryTheory
