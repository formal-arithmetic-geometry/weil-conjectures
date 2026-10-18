/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q07
-/
module

public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import Mathlib.CategoryTheory.Yoneda
import Mathlib.CategoryTheory.Limits.Types.Filtered

/-!
# Simultaneous refinement of an inverse system on a site

Source: Stacks Project, Sites, Tag 00YP, Lemma `lemma-refine-all-at-once`
(blueprint: lem-trf-point-system-refine-all).

An inverse system is encoded covariantly in the opposite category. An order embedding
identifies the old index set with a subset carrying the induced order; equality of the
restricted functor keeps both its objects and transitions unchanged.
-/

@[expose] public section

universe u v w t r

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- Source: Stacks Project, Sites, the refinement maps preceding Tag 00YO
(blueprint: lem-trf-point-system-refine-all).
The canonical map on colimits induced by an inclusion of inverse systems, after applying
any presheaf. The equality `h` identifies the old diagram with the restricted new one. -/
noncomputable def pointSystemRefinementMap
    {C : Type u} [Category.{v} C]
    {J : Type w} [PartialOrder J] {I : Type r} [PartialOrder I]
    (V : J ⥤ Cᵒᵖ) (U : I ⥤ Cᵒᵖ) (e : J ↪o I)
    (h : V = e.monotone.functor ⋙ U) (P : Cᵒᵖ ⥤ Type t)
    [HasColimit (V ⋙ P)] [HasColimit (e.monotone.functor ⋙ (U ⋙ P))]
    [HasColimit (U ⋙ P)] : colimit (V ⋙ P) ⟶ colimit (U ⋙ P) :=
  colimMap (Functor.whiskerRight (eqToHom h) P ≫
    (Functor.associator e.monotone.functor U P).hom) ≫
      colimit.pre (U ⋙ P) e.monotone.functor

/-- Source: Stacks Project, Sites, Tag 00YP, Lemma `lemma-refine-all-at-once`
(blueprint: lem-trf-point-system-refine-all).
For a sheaf and two distinct germs in a directed inverse system, there is a refinement
preserving distinctness and lifting every original germ of a representable functor through
some member of every finite covering. `uliftYoneda` only places Hom sets in the common set
universe and its elements are exactly lifted morphisms.

Proof: Form the set E of all pairs of a finite covering and an element of the original
Hom colimit. Well-order E. Start with the original system and recurse through the order,
maintaining distinctness and the lifting conditions already processed. At a successor use
Tag 00YO (lem-trf-point-system-refine), applied to the current images of the two germs and
the selected original Hom germ. At a limit take the union of the nested index systems,
orders, objects and transitions. Two indices lie in one previous system, which supplies
an upper bound, so the union is still directed. If the two germs became equal in this
union, the filtered-colimit equality criterion
(lem-weil-pbc-filtered-colimit-sets-elementwise) would witness equality in a single earlier
system, a contradiction. Finally take the union over E. Each finite-cover/germ pair was
processed at one stage, and its factorization survives in the final colimit. The same
filtered-colimit criterion ensures the two final germs remain distinct. -/
theorem exists_pointSystem_refinement_all
    {C : Type u} [Category.{v} C] (K : Precoverage C)
    (hK : K.IsSiteForCoverings)
    {J : Type (max u v)} [PartialOrder J] [Nonempty J] [IsDirectedOrder J]
    (V : J ⥤ Cᵒᵖ) (F : Sheaf K.toGrothendieck (Type (max u v w)))
    (s s' : colimit (V ⋙ F.obj)) (hne : s ≠ s') :
    ∃ (I : Type (max u v)) (_ : PartialOrder I) (_ : Nonempty I)
      (_ : IsDirectedOrder I) (U : I ⥤ Cᵒᵖ) (e : J ↪o I)
      (h : V = e.monotone.functor ⋙ U),
      pointSystemRefinementMap V U e h F.obj s ≠
        pointSystemRefinementMap V U e h F.obj s' ∧
      ∀ (n : ℕ) (W : C) (Wk : Fin n → C) (a : ∀ k, Wk k ⟶ W),
        Presieve.ofArrows Wk a ∈ K W →
        ∀ f : colimit (V ⋙ uliftYoneda.{max u v}.obj W),
          ∃ (k : Fin n) (i : I) (b : (U.obj i).unop ⟶ Wk k),
            pointSystemRefinementMap V U e h (uliftYoneda.{max u v}.obj W) f =
              colimit.ι (U ⋙ uliftYoneda.{max u v}.obj W) i (ULift.up (b ≫ a k)) := by
  sorry

end CategoryTheory
