/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.ArrowsFunctor
public import Mathlib.CategoryTheory.Functor.KanExtension.Basic
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import Mathlib.CategoryTheory.Filtered.Basic

/-! # A stagewise Kan comparison cocone is colimiting

Source: Stacks Project, Sites, Tag 0A35, arbitrary-object section formula.
(blueprint: lem-weil-pbc-colimit-stage-kan-cocone).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

/-- The generator comparison cocone for compatible stage presheaves is colimiting.
The supplied stage transitions satisfy identity and composition componentwise
as objects of Arrow(Set), which includes their endpoint transports.
This is a presheaf result: it uses neither a topology nor sheaf adjunctions.

Source: Stacks Project, Sites, Tag 0A35 (lemma-compute-pullback-to-limit),
arbitrary-object section formula and the verification of its independence of choices.
(blueprint: lem-weil-pbc-colimit-stage-kan-cocone).

Proof: Evaluate at U of F(j). By the pointwise Kan presentation, every element of
B(t)(V(j)U) has a representative consisting of a stage section x and an arrow from
V(j)U to V(t.right)X. The arrow colimit lifts that arrow to a later stage. The object
colimit makes its endpoints agree with the images of U and X after a further
refinement. Refine once more to receive k and equalize the two maps from i; this
makes the resulting stage an object of Under k and its image under Under.map a the
chosen refinement in Under i. Restriction of the transported section along the
lifted arrow, followed by e.inv, is a representative in D. The compatibility of
beta with theta and the prescribed formula hnu identify its image with the given
generator. This proves surjectivity of the comparison from colimit D.

For injectivity, equality in colimit B is eventual equality at one stage because
Under i is filtered. At that stage, a pointwise Kan colimit equality is a finite
chain of generating relations. Lift all objects and arrows of this chain into a
common stage using the object and arrow colimits, and make every asserted equation
hold by the filtered-set eventual-equality criterion. Equalize the maps out of k.
At the resulting object of Under k, Kan relations are the naturality equations for
beta, while outer transition relations become the D transitions by hD. Thus the
two representatives agree in colimit D. Identity and composition of theta
allow all refinements in the finite chain to be compared at this single stage.
These bijections are components of the map induced by nu, so its naturality is
already known. It is an isomorphism of
presheaves, and nu is colimiting by transport from the colimit cocone of D.
-/
theorem colimit_stage_kan_cocone
    (J : Type u) [SmallCategory J] [IsFiltered J] (F : J ⥤ Cat.{u, u})
    (V : Cocone F)
    (hobjects : IsColimit (Cat.objects.mapCocone V))
    (harrows : IsColimit (Cat.arrows.mapCocone V))
    (i : J) (A : ∀ t : Under i, (F.obj t.right)ᵒᵖ ⥤ Type u)
    (θ : ∀ (t t' : Under i) (c : t ⟶ t'),
      A t ⟶ (F.map c.right).toFunctor.op ⋙ A t')
    (hθid : ∀ (t : Under i) (X : (F.obj t.right)ᵒᵖ),
      Arrow.mk ((θ t t (𝟙 t)).app X) = Arrow.mk (𝟙 ((A t).obj X)))
    (hθcomp : ∀ (t t' t'' : Under i) (c : t ⟶ t') (d : t' ⟶ t'')
        (X : (F.obj t.right)ᵒᵖ),
      Arrow.mk ((θ t t' c).app X ≫
        (θ t' t'' d).app ((F.map c.right).toFunctor.op.obj X)) =
      Arrow.mk ((θ t t'' (c ≫ d)).app X))
    (B : Under i ⥤ (V.ptᵒᵖ ⥤ Type u))
    (β : ∀ t : Under i, A t ⟶ (V.ι.app t.right).toFunctor.op ⋙ B.obj t)
    (hβ : ∀ t : Under i, (B.obj t).IsLeftKanExtension (β t))
    (hβmap : ∀ (t t' : Under i) (c : t ⟶ t') (X : F.obj t.right),
      Arrow.mk ((β t).app (op X) ≫
        (B.map c).app (op ((V.ι.app t.right).toFunctor.obj X))) =
      Arrow.mk ((θ t t' c).app (op X) ≫
        (β t').app (op ((F.map c.right).toFunctor.obj X))))
    (j k : J) (a : i ⟶ k) (b : j ⟶ k)
    (D : Under k ⥤ ((F.obj j)ᵒᵖ ⥤ Type u))
    (e : ∀ t : Under k, D.obj t ≅
      (F.map (b ≫ t.hom)).toFunctor.op ⋙ A ((Under.map a).obj t))
    (hD : ∀ (t t' : Under k) (c : t ⟶ t') (U : (F.obj j)ᵒᵖ),
      Arrow.mk ((D.map c).app U ≫ (e t').hom.app U) =
      Arrow.mk ((e t).hom.app U ≫
        (θ ((Under.map a).obj t) ((Under.map a).obj t') ((Under.map a).map c)).app
          ((F.map (b ≫ t.hom)).toFunctor.op.obj U)))
    (ν : Cocone D)
    (hpt : ν.pt = (V.ι.app j).toFunctor.op ⋙ colimit B)
    (hν : ∀ (t : Under k) (U : (F.obj j)ᵒᵖ),
      Arrow.mk ((ν.ι.app t).app U) =
      Arrow.mk ((e t).hom.app U ≫
        (β ((Under.map a).obj t)).app ((F.map (b ≫ t.hom)).toFunctor.op.obj U) ≫
        (colimit.ι B ((Under.map a).obj t)).app
          ((V.ι.app t.right).toFunctor.op.obj
            ((F.map (b ≫ t.hom)).toFunctor.op.obj U)))) :
    Nonempty (IsColimit ν) := by sorry

end CategoryTheory
