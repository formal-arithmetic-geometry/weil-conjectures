/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import Sheaf.CategoryTheory.ArrowsFunctor
public import Sheaf.CategoryTheory.FinitePrecoverage
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.CategoryTheory.Comma.Over.Basic

public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic

/-! # Matching lifts of raw sections

Source: Stacks Project, Sites, Tag 0A35.
(blueprint: lem-weil-pbc-colimit-site-raw-section-matching-lift).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Functor.sheafPullbackConstruction

namespace CategoryTheory

/-- Source: Stacks Project, Sites, Tag 0A35 (lemma-compute-pullback-to-limit),
the finite-cover equalizer calculation, before applying the stage sheaf condition.
(blueprint: lem-weil-pbc-colimit-site-raw-section-matching-lift).

Proof: Compute each left Kan extension pointwise. Its generators are sections of a
stage inverse image together with an arrow from the evaluation object to a stage image.
The object and arrow set-colimits let us lift that arrow and its endpoints to a common
stage; restrict the section along the lifted arrow. A finite chain of Kan relations
can likewise be lifted to a later stage. Naturality of beta and h-beta-map turn its
relations into restriction and theta transport. The equation h-theta identifies theta
with the unique adjunction transpose of the unit, so these transports compose.
Consequently every raw section has a stage representative and every equality of raw
representatives holds after further refinement.

Index the original cover by R.uncurry. Its finiteness allows us to lift all its local
sections simultaneously to a stage receiving i and j. Transport the original cover
there; hcover makes it covering. For each pair of covering arrows, hx gives equality
on their pullback in the limit category. Covering pullbacks exist at the stage, and
hpullback and hVpullback identify their images with these limit pullbacks. Apply the
raw equality criterion to the finitely many resulting equations and refine once more
so all hold. The pullback universal property then gives compatibility on every common
test object. The resulting family y has the prescribed beta/colimit images by
naturality and h-beta-map. The cocone equation identifies the transported target W
with the original image target; its equality is e. The transported covering arrows,
indexed by T.uncurry, give exactly the original image presieve, including duplicates,
which is hT. If R is empty, use its transported empty cover and the empty family:
there are no sections or equations to lift. No amalgamation or uniqueness is asserted
and no arbitrary existential witness is used to define data.
-/
theorem colimit_site_raw_section_matching_lift
    (J : Type u) [SmallCategory J] [IsFiltered J] (F : J ⥤ Cat.{u, u})
    (P : ∀ j : J, Precoverage (F.obj j))
    [∀ j, (P j).HasIsos] [∀ j, (P j).IsStableUnderFiniteComposition]
    [∀ j, (P j).IsStableUnderFiniteBaseChange] [∀ j, (P j).HasPullbacks]
    (hfinite : ∀ (j : J) (X : F.obj j) (R : Presieve X), R ∈ P j X →
      Finite R.uncurry)
    (hcover : ∀ (j k : J) (a : j ⟶ k) (X : F.obj j) (R : Presieve X),
      R ∈ P j X → R.map (F.map a).toFunctor ∈ P k ((F.map a).toFunctor.obj X))
    (hpullback : ∀ (j k : J) (a : j ⟶ k) (X Y Z : F.obj j) (R : Presieve X),
      R ∈ P j X → ∀ (f : Y ⟶ X) (g : Z ⟶ X), R f →
        PreservesLimit (cospan f g) (F.map a).toFunctor)
    [∀ (j k : J) (a : j ⟶ k),
      (F.map a).toFunctor.IsContinuous (P j).toGrothendieck (P k).toGrothendieck]
    [∀ (j k : J) (a : j ⟶ k), PreservesFiniteLimits
      (sheafPullback (F.map a).toFunctor (Type u)
        (P j).toGrothendieck (P k).toGrothendieck)]
    (V : Cocone F)
    (hobjects : IsColimit (Cat.objects.mapCocone V))
    (harrows : IsColimit (Cat.arrows.mapCocone V))
    (Q : Precoverage V.pt)
    (hVpullback : (∀ (j : J) (X Y Z : F.obj j) (R : Presieve X), R ∈ P j X →
            ∀ (f : Y ⟶ X) (g : Z ⟶ X), R f →
              PreservesLimit (cospan f g) (V.ι.app j).toFunctor))
    [∀ j : J, (V.ι.app j).toFunctor.IsContinuous
      (P j).toGrothendieck Q.toGrothendieck]
    (i : J) (G : Sheaf (P i).toGrothendieck (Type u))
    (θ : ∀ (t t' : Under i) (b : t ⟶ t'),
                        (sheafPullback (F.map t.hom).toFunctor (Type u)
                          (P i).toGrothendieck (P t.right).toGrothendieck).obj G ⟶
                        ((F.map b.right).toFunctor.sheafPushforwardContinuous (Type u)
                          (P t.right).toGrothendieck (P t'.right).toGrothendieck).obj
                          ((sheafPullback (F.map t'.hom).toFunctor (Type u)
                            (P i).toGrothendieck (P t'.right).toGrothendieck).obj G))
    (hθ : ∀ (t t' : Under i) (b : t ⟶ t'),
      (∀ X : F.obj i,
                          Arrow.mk
                            (((sheafAdjunctionContinuous (F.map t.hom).toFunctor (Type u)
                              (P i).toGrothendieck (P t.right).toGrothendieck).unit.app
                                G).hom.app (op X) ≫
                              (θ t t' b).hom.app (op ((F.map t.hom).toFunctor.obj X))) =
                          Arrow.mk
                            (((sheafAdjunctionContinuous (F.map t'.hom).toFunctor (Type u)
                              (P i).toGrothendieck (P t'.right).toGrothendieck).unit.app
                                G).hom.app (op X))))
    (B : Under i ⥤ (V.ptᵒᵖ ⥤ Type u))
    (β : ∀ t : Under i,
      ((sheafPullback (F.map t.hom).toFunctor (Type u)
        (P i).toGrothendieck (P t.right).toGrothendieck).obj G).obj ⟶
        (V.ι.app t.right).toFunctor.op ⋙ B.obj t)
    (hβ : ∀ t : Under i, (B.obj t).IsLeftKanExtension (β t))
    (hβmap : ∀ (t t' : Under i) (b : t ⟶ t') (X : F.obj t.right),
      Arrow.mk ((β t).app (op X) ≫
        (B.map b).app (op ((V.ι.app t.right).toFunctor.obj X))) =
      Arrow.mk ((θ t t' b).hom.app (op X) ≫
        (β t').app (op ((F.map b.right).toFunctor.obj X))))
    (j : J) (X : F.obj j) (R : Presieve X) (hR : R ∈ P j X)
    (x : (R.map (V.ι.app j).toFunctor).FamilyOfElements (colimit B))
    (hx : x.Compatible) :
    ∃ (t : Under i) (W : F.obj t.right) (T : Presieve W) (hcoverT : T ∈ P t.right W)
      (e : (V.ι.app t.right).toFunctor.obj W = (V.ι.app j).toFunctor.obj X)
      (hT : Presieve.ofArrows
        (fun p : T.uncurry ↦ (V.ι.app t.right).toFunctor.obj p.val.1)
        (fun p ↦ (V.ι.app t.right).toFunctor.map p.val.2 ≫ eqToHom e) =
          R.map (V.ι.app j).toFunctor)
      (y : T.FamilyOfElements
        ((sheafPullback (F.map t.hom).toFunctor (Type u)
          (P i).toGrothendieck (P t.right).toGrothendieck).obj G).obj),
      y.Compatible ∧ ∀ p : T.uncurry,
        (colimit.ι B t).app (op ((V.ι.app t.right).toFunctor.obj p.val.1))
          ((β t).app (op p.val.1) (y p.val.2 p.property)) =
        x ((V.ι.app t.right).toFunctor.map p.val.2 ≫ eqToHom e)
          (hT ▸ Presieve.ofArrows.mk p) := by sorry

end CategoryTheory
