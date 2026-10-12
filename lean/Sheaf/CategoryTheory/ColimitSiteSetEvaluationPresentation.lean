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


/-! # General-object section functor presentation

Source: Stacks Project, Sites, Tag 0A35.
(blueprint: lem-weil-pbc-colimit-site-set-evaluation-presentation).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Functor.sheafPullbackConstruction

namespace CategoryTheory

/-- Source: Stacks Project, Sites, Tag 0A35, general-object section construction and
final left-exactness paragraph.
(blueprint: lem-weil-pbc-colimit-site-set-evaluation-presentation).

Proof: For fixed i and Y, use all stage presentations of Y above i. Existence of a
presentation follows from hobjects and filteredness of J. A finite collection of
presentations has a common refinement by filteredness and eventual object equality;
parallel refinements are equalized using eventual arrow equality from harrows.
Thus the presentation category A is small and filtered. At a presentation (a,W),
assign the functor G to sections of the stage inverse image of G at W. Adjunction
transposes of units give its refinement maps, natural in G; uniqueness of adjuncts
proves identity and composition. These functors form L. Each stage inverse image
preserves finite limits by assumption and section evaluation does so because sheaf
limits are presheaf limits. Objectwise detection of limits proves that L preserves
finite limits. The colimit of L(G) is a presheaf in Y: lift restriction arrows and
verify independence, identities and composition using eventual equality. Finite
covers lift by hQ; preservation of covering pullbacks and commutation of filtered
colimits with finite products and equalizers show this presheaf is a sheaf.
Maps from this sheaf to H correspond to compatible stage maps. Stage adjunctions
identify them with a map from G to restriction of H along V i. The inverse uses
the identity presentation and the unit; uniqueness of adjuncts proves the inverse
identities. Unique unit-compatible left-adjoint isomorphisms therefore give the
asserted natural isomorphism, including naturality in G. If F i is empty, its
sheaf category is terminal and transition left exactness forces terminal sections
at later stages; the same argument applies. If V.pt is empty, there is no Y.
Empty covers are included as equalizers of empty finite products.
-/
theorem colimit_site_set_evaluation_presentation
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
    [Q.HasIsos] [Q.IsStableUnderFiniteComposition]
    [Q.IsStableUnderFiniteBaseChange] [Q.HasPullbacks]
    (hQ : (∀ (Y : V.pt) (R : Presieve Y), R ∈ Q Y ↔
          ∃ (j : J) (X : F.obj j) (S : Presieve X) (h : (V.ι.app j).toFunctor.obj X = Y),
            S ∈ P j X ∧ h ▸ S.map (V.ι.app j).toFunctor = R))
    (hVpullback : (∀ (j : J) (X Y Z : F.obj j) (R : Presieve X), R ∈ P j X →
            ∀ (f : Y ⟶ X) (g : Z ⟶ X), R f →
              PreservesLimit (cospan f g) (V.ι.app j).toFunctor))
    [∀ j : J, (V.ι.app j).toFunctor.IsContinuous
      (P j).toGrothendieck Q.toGrothendieck]
    (i : J) (Y : V.pt) :
    ∃ (A : Type u) (c : SmallCategory A), letI := c
      ∃ (hf : IsFiltered A), letI := hf
        ∃ (L : Sheaf (P i).toGrothendieck (Type u) ⥤ (A ⥤ Type u)),
          Nonempty (PreservesFiniteLimits L) ∧
          Nonempty ((sheafPullback (V.ι.app i).toFunctor (Type u)
            (P i).toGrothendieck Q.toGrothendieck ⋙
              sheafToPresheaf Q.toGrothendieck (Type u) ⋙
              (evaluation V.ptᵒᵖ (Type u)).obj (op Y)) ≅ L ⋙ colim) := by sorry

end CategoryTheory
