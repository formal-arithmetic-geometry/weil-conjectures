/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M2
-/
module

public import Sheaf.CategoryTheory.ArrowsFunctor
public import Sheaf.CategoryTheory.FinitePrecoverage
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits

/-! # Stage representatives of abelian inverse-image sections

Source: Stacks Project, Sites, Tag 0A35, and Modules on Sites, Tag 03CO.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Functor.sheafPullbackConstruction
namespace CategoryTheory

/-- Source: Stacks Project, Sites, Tag 0A35, the general-object section construction,
finite-cover sheaf equalizers and adjunction paragraphs; abelian extension by
Modules on Sites, Tag 03CO.
(blueprint: lem-weil-pbc-colimit-site-abelian-section-representatives).

Proof: For a limit object Y, use its stage presentations above i. Object and arrow
colimit representatives give presentations and restriction arrows; filteredness
and eventual equality give common refinements and equalize parallel refinements.
Take the filtered colimit of the abelian inverse-image sections of G on these
presentations. Restrictions are independent of lifts by eventual arrow equality.
Every Q-cover is a finite stage cover by hQ and hfinite. Covering pullbacks are
preserved, so its sheaf equalizer is a filtered colimit of finite stage equalizers.
The abelian forgetful functor preserves filtered colimits and finite limits;
therefore this presheaf is a sheaf, also for empty covers. Maps from it to H are
compatible stage maps, whose adjuncts are a single map from G to restriction of H
along V i. The inverse uses the identity presentation and the unit; uniqueness of
adjuncts proves both inverse identities. This gives the unit-compatible comparison
with the canonical inverse image. At Y = V i U the presentations carrying U forward
are final: move any presentation and its identifying arrow to a common stage and
use eventual object and arrow equality. Hence every section is represented at such
a stage. The unit equations hα identify the coprojections with α. The equality of
Y with V t.right (F t.hom U) comes from cocone naturality; HEq records its transport
without choosing an additional isomorphism. This asserts only representatives,
not uniqueness or eventual equality. Empty source stages have no U; empty covers
give zero section groups and the zero representative.
-/
theorem colimit_site_abelian_section_representatives
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
    (i : J) (G : Sheaf (P i).toGrothendieck AddCommGrpCat.{u})
    (α : ∀ t : Under i,
      (sheafPullback (F.map t.hom).toFunctor AddCommGrpCat.{u} (P i).toGrothendieck (P
        t.right).toGrothendieck).obj G ⟶
      ((V.ι.app t.right).toFunctor.sheafPushforwardContinuous AddCommGrpCat.{u} (P
        t.right).toGrothendieck Q.toGrothendieck).obj
        ((sheafPullback (V.ι.app i).toFunctor AddCommGrpCat.{u} (P i).toGrothendieck
          Q.toGrothendieck).obj G))
    (hα : ∀ (t : Under i) (X : F.obj i),
      Arrow.mk (((sheafAdjunctionContinuous (F.map t.hom).toFunctor AddCommGrpCat.{u} (P
        i).toGrothendieck (P t.right).toGrothendieck).unit.app G).hom.app (op X) ≫ (α t).hom.app
        (op ((F.map t.hom).toFunctor.obj X))) =
      Arrow.mk (((sheafAdjunctionContinuous (V.ι.app i).toFunctor AddCommGrpCat.{u} (P
        i).toGrothendieck Q.toGrothendieck).unit.app G).hom.app (op X)))
    (U : F.obj i)
    (x : ((sheafPullback (V.ι.app i).toFunctor AddCommGrpCat.{u}
      (P i).toGrothendieck Q.toGrothendieck).obj G).obj.obj
        (op ((V.ι.app i).toFunctor.obj U))) :
    ∃ (t : Under i)
      (y : ((sheafPullback (F.map t.hom).toFunctor AddCommGrpCat.{u}
        (P i).toGrothendieck (P t.right).toGrothendieck).obj G).obj.obj
          (op ((F.map t.hom).toFunctor.obj U))),
      HEq ((α t).hom.app (op ((F.map t.hom).toFunctor.obj U)) y) x := by sorry

end CategoryTheory
