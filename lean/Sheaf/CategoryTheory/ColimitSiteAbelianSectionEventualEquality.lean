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

/-! # Eventual equality of abelian inverse-image sections

Source: Stacks Project, Sites, Tag 0A35, and Modules on Sites, Tag 03CO.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Functor.sheafPullbackConstruction
namespace CategoryTheory

/-- Source: Stacks Project, Sites, Tag 0A35, presentation independence and
unit-compatible adjunction identification; abelian extension by Modules on Sites,
Tag 03CO.
(blueprint: lem-weil-pbc-colimit-site-abelian-section-eventual-equality).

Proof: Build the presentation presheaf of abelian groups: its value at Y is the
filtered colimit over presentations of Y above i of stage inverse-image sections.
Representatives and eventual equality in the object and arrow set colimits give
common refinements, equalize parallel refinements, and make restrictions independent
of lifts. Finite covers lift by hQ; preserved covering pullbacks identify their
finite stage sheaf equalizers. Commutation of filtered abelian colimits with finite
limits makes this a sheaf, including empty covers. Compatible maps from it to H
transpose under the stage adjunctions to one map from G to V i restriction of H.
The identity presentation and unit give the inverse correspondence, so uniqueness
of left adjoints identifies this sheaf with the canonical inverse image,
compatibly with units. At V i U, presentations carrying U forward are final by
common refinement and eventual equality. The unit equations identify α with its
coprojections and θ with its refinement maps. Equality of the images of x and y
in the canonical inverse image is consequently equality in this filtered colimit.
The same-stage equality criterion for filtered colimits of underlying sets gives
a refinement b : t to t' equating their images. Its map is θ by adjunct uniqueness.
Both images have the same target group, so no endpoint transport is needed to
state their equality. This assertion supplies only eventual equality of existing
representatives; it makes no claim that all limit sections have representatives.
There is no U in an empty source stage, and the zero group case is immediate.
-/
theorem colimit_site_abelian_section_eventual_equality
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
    (θ : ∀ (t t' : Under i) (b : t ⟶ t'),
      (sheafPullback (F.map t.hom).toFunctor AddCommGrpCat.{u} (P i).toGrothendieck (P
        t.right).toGrothendieck).obj G ⟶
      ((F.map b.right).toFunctor.sheafPushforwardContinuous AddCommGrpCat.{u} (P
        t.right).toGrothendieck (P t'.right).toGrothendieck).obj
        ((sheafPullback (F.map t'.hom).toFunctor AddCommGrpCat.{u} (P i).toGrothendieck (P
          t'.right).toGrothendieck).obj G))
    (hα : ∀ (t : Under i) (X : F.obj i),
      Arrow.mk (((sheafAdjunctionContinuous (F.map t.hom).toFunctor AddCommGrpCat.{u} (P
        i).toGrothendieck (P t.right).toGrothendieck).unit.app G).hom.app (op X) ≫ (α t).hom.app
        (op ((F.map t.hom).toFunctor.obj X))) =
      Arrow.mk (((sheafAdjunctionContinuous (V.ι.app i).toFunctor AddCommGrpCat.{u} (P
        i).toGrothendieck Q.toGrothendieck).unit.app G).hom.app (op X)))
    (hθ : ∀ (t t' : Under i) (b : t ⟶ t') (X : F.obj i),
      Arrow.mk (((sheafAdjunctionContinuous (F.map t.hom).toFunctor AddCommGrpCat.{u} (P
        i).toGrothendieck (P t.right).toGrothendieck).unit.app G).hom.app (op X) ≫
        (θ t t' b).hom.app (op ((F.map t.hom).toFunctor.obj X))) =
      Arrow.mk (((sheafAdjunctionContinuous (F.map t'.hom).toFunctor AddCommGrpCat.{u} (P
        i).toGrothendieck (P t'.right).toGrothendieck).unit.app G).hom.app (op X)))
    (U : F.obj i) (t : Under i)
    (x y : ((sheafPullback (F.map t.hom).toFunctor AddCommGrpCat.{u}
      (P i).toGrothendieck (P t.right).toGrothendieck).obj G).obj.obj
        (op ((F.map t.hom).toFunctor.obj U)))
    (hxy : (α t).hom.app (op ((F.map t.hom).toFunctor.obj U)) x =
      (α t).hom.app (op ((F.map t.hom).toFunctor.obj U)) y) :
    ∃ (t' : Under i) (b : t ⟶ t'),
      (θ t t' b).hom.app (op ((F.map t.hom).toFunctor.obj U)) x =
        (θ t t' b).hom.app (op ((F.map t.hom).toFunctor.obj U)) y := by sorry

end CategoryTheory
