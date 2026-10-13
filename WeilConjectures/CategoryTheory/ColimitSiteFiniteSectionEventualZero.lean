/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.ArrowsFunctor
public import WeilConjectures.CategoryTheory.FinitePrecoverage
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.Grp.Colimits

/-! # Finite-site stage section eventual zero

Source: Stacks Project, Sites, Tag 0A35; Modules on Sites, Tag 03CO.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Functor.sheafPullbackConstruction
namespace CategoryTheory

/-- Source: Stacks Project, Sites, Tag 0A35, presentation construction and
adjunction identification; abelian groups as in Modules on Sites, Tag 03CO.
(blueprint: lem-weil-pbc-colimit-site-finite-section-eventual-zero).

Proof: For each limit object Y, consider presentations (t,W,p), where t is in Under i,
W belongs to F(t.right), and p identifies V(t.right)(W) with Y. Move two presentations
to a common stage and use eventual object equality to refine their representatives
until equal. Equalize parallel refinements using filteredness. Thus the presentation
category is filtered. Evaluate the unit-characterized adjunct stage maps at W;
adjunction uniqueness gives their identity and composition laws. Take their filtered
colimit in abelian groups. Lift restriction arrows by harrows and correct endpoints
using hobjects; eventual arrow equality makes the restriction independent of the
lift. Lifting finite arrow diagrams proves the presheaf laws. By hQ, every cover is
an image of a stage cover, and by hfinite it has finitely many arrows. Lift its
matching data and the finitely many compatibility equations to a common stage.
The preserved covering pullbacks identify the stage matching diagram. Filtered
abelian colimits commute with its finite products and equalizer, so the presheaf
is a sheaf; the empty matching diagram gives the zero group.

A morphism from this sheaf to T is a compatible family of maps on presentation
section groups. Identity refinements give stage sheaf maps, and the stage
adjunctions identify their compatible family with a map G to the restriction of T
along V i. The reverse assignment takes the adjunct at every stage. Adjunction
identities and colimit hom_ext show that the assignments are inverse and natural.
Uniqueness of left adjoints identifies the constructed sheaf with the canonical
inverse image, preserving its unit. At V i U, presentations carrying U forward
are final: lift any presentation to a common stage, enforce eventual object
equality, and equalize the refinement arrows. These constructions use only
object/arrow colimits, finite covers, and adjunctions; they do not use the parent
comparison-bijectivity theorem or any of its downstream zero-detection results.

Suppose (K.ι.app t).hom x is zero. By hK its representative (E t).hom x
maps to zero in the canonical inverse-image sections. Under the constructed
sheaf identification, compare this representative with zero. Equality in a
filtered colimit holds at a common refinement. Equalize the two refinement
arrows if necessary; additivity sends the zero representative to zero. Finality
of the carried-U presentations moves this refinement into Under i. The unit
equations hα and hθ identify its maps with α and θ by adjunct uniqueness.
The equation hD identifies its transported stage value with (E t').hom
((D.map b).hom x). Injectivity and additivity of E t' imply (D.map b).hom x = 0.

Edge cases: a zero section is killed by the identity refinement; zero section
groups satisfy the assertion by map_zero. In a constant identity diagram the
hypothesis already says x = 0. This asserts only eventual vanishing of a single
stage section, not surjectivity or bijectivity of a comparison.
-/
theorem colimit_site_finite_section_eventual_zero
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
    (U : F.obj i)
    (D : Under i ⥤ AddCommGrpCat.{u})
    (E : ∀ t : Under i, D.obj t ≅
      ((sheafPullback (F.map t.hom).toFunctor AddCommGrpCat.{u} (P i).toGrothendieck (P
        t.right).toGrothendieck).obj G).obj.obj (op ((F.map t.hom).toFunctor.obj U)))
    (K : Cocone D) (e : K.pt ≅ ((sheafPullback (V.ι.app i).toFunctor AddCommGrpCat.{u} (P
      i).toGrothendieck Q.toGrothendieck).obj G).obj.obj (op ((V.ι.app i).toFunctor.obj U)))
    (hK : ∀ t : Under i, Arrow.mk (K.ι.app t ≫ e.hom) =
      Arrow.mk ((E t).hom ≫ (α t).hom.app (op ((F.map t.hom).toFunctor.obj U))))
    (hD : ∀ (t t' : Under i) (b : t ⟶ t'),
      Arrow.mk ((E t).hom ≫ (θ t t' b).hom.app (op ((F.map t.hom).toFunctor.obj U))) =
      Arrow.mk (D.map b ≫ (E t').hom)) :
    ∀ (t : Under i) (x : D.obj t), (K.ι.app t).hom x = 0 →
      ∃ (t' : Under i) (b : t ⟶ t'), (D.map b).hom x = 0 := by sorry

end CategoryTheory
