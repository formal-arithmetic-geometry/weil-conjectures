/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
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
import Sheaf.CategoryTheory.ColimitSiteAbelianSectionDiagram
import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.CategoryTheory.Filtered.Final
import Mathlib.CategoryTheory.Limits.FilteredColimitCommutesFiniteLimit

/-! # A section-colimit presentation with finite covering axioms

Source: Stacks Project, Sites, Tag 0A35, the section formula and adjunction proof;
Modules on Sites, Tag 03CO, abelian extension.
(blueprint: lem-weil-pbc-colimit-site-finite-section-colimit-presentation).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Functor.sheafPullbackConstruction
namespace CategoryTheory

/-- Source: Stacks Project, Sites, Tag 0A35, equation-compute-pullback-to-limit
and the presentation, sheaf-condition and adjunction paragraphs; abelian extension
by Modules on Sites, Tag 03CO.
(blueprint: lem-weil-pbc-colimit-site-finite-section-colimit-presentation).

Proof: For each arrow a : j to k take the group of sections of a inverse image
of H at F(a)(X). The transition for a refinement b is the unit for F(b), followed
by the canonical comparison between iterated and composite inverse images and
transport along F.map_comp. The comparison is characterized by its adjunction
unit equation; uniqueness of adjuncts proves identity, composition and naturality
of the source units. These groups and maps give D and e, with the displayed
object isomorphisms alpha.

For an arbitrary limit object Y use the category of its stage presentations
above j. Lift finitely many objects and arrows using the supplied set colimits;
filteredness gives a common stage and eventual equality imposes endpoint and
composition equations there. This makes the presentation category filtered,
and the subcategory of refinements of any fixed presentation final. Take its
filtered abelian section colimit. Lift each restriction arrow to a common stage;
eventual equality and naturality make the restriction independent of the lift,
and give the presheaf identity and composition laws.

Each Q cover is the transported image of a finite stage cover by hQ and hfinite.
Covering pullbacks are preserved by hpullback and hVpullback. Lift the finitely
many matching-family objects and equations to a common stage. The sheaf equalizer
is then the filtered colimit of the stage sheaf equalizers. Filtered abelian
colimits commute with finite limits, including the empty product, so the
presheaf is a sheaf. Only finite composition and finite base change are needed.

Maps from this sheaf to T are compatible stage maps. Transpose them by the
stage adjunctions: the identity presentation gives a map from H to restriction
of T along V(j). Conversely that map supplies all the stage adjuncts, and the
colimit universal property assembles them. Adjunct uniqueness makes these
assignments mutually inverse and natural. Uniqueness of left adjoints identifies
this sheaf with the canonical V(j) inverse image, preserving the units.
At V(j)(X), presentations obtained by carrying X forward are final, by the
common-refinement and eventual-equality argument. Their colimit is therefore
the section group at V(j)(X). This supplies c and beta, and the unit comparison
is precisely the last displayed equation for every source section. This is a
section-colimit construction, with no vanishing assumption or detection claim.
-/
theorem colimit_site_finite_section_colimit_presentation
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
    (j : J) (H : Sheaf (P j).toGrothendieck AddCommGrpCat.{u})
    (X : F.obj j) :
    ∃ (D : Under j ⥤ AddCommGrpCat.{u})
      (e : (Functor.const (Under j)).obj (H.obj.obj (op X)) ⟶ D)
      (c : Cocone D)
      (β : c.pt ≅ ((sheafPullback (V.ι.app j).toFunctor AddCommGrpCat.{u}
        (P j).toGrothendieck Q.toGrothendieck).obj H).obj.obj
          (op ((V.ι.app j).toFunctor.obj X)))
      (α : ∀ a : Under j, D.obj a ≅
        ((sheafPullback (F.map a.hom).toFunctor AddCommGrpCat.{u}
          (P j).toGrothendieck (P a.right).toGrothendieck).obj H).obj.obj
            (op ((F.map a.hom).toFunctor.obj X))),
      Nonempty (IsColimit c) ∧
      (∀ a : Under j, e.app a ≫ (α a).hom =
        ((sheafAdjunctionContinuous (F.map a.hom).toFunctor AddCommGrpCat.{u}
          (P j).toGrothendieck (P a.right).toGrothendieck).unit.app H).hom.app
            (op X)) ∧
      (∀ a : Under j, e.app a ≫ c.ι.app a ≫ β.hom =
        ((sheafAdjunctionContinuous (V.ι.app j).toFunctor AddCommGrpCat.{u}
          (P j).toGrothendieck Q.toGrothendieck).unit.app H).hom.app (op X)) := by sorry

end CategoryTheory
