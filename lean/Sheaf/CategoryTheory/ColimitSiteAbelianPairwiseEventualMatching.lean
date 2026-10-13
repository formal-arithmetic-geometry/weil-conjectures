/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
-/
module

public import Sheaf.CategoryTheory.ColimitSiteAbelianStageImage
public import Sheaf.CategoryTheory.ArrowsFunctor
public import Sheaf.CategoryTheory.FinitePrecoverage

/-! # One eventual matching equation

Source: Stacks Project, Sites, Tag 0A35, section formula and adjunction paragraphs.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Functor.sheafPullbackConstruction
namespace CategoryTheory

/-- One pair of restrictions with matching colimit images agrees at a later stage.
Source: Stacks Project, Sites, Tag 0A35, section formula and finite-cover equalizer
and adjunction paragraphs; Modules on Sites, Tag 03CO, abelian interpretation.
(blueprint: lem-weil-pbc-colimit-site-abelian-pairwise-eventual-matching)

Proof: Put A = F(t.hom) inverse image of G and let x and z be the two restrictions
along gs and gr. Compatibility hy and naturality of alpha imply alpha_t(x) =
alpha_t(z). The composite adjunction for F(t.hom) and V_t and the direct V_i
adjunction have the same right adjoint. Their unique left-adjoint isomorphism,
compatible with their units, identifies alpha_t with the V_t unit on A followed
by that isomorphism. Each component of the isomorphism is injective. Thus the
V_t unit kills x - z in A(Z).

Use the section formula of Tag 0A35 for the source stage t.right, sheaf A, and
object Z: the sections of V_t inverse image of A at V_t(Z) are the filtered
colimit of sections of the later inverse images at the images of Z. The formula
is proved independently by constructing the presheaf of filtered section
colimits over presentations of each colimit-site object. The object and arrow
set colimits lift finite object, arrow, and relation data to a common stage and
make presentation refinements filtered and the refinements of any presentation
final. Restriction maps are induced by those lifts and independent of lifts by
eventual equality. Every covering family is the image of a finite stage cover;
preserved covering pullbacks and commutation of filtered abelian colimits with
finite limits give the sheaf equalizer, also for an empty cover. Transposing maps
out of this sheaf through the stage adjunctions identifies it with V_t inverse
image of A, compatibly with the source unit. This is a raw section-colimit
construction, not the already assembled stage-image sheaf that needs the present
finite-family stabilization theorem.

In this filtered colimit the representative x - z from the identity stage equals
zero. Equality of representatives is witnessed by a transition d : t.right to k;
unit compatibility says that the d adjunction unit kills x - z. Take t' to be
Under.mk(t.hom followed by d) and b its morphism with right component d. Apply
left-adjoint uniqueness once more to F(t.hom), F(d), and F(t'.hom): htheta
identifies the kernel of theta_b with that of the d unit. Therefore theta_b(x)
equals theta_b(z). This concerns one prescribed pair and one prescribed test
object only. It supplies neither a simultaneous transition for all pairs nor
compatibility at every object of a later stage nor descent to an image presieve.
-/
theorem colimit_site_abelian_pairwise_eventual_matching
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
    (t : Under i) (W : F.obj t.right) (T : Presieve W) (hT : T ∈ P t.right W)
    (y : T.FamilyOfElements
      (((sheafPullback (F.map t.hom).toFunctor AddCommGrpCat.{u}
        (P i).toGrothendieck (P t.right).toGrothendieck).obj G).obj ⋙
          forget AddCommGrpCat.{u}))
    (hy : (show T.FamilyOfElements
        ((V.ι.app t.right).toFunctor.op ⋙
          (ColimitSiteStageImage.target F P V Q i G).obj ⋙ forget AddCommGrpCat.{u}) from
        fun {Z} g hg ↦ (α t).hom.app (op Z) (y g hg)).Compatible)
    (Z : F.obj t.right) (s r : T.uncurry)
    (gs : Z ⟶ s.val.1) (gr : Z ⟶ r.val.1)
    (heq : gs ≫ s.val.2 = gr ≫ r.val.2) :
    ∃ (t' : Under i) (b : t ⟶ t'),
      (θ t t' b).hom.app (op Z)
          (((sheafPullback (F.map t.hom).toFunctor AddCommGrpCat.{u}
            (P i).toGrothendieck (P t.right).toGrothendieck).obj G).obj.map gs.op
              (y s.val.2 s.property)) =
        (θ t t' b).hom.app (op Z)
          (((sheafPullback (F.map t.hom).toFunctor AddCommGrpCat.{u}
            (P i).toGrothendieck (P t.right).toGrothendieck).obj G).obj.map gr.op
              (y r.val.2 r.property)) := by sorry

end CategoryTheory
