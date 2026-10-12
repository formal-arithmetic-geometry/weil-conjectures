/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.CategoryTheory.ColimitSites

/-! # Scalar stage-section representatives and eventual zero

Source: Stacks Project, Sites, Tags 09YM, 09YN and 0738; Modules on Sites, Tag 03CO.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Functor.sheafPullbackConstruction
namespace CategoryTheory

/-- Scalar sections of a colimit of inverse images have stage representatives,
and a stage representative of zero vanishes after one transition.
Source: Stacks Project, Sites, Tags 09YM and 09YN (proof), and Modules on Sites,
Tags 0738 and 03CO (finite-cover section comparison and abelian colimits).
(blueprint: lem-weil-pbc-colimit-site-scalar-section-comparison).

Proof: The laws for rho and mu form a diagram and a cocone of scalar section
groups over Under i. First hQ and hfinite imply that every limit-site covering
presieve is finite: its arrows are the image of a finite stage presieve. Thus
filtered abelian sheaf colimits are computed on sections, by the finite sheaf
matching-family equalizer and commutation of filtered colimits with finite
limits (0738); 03CO identifies abelian colimits with sheafified presheaf colimits.
Apply this to H and its specified colimit c, evaluated at V i X.
For each stage j, the inverse-image section formula 09YM expresses the sections
of H j as the filtered colimit of the sections of the further inverse images
of G j. For any finite set of presentations, arrows and relations, hobjects
and harrows put them at one common later stage. Therefore the category of
simultaneous refinements is filtered, and its diagonal subcategory is final:
a presentation has a common refinement with the fixed presentation (i,X),
and two such refinements become equal by eventual equality of their arrows.
The iterated colimit is consequently the colimit of the original G sections
on the objects F(a.hom) X. To identify its maps, transpose the maps of H through
sheaf adjunctions. The beta compatibility identifies these adjuncts with theta.
The supplied Arrow equations identify rho with these transitions, including
endpoint transport, and mu with the units followed by the coprojections of c.
The identity and composition laws ensure this is precisely the supplied scalar
diagram. The comparison is thus a colimiting cocone with apex C. Every element
of a filtered group colimit has a stage representative, giving the first clause.
Equality with the zero representative is witnessed after one further arrow,
giving the second clause. The sheaf equalizer for an empty cover is the zero
group, and the same finite-cover argument applies; no cover is assumed nonempty.
This scalar assertion contains no finite-product data or universal property for
an arbitrary product cocone.
-/
theorem colimitSite_scalar_sections_representatives_and_zero
    {J : Type u} [SmallCategory J] [IsFiltered J]
    (F : J ⥤ Cat.{u, u}) (P : ∀ j, Precoverage (F.obj j))
    [∀ j, (P j).HasIsos] [∀ j, (P j).IsStableUnderComposition]
    [∀ j, (P j).IsStableUnderBaseChange] [∀ j, (P j).HasPullbacks]
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
    [∀ (j k : J) (a : j ⟶ k), PreservesFiniteColimits
      (sheafPullback (F.map a).toFunctor (Type u)
        (P j).toGrothendieck (P k).toGrothendieck)]
    (V : Cocone F)
    (hobjects : IsColimit (Cat.objects.mapCocone V))
    (harrows : IsColimit (Cat.arrows.mapCocone V))
    (Q : Precoverage V.pt)
    [Q.HasIsos] [Q.IsStableUnderComposition] [Q.IsStableUnderBaseChange] [Q.HasPullbacks]
    (hQ : ∀ (Y : V.pt) (R : Presieve Y), R ∈ Q Y ↔
      ∃ (j : J) (X : F.obj j) (S : Presieve X) (h : (V.ι.app j).toFunctor.obj X = Y),
        S ∈ P j X ∧ h ▸ S.map (V.ι.app j).toFunctor = R)
    [∀ j, (V.ι.app j).toFunctor.IsContinuous (P j).toGrothendieck Q.toGrothendieck]
    (G : ∀ j, Sheaf (P j).toGrothendieck AddCommGrpCat.{u})
    (θ : ∀ (j k : J) (a : j ⟶ k),
      (G j).obj ⟶ (F.map a).toFunctor.op ⋙ (G k).obj)
    (H : J ⥤ Sheaf Q.toGrothendieck AddCommGrpCat.{u})
    (E : ∀ j, H.obj j ≅
      (sheafPullback (V.ι.app j).toFunctor AddCommGrpCat.{u}
        (P j).toGrothendieck Q.toGrothendieck).obj (G j)) :
    let β := fun (j : J) (X : F.obj j) ↦
      (((sheafAdjunctionContinuous (V.ι.app j).toFunctor AddCommGrpCat.{u}
        (P j).toGrothendieck Q.toGrothendieck).unit.app (G j)).hom.app (op X)) ≫
        (E j).inv.hom.app (op ((V.ι.app j).toFunctor.obj X))
    (∀ (j k : J) (a : j ⟶ k) (X : F.obj j),
      Arrow.mk (β j X ≫ (H.map a).hom.app (op ((V.ι.app j).toFunctor.obj X))) =
        Arrow.mk ((θ j k a).app (op X) ≫ β k ((F.map a).toFunctor.obj X))) →
    ∀ (c : Cocone H), IsColimit c →
    ∀ (i : J) (X : F.obj i),
    let B := fun a : Under i ↦
      (G a.right).obj.obj (op ((F.map a.hom).toFunctor.obj X))
    let C := c.pt.obj.obj (op ((V.ι.app i).toFunctor.obj X))
    ∀ (ρ : ∀ {a a' : Under i}, (a ⟶ a') → (B a ⟶ B a'))
      (μ : ∀ a : Under i, B a ⟶ C),
      (∀ a : Under i, ρ (𝟙 a) = 𝟙 (B a)) →
      (∀ {a a' a'' : Under i} (b : a ⟶ a') (b' : a' ⟶ a''),
        ρ (b ≫ b') = ρ b ≫ ρ b') →
      (∀ {a a' : Under i} (b : a ⟶ a'), ρ b ≫ μ a' = μ a) →
      (∀ {a a' : Under i} (b : a ⟶ a'),
        Arrow.mk (ρ b) = Arrow.mk ((θ a.right a'.right b.right).app
          (op ((F.map a.hom).toFunctor.obj X)))) →
      (∀ a : Under i, Arrow.mk (μ a) =
        Arrow.mk (β a.right ((F.map a.hom).toFunctor.obj X) ≫
          (c.ι.app a.right).hom.app
            (op ((V.ι.app a.right).toFunctor.obj
              ((F.map a.hom).toFunctor.obj X))))) →
      (∀ x : C, ∃ (a : Under i) (z : B a), μ a z = x) ∧
      (∀ (a : Under i) (z : B a), μ a z = 0 →
        ∃ (a' : Under i) (b : a ⟶ a'), ρ b z = 0) := by sorry

end CategoryTheory
