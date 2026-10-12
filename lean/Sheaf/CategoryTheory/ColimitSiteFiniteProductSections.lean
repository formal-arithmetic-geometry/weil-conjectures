/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.CategoryTheory.ColimitSites
import Sheaf.CategoryTheory.ColimitSiteSections

/-! # Finite products of sections on a filtered colimit of sites

Source: Stacks Project, Sites, Tags 09YM and 09YN; Cohomology on Sites, Tag 09YP.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Functor.sheafPullbackConstruction

namespace CategoryTheory

/-- Finite products of stage sections have their canonical colimit universal property.
Source: Stacks Project, Sites, Tags 09YM and 09YN; Cohomology on Sites, proof of
Tag 09YP, the finite-product step of the displayed Čech comparison.
(blueprint: lem-weil-pbc-colimit-site-finite-product-sections).

Proof: first fix one object X(t) of F.obj i. The section formula 09YM computes
sections of each inverse image H(j) as the filtered colimit over later-stage
presentations of that object. Insert these formulas into the sectionwise
colimit of H. The category of simultaneous refinements is filtered: finite
objects, arrows and their equalities lift to a common stage by hobjects and
harrows. Its diagonal refinement functor is final, giving the colimit over
Under i of G(a.right)(F(a.hom)(X(t))). Under this comparison the coprojections
are beta followed by c's coprojections, and transition maps are theta, by the
assumed compatibility and the adjunction-unit equations. Every Q-cover is the
image of a finite stage cover by hQ and hfinite. Filtered sheaf colimits are
therefore computed on sections: filtered colimits commute with their finite
sheaf equalizer diagrams (09YN, and the abelian version 03CO). Thus the scalar
section comparison is an isomorphism, compatibly with these exact maps.
Now A is finite, so filtered colimits of abelian groups commute with the product
over A. Apply the scalar comparison to every X(t). The stated projection
identities identify D and K, via eD and eK, with that finite product diagram and
its canonical cocone. Product projections jointly determine homomorphisms, so
this identification respects all transitions and coprojections. Transfer the
colimit universal property across these isomorphisms to obtain IsColimit K.
For A empty, both identified objects are zero and every cocone has its unique
mediating zero map; no nonempty-cover assumption is used. For a singleton A
this is exactly the scalar formula. The choices of X(t) need not be products
or belong to a covering. This theorem asserts only a universal property for
already supplied objects, never a construction from arbitrary existence.
-/
theorem colimitSite_finiteProduct_sections_isColimit
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
    ∀ (i : J) {A : Type u} [Finite A] (X : A → F.obj i)
      (D : Under i ⥤ AddCommGrpCat.{u})
      (eD : ∀ a : Under i, D.obj a ≅ AddCommGrpCat.of
        (∀ t : A, (G a.right).obj.obj (op ((F.map a.hom).toFunctor.obj (X t)))))
      (K : Cocone D)
      (eK : K.pt ≅ AddCommGrpCat.of
        (∀ t : A, c.pt.obj.obj (op ((V.ι.app i).toFunctor.obj (X t))))),
      (∀ (a a' : Under i) (b : a ⟶ a') (t : A),
        Arrow.mk ((eD a).inv ≫ D.map b ≫ (eD a').hom ≫
          AddCommGrpCat.ofHom (Pi.evalAddMonoidHom _ t)) =
        Arrow.mk (AddCommGrpCat.ofHom (Pi.evalAddMonoidHom
          (fun t ↦ (G a.right).obj.obj
            (op ((F.map a.hom).toFunctor.obj (X t)))) t) ≫
          (θ a.right a'.right b.right).app
            (op ((F.map a.hom).toFunctor.obj (X t))))) →
      (∀ (a : Under i) (t : A),
        Arrow.mk ((eD a).inv ≫ K.ι.app a ≫ eK.hom ≫
          AddCommGrpCat.ofHom (Pi.evalAddMonoidHom _ t)) =
        Arrow.mk (AddCommGrpCat.ofHom (Pi.evalAddMonoidHom
          (fun t ↦ (G a.right).obj.obj
            (op ((F.map a.hom).toFunctor.obj (X t)))) t) ≫
          β a.right ((F.map a.hom).toFunctor.obj (X t)) ≫
          (c.ι.app a.right).hom.app
            (op ((V.ι.app a.right).toFunctor.obj
              ((F.map a.hom).toFunctor.obj (X t)))))) →
      Nonempty (IsColimit K) := by sorry

end CategoryTheory
