module

public import Sheaf.CategoryTheory.ColimitSites
public import Sheaf.CategoryTheory.SiteCechComplex

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Functor.sheafPullbackConstruction

namespace CategoryTheory

/-- Transport the covering and all its chosen iterated products, with their projections.
Source: Stacks Project, Sites, proof of Tag 09YL (the Hom pullback calculation).
(blueprint: lem-weil-pbc-colimit-of-sites-cech-complex-transport).

Proof: `hcover` transports the stage covering, since the image of `ofArrows` is the
presieve of the image arrows. The equivalence `hQ`, with witness `i`, transports the
covering to the colimit site. Each resulting covering has chosen iterated products by
`SiteCechComplex.exists_of_covering`. At a stage, induct on the number of factors:
the one-factor case is the object itself, and the next product is a pullback of one
original covering arrow along the remaining product's map to the base. `hpullback`
preserves this pullback, so the image satisfies the same universal property. This
argument applies to any original choice `S`, by uniqueness of the universal product.
For the canonical functor to the colimit, lift a test object, its finitely many arrows,
and their compatibility equations to a common stage using the object and arrow set
colimits. There the image of the original product is a product by the stage argument.
Lift its unique mediating arrow to the colimit. Two mediating arrows become equal at a
later common stage by the equality criterion for filtered set colimits; this proves
uniqueness. Thus the canonical functor also preserves these products (the argument of
09YL). Finally the universal properties of the image product and the chosen target
product give inverse maps: their composites have the identity projections and hence
are identities. The forward map commutes with each projection by its construction.
There are no tuples when the covering index is empty, since every degree has at least
one factor; all assertions about those tuples are then vacuous.
-/
theorem colimitSite_cech_complex_transport
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
    (hθid : ∀ (j : J) (X : F.obj j),
      Arrow.mk ((θ j j (𝟙 j)).app (op X)) = Arrow.mk (𝟙 ((G j).obj.obj (op X))))
    (hθcomp : ∀ (j k l : J) (a : j ⟶ k) (b : k ⟶ l) (X : F.obj j),
      Arrow.mk ((θ j l (a ≫ b)).app (op X)) =
        Arrow.mk ((θ j k a).app (op X) ≫
          (θ k l b).app (op ((F.map a).toFunctor.obj X))))
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
    ∀ (i : J) {T : Type u} [Finite T] {U : F.obj i}
      (f : T → F.obj i) (hom : ∀ t, f t ⟶ U),
      Presieve.ofArrows f hom ∈ P i U →
    ∀ S : SiteCechComplex f hom,
      (∀ a : Under i,
        Presieve.ofArrows (fun t ↦ (F.map a.hom).toFunctor.obj (f t))
          (fun t ↦ (F.map a.hom).toFunctor.map (hom t)) ∈
            P a.right ((F.map a.hom).toFunctor.obj U) ∧
        ∃ Sa : SiteCechComplex (fun t ↦ (F.map a.hom).toFunctor.obj (f t))
            (fun t ↦ (F.map a.hom).toFunctor.map (hom t)),
          ∀ (p : ℕ) (t : Fin (p + 1) → T),
            ∃ e : (F.map a.hom).toFunctor.obj (S.W p t) ≅ Sa.W p t,
              ∀ k, e.hom ≫ Sa.pr p t k = (F.map a.hom).toFunctor.map (S.pr p t k)) ∧
      (Presieve.ofArrows (fun t ↦ (V.ι.app i).toFunctor.obj (f t))
          (fun t ↦ (V.ι.app i).toFunctor.map (hom t)) ∈
            Q ((V.ι.app i).toFunctor.obj U) ∧
        ∃ Sc : SiteCechComplex (fun t ↦ (V.ι.app i).toFunctor.obj (f t))
            (fun t ↦ (V.ι.app i).toFunctor.map (hom t)),
          ∀ (p : ℕ) (t : Fin (p + 1) → T),
            ∃ e : (V.ι.app i).toFunctor.obj (S.W p t) ≅ Sc.W p t,
              ∀ k, e.hom ≫ Sc.pr p t k = (V.ι.app i).toFunctor.map (S.pr p t k)) := by
  sorry

end CategoryTheory
