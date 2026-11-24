/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FullAffineEtaleTopos
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
import WeilConjectures.AlgebraicGeometry.AffineEtaleRestrictionCompositionGamma
import WeilConjectures.AlgebraicGeometry.AffineEtaleRestrictionCompositionMates

/-! # Affine étale inverse-image composition coherence -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- Compatibility of the affine étale inverse images with composition of affine morphisms
(Stacks, Tags 09YQ, 04HR, 03CB and 03CC). -/
theorem affineEtale_inverseImage_restriction_composition
    (U : ∀ {X Y : Scheme.{u}} (h : Y ⟶ X) [IsAffineHom h],
        X.FullAffineEtale ⥤ Y.FullAffineEtale)
      (t : ∀ {X Y : Scheme.{u}} (h : Y ⟶ X) [IsAffineHom h],
        U h ⋙ fullAffineEtaleInclusion Y ≅
          fullAffineEtaleInclusion X ⋙ (MorphismProperty.Over.pullback @Etale ⊤ h))
    [hu : ∀ (X Y : Scheme.{u}) (h : Y ⟶ X) [IsAffineHom h],
      (U h).IsContinuous (fullAffineEtaleTopology X) (fullAffineEtaleTopology Y)]
    (L : ∀ {X Y : Scheme.{u}} (h : Y ⟶ X) [IsAffineHom h],
        Sheaf (fullAffineEtaleTopology X) (Type (u + 1)) ⥤
          Sheaf (fullAffineEtaleTopology Y) (Type (u + 1)))
      (a : ∀ {X Y : Scheme.{u}} (h : Y ⟶ X) [IsAffineHom h],
        L h ⊣ (U h).sheafPushforwardContinuous (Type (u + 1))
          (fullAffineEtaleTopology X) (fullAffineEtaleTopology Y))
    (e : ∀ {X Y : Scheme.{u}} (h : Y ⟶ X) [IsAffineHom h],
        etaleSetPullback h ⋙ ((fullAffineEtaleInclusion Y).sheafPushforwardContinuous (Type (u + 1))
          (fullAffineEtaleTopology Y) Y.smallEtaleTopology) ≅
          ((fullAffineEtaleInclusion X).sheafPushforwardContinuous (Type (u + 1))
          (fullAffineEtaleTopology X) X.smallEtaleTopology) ⋙ L h)
    (he : (∀ (X Y : Scheme.{u}) (h : Y ⟶ X) [IsAffineHom h]
      (G : Sheaf X.smallEtaleTopology (Type (u + 1)))
      (V : X.FullAffineEtale) (s : G.obj.obj (op V.obj)),
      ((e h).hom.app G).hom.app (op ((U h).obj V))
          (((etaleSetPullback h).obj G).obj.map ((t h).hom.app V).op
            ((((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
          (MorphismProperty.Over.pullback @Etale ⊤ h) (Type (u + 1))
          (X.smallGrothendieckTopology @Etale) (Y.smallGrothendieckTopology @Etale)).unit).app
          G).hom.app (op V.obj) s)) =
        ((a h).unit.app (((fullAffineEtaleInclusion X).sheafPushforwardContinuous (Type (u + 1))
          (fullAffineEtaleTopology X) X.smallEtaleTopology).obj G)).hom.app (op V) s))
    (c : ∀ {X Y Z : Scheme.{u}} (f : Y ⟶ X) (g : Z ⟶ Y)
        [IsAffineHom f] [IsAffineHom g],
        etaleSetPullback f ⋙ etaleSetPullback g ≅ etaleSetPullback (g ≫ f))
    (hc : (∀ (X Y Z : Scheme.{u}) (f : Y ⟶ X) (g : Z ⟶ Y)
      [IsAffineHom f] [IsAffineHom g]
      (G : Sheaf X.smallEtaleTopology (Type (u + 1)))
      (V : X.Etale) (s : G.obj.obj (op V)),
      ((c f g).hom.app G).hom.app (op ((MorphismProperty.Over.pullback @Etale ⊤ g).obj
          ((MorphismProperty.Over.pullback @Etale ⊤ f).obj V)))
        ((((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
          (MorphismProperty.Over.pullback @Etale ⊤ g) (Type (u + 1))
          (Y.smallGrothendieckTopology @Etale) (Z.smallGrothendieckTopology @Etale)).unit).app
          ((etaleSetPullback f).obj G)).hom.app
          (op ((MorphismProperty.Over.pullback @Etale ⊤ f).obj V))
          ((((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
          (MorphismProperty.Over.pullback @Etale ⊤ f) (Type (u + 1))
          (X.smallGrothendieckTopology @Etale) (Y.smallGrothendieckTopology @Etale)).unit).app
          G).hom.app (op V) s)) =
        ((etaleSetPullback (g ≫ f)).obj G).obj.map
          ((MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤) g f).inv.app V).op
          ((((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
          (MorphismProperty.Over.pullback @Etale ⊤ (g ≫ f)) (Type (u + 1))
          (X.smallGrothendieckTopology @Etale) (Z.smallGrothendieckTopology @Etale)).unit).app
          G).hom.app (op V) s))) :
    ∃ (gamma : ∀ {X Y Z : Scheme.{u}} (f : Y ⟶ X) (g : Z ⟶ Y)
        [IsAffineHom f] [IsAffineHom g], U f ⋙ U g ≅ U (g ≫ f))
      (d : ∀ {X Y Z : Scheme.{u}} (f : Y ⟶ X) (g : Z ⟶ Y)
        [IsAffineHom f] [IsAffineHom g], L f ⋙ L g ≅ L (g ≫ f)),
    (∀ (X Y Z : Scheme.{u}) (f : Y ⟶ X) (g : Z ⟶ Y)
      [IsAffineHom f] [IsAffineHom g] (V : X.FullAffineEtale),
      (fullAffineEtaleInclusion Z).map ((gamma f g).hom.app V) ≫ (t (g ≫ f)).hom.app V =
        (t g).hom.app ((U f).obj V) ≫
          (MorphismProperty.Over.pullback @Etale ⊤ g).map ((t f).hom.app V) ≫
          (MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤) g f).inv.app V.obj) ∧
    (∀ (X Y Z : Scheme.{u}) (f : Y ⟶ X) (g : Z ⟶ Y)
      [IsAffineHom f] [IsAffineHom g]
      (F : Sheaf (fullAffineEtaleTopology X) (Type (u + 1)))
      (V : X.FullAffineEtale) (s : F.obj.obj (op V)),
      ((d f g).hom.app F).hom.app (op ((U g).obj ((U f).obj V)))
          (((a g).unit.app ((L f).obj F)).hom.app (op ((U f).obj V))
            (((a f).unit.app F).hom.app (op V) s)) =
        ((L (g ≫ f)).obj F).obj.map ((gamma f g).hom.app V).op
          (((a (g ≫ f)).unit.app F).hom.app (op V) s)) ∧
    (∀ (X Y Z : Scheme.{u}) (f : Y ⟶ X) (g : Z ⟶ Y)
      [IsAffineHom f] [IsAffineHom g]
      (G : Sheaf X.smallEtaleTopology (Type (u + 1))),
      ((fullAffineEtaleInclusion Z).sheafPushforwardContinuous (Type (u + 1))
          (fullAffineEtaleTopology Z) Z.smallEtaleTopology).map ((c f g).hom.app G) ≫
          (e (g ≫ f)).hom.app G =
        (e g).hom.app ((etaleSetPullback f).obj G) ≫
          (L g).map ((e f).hom.app G) ≫ (d f g).hom.app (((fullAffineEtaleInclusion
          X).sheafPushforwardContinuous (Type (u + 1))
          (fullAffineEtaleTopology X) X.smallEtaleTopology).obj G)) := by
  obtain ⟨gamma, hgamma⟩ := affineEtale_restriction_composition_gamma U t
  obtain ⟨d, hd, hcompat⟩ :=
    affineEtale_restriction_composition_mates U t L a e he c hc gamma hgamma
  exact ⟨gamma, d, hgamma, hd, hcompat⟩

end AlgebraicGeometry.Scheme
