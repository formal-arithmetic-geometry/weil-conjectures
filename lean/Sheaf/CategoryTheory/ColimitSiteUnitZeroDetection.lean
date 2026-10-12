/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S2
-/
module

public import Sheaf.CategoryTheory.ColimitSites

/-! # Zero detection for the unit of inverse image to a colimit site

Source: Stacks Project, Sites, Tag 0A35, equation-compute-pullback-to-limit.
(blueprint: lem-weil-pbc-colimit-site-unit-zero-detection).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Functor.sheafPullbackConstruction
namespace CategoryTheory

/-- A section killed by the colimit-site inverse-image unit is killed by a stage unit.
Source: Stacks Project, Sites, Tag 0A35, equation-compute-pullback-to-limit.
(blueprint: lem-weil-pbc-colimit-site-unit-zero-detection).

Proof: The object and arrow colimit witnesses give the unique equivalence between
V.pt and the constructed filtered colimit category. It carries each canonical
stage functor to V.ι.app j. The image-covering characterization hQ identifies
its topology with Q. Transport the inverse-image section formula of Tag 0A35
across that equivalence. Uniqueness of left adjoints identifies the comparison
maps with the specified adjunction units. Apply the formula to G at X. The
section z is represented at the identity stage via the identity inverse-image
unit, which is an isomorphism. Since its image in the limit inverse image is
zero, the equality criterion for filtered colimits of underlying sets equates
this representative with zero at a common later stage. The transition out of
the identity representative is the unit along the resulting arrow d, by unit
coherence (or uniqueness of adjuncts). The formula applies to abelian sheaves:
the finite-cover sheaf equalizers and filtered colimits are computed on
underlying sets, and all comparison maps are additive. Thus every transport
preserves zero, and the unit along d kills z as claimed. This argument uses no
coefficient system, no composition isomorphisms supplied by a caller, and no
outer colimit of sheaves.
-/
theorem colimitSite_unit_zero_detection
    (J : Type u)
    [SmallCategory J]
    [IsFiltered J]
    (F : J ⥤ Cat.{u, u})
    (P : ∀ j : J, Precoverage (F.obj j))
    [∀ j, (P j).HasIsos]
    [∀ j, (P j).IsStableUnderComposition]
    [∀ j, (P j).IsStableUnderBaseChange]
    [∀ j, (P j).HasPullbacks]
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
    [Q.HasIsos]
    [Q.IsStableUnderComposition]
    [Q.IsStableUnderBaseChange]
    [Q.HasPullbacks]
    (hQ : ∀ (Y : V.pt) (R : Presieve Y), R ∈ Q Y ↔
      ∃ (j : J) (X : F.obj j) (S : Presieve X)
        (h : (V.ι.app j).toFunctor.obj X = Y),
        S ∈ P j X ∧ h ▸ S.map (V.ι.app j).toFunctor = R)
    (hVcover : ∀ (j : J) (X : F.obj j) (R : Presieve X), R ∈ P j X →
      R.map (V.ι.app j).toFunctor ∈ Q ((V.ι.app j).toFunctor.obj X))
    (hVpullback : ∀ (j : J) (X Y Z : F.obj j) (R : Presieve X), R ∈ P j X →
      ∀ (f : Y ⟶ X) (g : Z ⟶ X), R f →
        PreservesLimit (cospan f g) (V.ι.app j).toFunctor)
    [∀ j : J, (V.ι.app j).toFunctor.IsContinuous
      (P j).toGrothendieck Q.toGrothendieck]
    [∀ j : J, PreservesFiniteLimits (sheafPullback (V.ι.app j).toFunctor (Type u)
      (P j).toGrothendieck Q.toGrothendieck)]
    [∀ j : J, PreservesFiniteColimits (sheafPullback (V.ι.app j).toFunctor (Type u)
      (P j).toGrothendieck Q.toGrothendieck)]
    (j : J) (G : Sheaf (P j).toGrothendieck AddCommGrpCat.{u})
    (X : F.obj j) (z : G.obj.obj (op X))
    (hz : (((sheafAdjunctionContinuous (V.ι.app j).toFunctor AddCommGrpCat.{u}
      (P j).toGrothendieck Q.toGrothendieck).unit.app G).hom.app (op X)).hom z = 0) :
    ∃ (k : J) (d : j ⟶ k),
      (((sheafAdjunctionContinuous (F.map d).toFunctor AddCommGrpCat.{u}
        (P j).toGrothendieck (P k).toGrothendieck).unit.app
          G).hom.app (op X)).hom z = 0 := by sorry

end CategoryTheory
