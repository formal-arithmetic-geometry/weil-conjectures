/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactSupportCoefficientChange
public import WeilConjectures.AlgebraicGeometry.Canonical.CanonicalOriginCompactSupportComposition
import WeilConjectures.AlgebraicGeometry.Compact.CompactSupportComparisonNormalization
import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactSupportCoefficientChange
import WeilConjectures.SixFunctors.Etale.Derived.CoefficientChange
import WeilConjectures.AlgebraicGeometry.Proper.ProperRestrictionSiteSquare
import WeilConjectures.AlgebraicGeometry.Open.OpenRestrictionSiteSquare
import all WeilConjectures.AlgebraicGeometry.Canonical.CanonicalOriginCompactSupportComposition
public import WeilConjectures.AlgebraicGeometry.Etale.Restriction.EtaleRestrictionBaseChange
public import WeilConjectures.SixFunctors.Etale.Derived.CoefficientChangeExchange

/-! # Scalar restriction and the compositor on etale-origin complexes

Source: Stacks Project, Tags 09AF, 099R, 0F7J and 0GL6
(blueprint: lem-sf-origin-compact-restriction-composition).
-/

@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 4096
universe u
open CategoryTheory
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale

private theorem pasted_boundary_word
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {X₀ X₁ X₂ : C} {Y₀ Y₁ Y₂ Y₃ Y₄ : D}
    (a : X₀ ⟶ X₁) (b : X₁ ⟶ X₂) (c : F.obj X₂ ⟶ Y₀)
    (d : Y₀ ⟶ Y₁) (e : Y₁ ⟶ Y₂) (f : Y₂ ⟶ Y₃) (g : Y₃ ⟶ Y₄) :
    F.map a ≫ F.map b ≫ c ≫ d ≫ e ≫ f ≫ g =
      F.map (a ≫ b) ≫ (c ≫ d) ≫ e ≫ (f ≫ g) := by
  simp only [Functor.map_comp, Category.assoc]

private theorem transport_square
    {C : Type*} [Category C] {S₀ S T₀ T V₀ V : C}
    (u : S₀ ⟶ S) [Epi u] (l₀ : S₀ ⟶ T₀) (l : S ⟶ T)
    (a₀ : S₀ ⟶ V₀) (a : S ⟶ V) (v : V₀ ⟶ V)
    (c₀ : V₀ ⟶ T₀) (c : V ⟶ T) (w : T₀ ⟶ T)
    (hl : u ≫ l = l₀ ≫ w) (h₀ : l₀ = a₀ ≫ c₀)
    (hc : v ≫ c = c₀ ≫ w) (ha : u ≫ a = a₀ ≫ v) : l = a ≫ c := by
  apply (cancel_epi u).mp
  rw [hl, h₀, Category.assoc, ← hc, ← reassoc_of% ha]

private noncomputable def boundedSite (A : Type (u + 1)) [CommRing A]
    (T : Scheme.{u}) :=
  DerivedCategory.Plus.ι ⋙ (comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory

private noncomputable def compactBoundary (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    boundedSite A X ⋙ rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ≅
      Etale.rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} A) c ⋙
        boundedSite A Y :=
  compactSupportSiteComparison A c ≪≫ Functor.isoWhiskerRight
    (Etale.rightDerivedLowerShriekOfCompactificationPlusCompatibility
      (ModuleCat.{u + 1} A) c).symm
    (comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory

private theorem origin_model_image
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    [QuasiCompact f] [QuasiCompact g]
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (originCompositionAmbient A f g).hom.app
        ((comparisonUpperStarPlusEtaleOrigin (ModuleCat.{u + 1} A) X).obj L) =
    (originCompositionModel A f g).hom.app L := by
  let I := (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) Z).ι
  let H := (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) Z).fullyFaithfulι
  have hm := (H.whiskeringRight _).map_preimage
    (X := originCompactSupport A f ⋙ originCompactSupport A g)
    (Y := originCompactSupport A (f ≫ g))
    (originCompositionAmbient A f g).hom
  change Functor.whiskerRight (originComposition A f g).hom I =
    (originCompositionAmbient A f g).hom at hm
  have h := originComposition_model A f g
  rw [hm] at h
  exact congr_app h L

private theorem origin_model_word
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    [QuasiCompact f] [QuasiCompact g]
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (originCompositionModel A f g).hom.app L =
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A) g).map
        ((compactBoundary A (HasCompactification.compactification f)).hom.app L) ≫
      (compactBoundary A (HasCompactification.compactification g)).hom.app
        ((Etale.rightDerivedLowerShriekPlus (ModuleCat.{u + 1} A) f).obj L) ≫
      (boundedSite A Z).map ((Etale.rightDerivedLowerShriekPlusCompIso A f g).hom.app L) ≫
      (compactBoundary A (HasCompactification.compactification (f ≫ g))).inv.app L := by
  conv_lhs =>
    simp only [originCompositionModel, Iso.trans_hom, Iso.symm_hom,
      Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
      Functor.isoWhiskerRight_inv, Functor.isoWhiskerLeft_inv,
      Functor.whiskerRight_app, Functor.whiskerLeft_app, NatTrans.comp_app,
      Functor.comp_map]
  exact pasted_boundary_word (rightDerivedLowerShriek (ModuleCat.{u + 1} A) g)
      ((compactSupportSiteComparison A (HasCompactification.compactification f)).hom.app L)
      ((comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory.map
        ((Etale.rightDerivedLowerShriekPlusCompatibility (ModuleCat.{u + 1} A) f).inv.app L))
      ((compactSupportSiteComparison A (HasCompactification.compactification g)).hom.app
        ((Etale.rightDerivedLowerShriekPlus (ModuleCat.{u + 1} A) f).obj L))
      ((comparisonUpperStar (ModuleCat.{u + 1} A) Z).mapDerivedCategory.map
        ((Etale.rightDerivedLowerShriekPlusCompatibility (ModuleCat.{u + 1} A) g).inv.app
          ((Etale.rightDerivedLowerShriekPlus (ModuleCat.{u + 1} A) f).obj L)))
      ((boundedSite A Z).map ((Etale.rightDerivedLowerShriekPlusCompIso A f g).hom.app L))
      ((comparisonUpperStar (ModuleCat.{u + 1} A) Z).mapDerivedCategory.map
        ((Etale.rightDerivedLowerShriekPlusCompatibility
          (ModuleCat.{u + 1} A) (f ≫ g)).hom.app L))
      ((compactSupportSiteComparison A
        (HasCompactification.compactification (f ≫ g))).inv.app L)

attribute [local irreducible] HasDerivedCategory.standard
  Functor.mapDerivedCategory Functor.rightDerivedFunctor
  Functor.leftAdjoint Functor.rightAdjoint
  comparisonUpperStar pbcDerivedComparisonRestrict compactSupportSiteComparison

attribute [local irreducible] originCompositionAmbient originCompositionModel

attribute [local irreducible] realizedEtaleCompositor

attribute [local irreducible] realizedCompositor

attribute [local irreducible] compactSupportRestrictionIso

attribute [local irreducible] restrictionCompositorLeft

end AlgebraicGeometry.ProEtale
