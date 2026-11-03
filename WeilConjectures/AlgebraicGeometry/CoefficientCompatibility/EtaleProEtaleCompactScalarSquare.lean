/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CoefficientCompatibility.EtaleProEtaleCoefficientTransport
public import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactScalarCoherence
public import WeilConjectures.AlgebraicGeometry.Canonical.CanonicalCompactSupportSiteComparison
import WeilConjectures.AlgebraicGeometry.Compact.CompactSupportComparisonNormalization
import all WeilConjectures.AlgebraicGeometry.Sp.SpDirectImageEtaleMate
import all WeilConjectures.AlgebraicGeometry.OpenScalarSite.OpenScalarSiteCoherence
import all WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactScalarCoherence
import WeilConjectures.AlgebraicGeometry.Etale.ProEtale.EtaleProEtaleScalarMate
import WeilConjectures.AlgebraicGeometry.CoefficientCompatibility.RecordedCompactScalarNormalization

/-! # The normalized compact-support scalar/site equation

Source: Stacks Project, Tag 0GL6, and the proper/open mate pasting of the
Charts paragraph of the blueprint's reduction-exceptional proof.
(blueprint: lem-sp-transported-compact-scalar-site-square).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Functor
open AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.ProEtale.CoefficientCompatibility

attribute [local irreducible] transportedRecordedReductionDirectImageComparison
  compactSupportSiteComparison comparisonUpperStar pbcComparisonReduction
  Etale.compactScalarMap Functor.mapDerivedCategory Functor.rightDerivedFunctor
  Functor.leftDerivedFunctor pbcFixedScalarExtension DerivedCategory
  HasDerivedCategory.ofIsGrothendieckAbelian DerivedCategory.TStructure.t

attribute [local instance] proEtEssentiallySmall

-- The bounded-below compact comparison uses the same ambient proper counit mate.
end AlgebraicGeometry.ProEtale.CoefficientCompatibility

namespace AlgebraicGeometry.ProEtale.CoefficientCompatibility

private theorem compactComparison_inv
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (L : DerivedCategory.Plus
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (compactSupportSiteComparison A c).inv.app L =
      (directImageComparisonAmbient A c.g).app
          ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapDerivedCategory.obj
            L.obj) ≫
        (lowerStar (ModuleCat.{u + 1} A) c.g).rightDerivedFunctor.map
          ((mapDerivedCategoryOpenImmersionLowerShriekComparisonUpperStarIso
            (ModuleCat.{u + 1} A) c.i).hom.app L.obj) := by
  rw [← compactSupportComparisonNormalization]
  have h := sp_comparison_hom A c.g
    ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapDerivedCategory.obj
      L.obj)
    (Etale.exact_open_preserves_plus A c.i L)
  have hh : (spDirectImageComparisonIso A c.g
      ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapDerivedCategory.obj
        L.obj) (Etale.exact_open_preserves_plus A c.i L)).hom =
      (directImageComparisonAmbient A c.g).app
        ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapDerivedCategory.obj
          L.obj) := by
    simpa only [BoundaryComparison.directImageMate, BoundaryComparison.pullbackSquare,
      directImageComparisonAmbient, directImageComparisonAmbientPullbackIso,
      leftDerivedUpperStarIsoMapDerivedCategory, Etale.leftDerivedUpperStarIsoMapDerivedCategory,
      BoundaryComparison.comparison, TwoSquare.mk, TwoSquare.natTrans] using h
  rw [← hh]
  simp only [fixedCompactSupportComparisonIso, fixedDirectImageComparisonIso,
    spDirectImageComparisonIso, Iso.trans_inv, Iso.trans_hom, Iso.symm_inv, Iso.symm_hom,
    Iso.app_hom, Iso.app_inv, NatTrans.comp_app, Functor.isoWhiskerLeft_inv,
    Functor.isoWhiskerRight_inv, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_inv_app, Functor.associator_hom_app,
    Functor.map_comp, Functor.mapIso_hom,
    Functor.mapDerivedCategoryPlusCompatibility, Iso.refl_hom, Iso.refl_inv,
    NatTrans.id_app, Category.id_comp, Category.comp_id, Category.assoc,
    asIso_hom, mapDerivedCategoryOpenImmersionLowerShriekComparisonUpperStarIso]
  rw [← Functor.mapDerivedCategoryNatIso_symm]
  dsimp only [Functor.mapDerivedCategoryPlus, ObjectProperty.lift, Functor.comp_obj,
    DerivedCategory.Plus.ι, ObjectProperty.ι_obj]
  simp only [Iso.symm_symm_eq, Category.id_comp]
  erw [((Etale.lowerStar (ModuleCat.{u + 1} A) c.g).rightDerivedFunctor ⋙
    (comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory).map_id]
  erw [(lowerStar (ModuleCat.{u + 1} A) c.g).rightDerivedFunctor.map_id]
  erw [((comparisonUpperStar (ModuleCat.{u + 1} A) c.Z).mapDerivedCategory ⋙
    (lowerStar (ModuleCat.{u + 1} A) c.g).rightDerivedFunctor).map_id]
  repeat erw [Category.id_comp]

private def fixedCompactScalarMap
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (a : A →+* B) {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ⋙
        CoefficientScalarRepresentatives.extension.{u} (Scheme.ProEt.topology Y) a ⟶
      CoefficientScalarRepresentatives.extension.{u} (Scheme.ProEt.topology X) a ⋙
        rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} B) c :=
  whiskerLeft (openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapDerivedCategory
      (mateEquiv (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) c.g)
        (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} B) c.g)
        (TwoSquare.mk
          (CoefficientScalarRepresentatives.extension (Scheme.ProEt.topology Y) a) _ _
          (CoefficientScalarRepresentatives.extension (Scheme.ProEt.topology c.Z) a)
          (scalarPullbackProEtaleIso a c.g).hom)).natTrans ≫
    whiskerRight (OpenScalarSite.scalarOpen a c.i).hom
      (lowerStar (ModuleCat.{u + 1} B) c.g).rightDerivedFunctor

/-- Scalar/site square for the fixed-module proper scalar mate followed by the proper
image of the open scalar isomorphism, in the retained scalar coordinates.
Source: Stacks 0GL6; blueprint det-sp-reduction-exceptional, Charts
(blueprint: lem-sp-transported-compact-scalar-site-square).

Proof: put J = j_!L; J and its scalar extension are bounded below. Apply the
etale/pro-etale scalar mate to J and the proper map, and the open scalar/site
square to L. Move the open comparisons past the proper scalar and site mates by
naturality, then expand compactSupportSiteComparison and cancel its bounded-below
inclusion factors. -/
private theorem fixedCompactScalar_site_square
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (a : A →+* B) {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (hLB : DerivedCategory.TStructure.t.plus ((Etale.scalarExtension a X).obj L.obj)) :
    (CoefficientScalarRepresentatives.extension.{u} (Scheme.ProEt.topology Y) a).map
        ((compactSupportSiteComparison A c).inv.app L) ≫
      (fixedCompactScalarMap a c).app
        ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj L.obj) ≫
      (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} B) c).map
        ((CoefficientScalarRepresentatives.comparisonIso X a).hom.app L.obj) =
    (CoefficientScalarRepresentatives.comparisonIso Y a).hom.app
        ((Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj
          L.obj) ≫
      (comparisonUpperStar (ModuleCat.{u + 1} B) Y).mapDerivedCategory.map
        ((Etale.compactScalarMap a c).app L.obj) ≫
      (compactSupportSiteComparison B c).inv.app
        ⟨(Etale.scalarExtension a X).obj L.obj, hLB⟩ := by
  let JA := (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapDerivedCategory
  let RB := (lowerStar (ModuleCat.{u + 1} B) c.g).rightDerivedFunctor
  let T := CoefficientScalarRepresentatives.extension.{u} (Scheme.ProEt.topology Y) a
  let γ := (mateEquiv (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) c.g)
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} B) c.g)
    (TwoSquare.mk
          (CoefficientScalarRepresentatives.extension (Scheme.ProEt.topology Y) a) _ _
          (CoefficientScalarRepresentatives.extension (Scheme.ProEt.topology c.Z) a)
          (scalarPullbackProEtaleIso a c.g).hom)).natTrans
  let oA := (mapDerivedCategoryOpenImmersionLowerShriekComparisonUpperStarIso
    (ModuleCat.{u + 1} A) c.i).hom.app L.obj
  let eB := (Etale.ExceptionalCoefficients.openIso a c.i).hom.app L.obj
  have hJ := Etale.exact_open_preserves_plus A c.i L
  have hBJ := Etale.scalar_open_preserves_plus a c.i L hLB
  have hm :
      γ.app ((comparisonUpperStar (ModuleCat.{u + 1} A) c.Z).mapDerivedCategory.obj
          (JA.obj L.obj)) ≫
        RB.map ((CoefficientScalarRepresentatives.comparisonIso c.Z a).hom.app
          (JA.obj L.obj)) =
      T.map (directImageComparisonAmbientIso A c.g (JA.obj L.obj) hJ).inv ≫
        (CoefficientScalarRepresentatives.comparisonIso Y a).hom.app
          ((Etale.lowerStar (ModuleCat.{u + 1} A) c.g).rightDerivedFunctor.obj
            (JA.obj L.obj)) ≫
        (comparisonUpperStar (ModuleCat.{u + 1} B) Y).mapDerivedCategory.map
          ((mateEquiv
            (Etale.derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) c.g)
            (Etale.derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} B) c.g)
            (TwoSquare.mk
              (Etale.scalarExtension a Y) _ _ (Etale.scalarExtension a c.Z)
              (scalarPullbackEtaleIso a c.g).hom)).natTrans.app
              (JA.obj L.obj)) ≫
        (directImageComparisonAmbient B c.g).app
          ((Etale.scalarExtension a c.Z).obj (JA.obj L.obj)) :=
    etaleProEtale_scalar_mate a c.g (JA.obj L.obj) hJ hBJ
  have hp := congrArg (fun q ↦ T.map
    ((directImageComparisonAmbientIso A c.g (JA.obj L.obj) hJ).hom) ≫ q) hm
  dsimp only [T] at hp
  simp only [directImageComparisonAmbientIso, asIso_hom, asIso_inv,
    ← Functor.map_comp_assoc, IsIso.hom_inv_id] at hp
  erw [(CoefficientScalarRepresentatives.extension.{u} (Scheme.ProEt.topology Y) a).map_id,
    Category.id_comp] at hp
  have ho :
      (CoefficientScalarRepresentatives.extension (Scheme.ProEt.topology c.Z) a).map oA ≫
        (OpenScalarSite.scalarOpen a c.i).hom.app
          ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj L.obj) ≫
        (openImmersionLowerShriek (ModuleCat.{u + 1} B) c.i).mapDerivedCategory.map
          ((CoefficientScalarRepresentatives.comparisonIso X a).hom.app L.obj) =
      (CoefficientScalarRepresentatives.comparisonIso c.Z a).hom.app (JA.obj L.obj) ≫
        (comparisonUpperStar (ModuleCat.{u + 1} B) c.Z).mapDerivedCategory.map
          ((Etale.openScalarExtension a c.i).hom.app L.obj) ≫
        (mapDerivedCategoryOpenImmersionLowerShriekComparisonUpperStarIso
          (ModuleCat.{u + 1} B) c.i).hom.app ((Etale.scalarExtension a X).obj L.obj) :=
    OpenScalarSite.scalar_site_square_aux a c.i L.obj
  rw [← Etale.compactScalarOpen_eq] at ho
  have hn := γ.naturality oA
  dsimp only [Functor.comp_map] at hn
  have hb := (directImageComparisonAmbient B c.g).naturality eB
  dsimp only [Functor.comp_map] at hb
  rw [compactComparison_inv, compactComparison_inv]
  dsimp only [fixedCompactScalarMap, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, rightDerivedLowerShriekOfCompactification, Functor.comp_map]
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% hn]
  rw [← RB.map_comp, ← RB.map_comp, ho]
  simp only [Functor.map_comp]
  rw [reassoc_of% hp]
  rw [← reassoc_of% hb]
  simp only [Etale.compactScalarMap, Etale.ExceptionalCoefficients.compactSupportMap,
    Etale.scalarMate, scalarPullbackEtaleIso, Functor.map_comp, Category.assoc, eB, JA, RB,
    Etale.scalarExtension, Etale.rightDerivedLowerShriekOfCompactification, Functor.comp_obj]

end AlgebraicGeometry.ProEtale.CoefficientCompatibility
