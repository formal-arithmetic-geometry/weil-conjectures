/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Refinement.RefinementComparisonIsomorphism
public import WeilConjectures.AlgebraicGeometry.AmbientProperOpen.RefinementProjection.RefinementProjectionCounit
import WeilConjectures.AlgebraicGeometry.Finite.Clopen.FiniteClopenMateSiteTransport
import WeilConjectures.AlgebraicGeometry.FixedComparisonDirectImageMate
import WeilConjectures.AlgebraicGeometry.Proper.Open.ProperOpenRefinementMatePlusCompatibility
import WeilConjectures.AlgebraicGeometry.ClopenMateNormalization.EtaleClopenMateNormalization
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.CompConjugate
import WeilConjectures.Mathlib.CategoryTheory.Functor.Derived.Adjunction

/-! # Ambient normalization of the retained refinement arrow

Source: the refinement sentence of fix-prop-projection-formula.proof.md,
expanded in step 2 of lem-sf-finite-refinement-projection-realization.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option backward.defeqAttrib.useBackward true
set_option Elab.async false
attribute [local irreducible] HasDerivedCategory.standard
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.AmbientProperOpen
open RefinementProjection

namespace WeilConjectures.CompactSupportFiniteProjection

private def purityRefinementMate (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f]
    {c₁ c₂ : Compactification f} (v : c₁.Refinement c₂) :
    ProperOpenShriek A c₂.i ⟶
      ProperOpenShriek A c₁.i ⋙ ProperOpenPush A v.hom :=
  letI : QuasiCompact c₁.i := c₁.quasiCompact_openImmersion inferInstance
  letI : QuasiCompact c₂.i := c₂.quasiCompact_openImmersion inferInstance
  Functor.whiskerRight
    ((conjugateIsoEquiv
      (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) (𝟙 X))
      Adjunction.id) (leftDerivedUpperStarId (ModuleCat.{u + 1} A) X).symm).inv
    (ProperOpenShriek A c₂.i) ≫
    properOpenMate A c₁.i (𝟙 X) v.hom c₂.i
      (v.i_hom.trans (Category.id_comp c₂.i).symm)

private def purityEtaleRefinementComparison (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} {c₁ c₂ : Compactification f}
    (v : c₁.Refinement c₂)
    (H : DerivedCategory.Plus (Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} A))) :=
  let J₂ := Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) c₂.i
  J₂.mapDerivedCategoryPlus.map
      ((Etale.lowerStarIdDerivedPlus (ModuleCat.{u + 1} A) X).inv.app H) ≫
        (Etale.ClopenMateNormalization.normalizedComparison A c₁.i (𝟙 X)
          v.hom c₂.i (v.i_hom.trans (Category.id_comp c₂.i).symm)).hom.app H

private def purityRefinementSiteWordPlus (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} {c₁ c₂ : Compactification f}
    (v : c₁.Refinement c₂)
    (H : DerivedCategory.Plus (Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} A))) :=
  let N := comparisonUpperStar (ModuleCat.{u + 1} A) c₂.Z
  let J₁ := Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) c₁.i
  let R := (lowerStar (ModuleCat.{u + 1} A) v.hom).rightDerivedFunctorPlus
  (properOpenSiteExtensionIso A c₂.i).inv.app H ≫
    N.mapDerivedCategoryPlus.map (purityEtaleRefinementComparison A v H) ≫
    (fixedComparisonDirectImageMatePlus A v.hom).app (J₁.mapDerivedCategoryPlus.obj H) ≫
    R.map ((properOpenSiteExtensionIso A c₁.i).hom.app H)

private def purityRefinementSiteWord (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} {c₁ c₂ : Compactification f}
    (v : c₁.Refinement c₂)
    (H : DerivedCategory.Plus (Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} A))) :=
  let N := comparisonUpperStar (ModuleCat.{u + 1} A) X
  let J₁ := openImmersionLowerShriek (ModuleCat.{u + 1} A) c₁.i
  let J₂ := openImmersionLowerShriek (ModuleCat.{u + 1} A) c₂.i
  let R₀ := lowerStar (ModuleCat.{u + 1} A) v.hom
  let R := R₀.rightDerivedFunctor
  J₂.mapDerivedCategory.map (N.mapDerivedCategoryPlusCompatibility.inv.app H) ≫
    J₂.mapDerivedCategoryPlusCompatibility.inv.app (N.mapDerivedCategoryPlus.obj H) ≫
    DerivedCategory.Plus.ι.map (purityRefinementSiteWordPlus A v H) ≫
    R₀.rightDerivedFunctorPlusCompatibility.hom.app
        (J₁.mapDerivedCategoryPlus.obj (N.mapDerivedCategoryPlus.obj H)) ≫
          R.map (J₁.mapDerivedCategoryPlusCompatibility.hom.app
            (N.mapDerivedCategoryPlus.obj H)) ≫
          R.map (J₁.mapDerivedCategory.map (N.mapDerivedCategoryPlusCompatibility.hom.app H))

attribute [local implicit_reducible] Etale.rightDerivedLowerStarPlus
attribute [local irreducible] properOpenMate properOpenAlpha

private theorem refinementSiteWordPlus_eq (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f]
    {c₁ c₂ : Compactification f} (v : c₁.Refinement c₂)
    (H : DerivedCategory.Plus (Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} A))) :
    let N := comparisonUpperStar (ModuleCat.{u + 1} A) X
    let J₂ := openImmersionLowerShriek (ModuleCat.{u + 1} A) c₂.i
    let d := Functor.rightDerivedFunctorPlusNatIso
      (lowerStarId (ModuleCat.{u + 1} A) X) ≪≫
        Functor.rightDerivedFunctorPlusIdIso _
    haveI := c₁.quasiCompact_openImmersion (inferInstance : QuasiCompact f)
    haveI := c₂.quasiCompact_openImmersion (inferInstance : QuasiCompact f)
    J₂.mapDerivedCategoryPlus.map (d.inv.app (N.mapDerivedCategoryPlus.obj H)) ≫
      (cbcClopenMatePlus A c₁.i c₂.i (𝟙 X) v.hom
        (v.i_hom.trans (Category.id_comp c₂.i).symm)).app
          (N.mapDerivedCategoryPlus.obj H) = purityRefinementSiteWordPlus A v H := by
  have := c₁.quasiCompact_openImmersion (inferInstance : QuasiCompact f)
  have := c₂.quasiCompact_openImmersion (inferInstance : QuasiCompact f)
  let N := (comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategoryPlus
  let J₂ := (openImmersionLowerShriek
    (ModuleCat.{u + 1} A) c₂.i).mapDerivedCategoryPlus
  let E₂ := (Etale.openImmersionLowerShriek
    (ModuleCat.{u + 1} A) c₂.i).mapDerivedCategoryPlus
  let N₂ := (comparisonUpperStar
    (ModuleCat.{u + 1} A) c₂.Z).mapDerivedCategoryPlus
  let d := Functor.rightDerivedFunctorPlusNatIso
    (lowerStarId (ModuleCat.{u + 1} A) X) ≪≫
      Functor.rightDerivedFunctorPlusIdIso _
  let e := Etale.lowerStarIdDerivedPlus (ModuleCat.{u + 1} A) X
  let b := fixedComparisonDirectImageMatePlus A (𝟙 X)
  let o := properOpenSiteExtensionIso A c₂.i
  have hid : N.map (e.inv.app H) ≫ b.app H = d.inv.app (N.obj H) := by
    apply (cancel_mono (d.hom.app (N.obj H))).1
    erw [Category.assoc]
    have hb := comparisonDirectImagePlus_id A X H
    change b.app H ≫ d.hom.app (N.obj H) = N.map (e.hom.app H) at hb
    rw [hb, ← N.map_comp, e.inv_hom_id_app, N.map_id, d.inv_hom_id_app]
    rfl
  have ht := (finiteClopenMateSiteTransport A c₁.i c₂.i (𝟙 X) v.hom
    (v.i_hom.trans (Category.id_comp c₂.i).symm)).2.2.2.2.2 H
  have htransport := ht.2.1
  rw [ht.1] at htransport
  have ho := o.hom.naturality (e.inv.app H)
  change N₂.map (E₂.map (e.inv.app H)) ≫ o.hom.app _ =
    o.hom.app H ≫ J₂.map (N.map (e.inv.app H)) at ho
  change J₂.map (d.inv.app (N.obj H)) ≫ _ = _
  erw [← hid, J₂.map_comp, Category.assoc]
  apply (cancel_epi (o.hom.app H)).1
  erw [← Category.assoc, ← ho]
  simp only [Category.assoc]
  erw [htransport]
  dsimp only [o, N₂, E₂, e]
  simp only [purityRefinementSiteWordPlus, purityEtaleRefinementComparison,
    Category.assoc, Functor.map_comp, Iso.hom_inv_id_app_assoc]

private theorem etaleRefinementComparison_eq (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} {c₁ c₂ : Compactification f}
    (v : c₁.Refinement c₂)
    (H : DerivedCategory.Plus (Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} A))) :
    purityEtaleRefinementComparison A v H =
      Etale.properOpenComparison A v.hom c₁.i c₂.i v.i_hom H := by
  exact (Etale.properOpenInterchangeCoherence A).choose_spec.choose_spec.2.2.1
    v.hom c₁.i c₂.i v.i_hom H

private theorem refinementSiteWord_eq (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} {c₁ c₂ : Compactification f}
    (v : c₁.Refinement c₂)
    (H : DerivedCategory.Plus (Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} A))) :
    purityRefinementSiteWord A v H =
      (properOpenProEtaleIso A v.hom c₁.i c₂.i v.i_hom H).hom := by
  have hp : purityRefinementSiteWordPlus A v H =
      (properOpenProEtaleIsoPlus A v.hom c₁.i c₂.i v.i_hom H).hom := by
    simp only [purityRefinementSiteWordPlus, etaleRefinementComparison_eq,
      properOpenProEtaleIsoPlus, Iso.trans_hom, Iso.symm_hom, Iso.app_hom,
      Functor.mapIso_hom, asIso_hom, fixedComparisonDirectImageMatePlus]
  simp only [purityRefinementSiteWord, hp, properOpenProEtaleIso,
    Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Functor.mapIso_hom, Iso.app_inv]

private theorem mateTransport
    {C D : Type*} [Category* C] [Category* D] {F G : C ⥤ D}
    (γ : F ⟶ G) {K M : C} (a : K ≅ M) :
    F.map a.inv ≫ γ.app K ≫ G.map a.hom = γ.app M := by
  rw [← γ.naturality a.hom, ← Category.assoc, ← F.map_comp,
    a.inv_hom_id, F.map_id, Category.id_comp]

section
attribute [local irreducible] Functor.mapDerivedCategory Functor.rightDerivedFunctor
  derivedUpperStarLowerStarAdjunction leftDerivedUpperStarComp

private theorem refinementMate_eq_siteWord (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f]
    {c₁ c₂ : Compactification f} (v : c₁.Refinement c₂)
    (H : DerivedCategory.Plus (Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} A))) :
    (purityRefinementMate A v).app
        ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj
          H.obj) = purityRefinementSiteWord A v H := by
  have := c₁.quasiCompact_openImmersion (inferInstance : QuasiCompact f)
  have := c₂.quasiCompact_openImmersion (inferInstance : QuasiCompact f)
  let N := comparisonUpperStar (ModuleCat.{u + 1} A) X
  let J₁ := openImmersionLowerShriek (ModuleCat.{u + 1} A) c₁.i
  let J₂ := openImmersionLowerShriek (ModuleCat.{u + 1} A) c₂.i
  let R := (lowerStar (ModuleCat.{u + 1} A) v.hom).rightDerivedFunctor
  let e := N.mapDerivedCategoryPlusCompatibility.app H
  let K := N.mapDerivedCategoryPlus.obj H
  have hc := properOpenRefinementMate_plus_compatibility A
    v.hom c₁.i c₂.i v.i_hom K
  change (purityRefinementMate A v).app K.obj = _ at hc
  have ht := mateTransport (purityRefinementMate A v) e
  calc
    (purityRefinementMate A v).app (N.mapDerivedCategory.obj H.obj) =
        J₂.mapDerivedCategory.map e.inv ≫ (purityRefinementMate A v).app K.obj ≫
          R.map (J₁.mapDerivedCategory.map e.hom) := ht.symm
    _ = J₂.mapDerivedCategory.map e.inv ≫
        (J₂.mapDerivedCategoryPlusCompatibility.inv.app K ≫
          DerivedCategory.Plus.ι.map
            (J₂.mapDerivedCategoryPlus.map
                ((Functor.rightDerivedFunctorPlusNatIso
                    (lowerStarId (ModuleCat.{u + 1} A) X) ≪≫
                  Functor.rightDerivedFunctorPlusIdIso _).inv.app K) ≫
              (cbcClopenMatePlus A c₁.i c₂.i (𝟙 X) v.hom
                (v.i_hom.trans (Category.id_comp c₂.i).symm)).app K) ≫
          (lowerStar (ModuleCat.{u + 1} A) v.hom).rightDerivedFunctorPlusCompatibility.hom.app
            (J₁.mapDerivedCategoryPlus.obj K) ≫
          R.map (J₁.mapDerivedCategoryPlusCompatibility.hom.app K)) ≫
          R.map (J₁.mapDerivedCategory.map e.hom) :=
      congrArg (fun t ↦ J₂.mapDerivedCategory.map e.inv ≫ t ≫
        R.map (J₁.mapDerivedCategory.map e.hom)) hc
    _ = purityRefinementSiteWord A v H := by
      rw [refinementSiteWordPlus_eq A v H]
      simp only [purityRefinementSiteWord, J₁, J₂, R, N, K, e, Iso.app_inv,
        Iso.app_hom, Category.assoc]

end

private theorem derived_compositor_conjugate
    (A : Type (u + 1)) [CommRing A]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (finiteDirectImageComposition A f g).inv =
      conjugateEquiv
        ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) g).comp
          (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f))
        (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) (f ≫ g))
        (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) f g).hom := by
  have : (lowerStar (ModuleCat.{u + 1} A) f).PreservesKInjectiveComplexes :=
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f).preservesKInjectiveComplexes
  have hadj {S T : Scheme.{u}} (h : S ⟶ T) :
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) h
        ).mapDerivedCategoryRightDerivedAdjunction =
      (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) h).ofNatIsoLeft
        (upperStar (ModuleCat.{u + 1} A) h).leftDerivedFunctorIsoMapDerivedCategory := by
    refine ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) h
      ).mapHomotopyCategory (.up ℤ)).derived_eq_ofNatIsoLeft
      (HomotopyCategory.quasiIso _ (.up ℤ))
      (HomotopyCategory.quasiIso _ (.up ℤ)) _ _ _
      (upperStar (ModuleCat.{u + 1} A) h).leftDerivedFunctorIsoMapDerivedCategory.symm ?_
    ext K
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Iso.symm_hom]
    have hfac := congr_app
      (Functor.leftDerivedFunctorIsoMapDerivedCategory_hom_fac
        (upperStar (ModuleCat.{u + 1} A) h)) K
    dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app] at hfac
    exact (Iso.eq_inv_comp
      ((upperStar (ModuleCat.{u + 1} A) h).leftDerivedFunctorIsoMapDerivedCategory.app
        (DerivedCategory.Qh.obj K))).2 hfac
  change (Functor.rightDerivedFunctorCompIso'
    (lowerStar (ModuleCat.{u + 1} A) f) (lowerStar (ModuleCat.{u + 1} A) g)
    (lowerStarComp (ModuleCat.{u + 1} A) f g)).hom = _
  rw [Adjunction.rightDerivedFunctorCompIso'_hom_eq_conjugateEquiv
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f)
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) g)
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) (f ≫ g))
    _ (upperStarComp (ModuleCat.{u + 1} A) f g) (by
      simp [upperStarComp])]
  rw [hadj, hadj, hadj]
  ext K
  simp [conjugateEquiv_apply_app, leftDerivedUpperStarComp, Functor.leftDerivedFunctorNatIso,
    Functor.leftDerivedFunctorCompIso]

private theorem derived_compositor_conjugate_iso
    (A : Type (u + 1)) [CommRing A]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (finiteDirectImageComposition A f g).inv =
      (conjugateIsoEquiv
        ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) g).comp
          (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f))
        (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) (f ≫ g))
        (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) f g)).hom := by
  simpa only [conjugateIsoEquiv_apply_hom] using derived_compositor_conjugate A f g

private theorem inverse_indexIso
    {I C : Type*} [Category C] (P : I → C) {i j : I} (h : i = j) :
    (eqToIso (congrArg P h.symm)).inv = (indexIso P h).hom := by
  subst j
  rfl

attribute [local irreducible] derivedUpperStarLowerStarAdjunction
  leftDerivedUpperStarComp Functor.mapDerivedCategory Functor.rightDerivedFunctor

private theorem ordinary_identity_inv
    (D : FiniteFieldDatum.{u}) (A : Type (u + 1)) [CommRing A] [Finite A]
    (X : Spaces D) (M : ProperOpenDerived A X.obj.left) :
    ((ordinary D A).sId X).inv.app M =
      ((conjugateIsoEquiv
        (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) (𝟙 X.obj.left))
        Adjunction.id)
        (leftDerivedUpperStarId (ModuleCat.{u + 1} A) X.obj.left).symm).inv.app M := by
  dsimp only [ordinary, Calculus.sId]
  rfl

private theorem finiteComparison_word
    (D : FiniteFieldDatum.{u}) (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Spaces D} {f : X ⟶ Y} [QuasiCompact f.hom.left]
    {c d : Compactification f.hom.left} (r : c.Refinement d)
    (M : ProperOpenDerived A X.obj.left) :
    RefinementProjection.finiteComparison D A r M =
      (lowerStar (ModuleCat.{u + 1} A) d.g).rightDerivedFunctor.map
        ((purityRefinementMate A r).app M) ≫
        (conjugateIsoEquiv
          ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) d.g).comp
            (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) r.hom))
          (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) (r.hom ≫ d.g))
          (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) r.hom d.g)).hom.app
            ((openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapDerivedCategory.obj M) ≫
          (indexIso (fun q : c.Z ⟶ Y.obj.left ↦
            (lowerStar (ModuleCat.{u + 1} A) q).rightDerivedFunctor) r.hom_g).hom.app
            ((openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapDerivedCategory.obj M) := by
  let := c.quasiCompact_openImmersion (inferInstance : QuasiCompact f.hom.left)
  let := d.quasiCompact_openImmersion (inferInstance : QuasiCompact f.hom.left)
  exact congrArg (fun t ↦
      (lowerStar (ModuleCat.{u + 1} A) d.g).rightDerivedFunctor.map
        ((openImmersionLowerShriek (ModuleCat.{u + 1} A) d.i).mapDerivedCategory.map t ≫
          (properOpenMate A c.i (𝟙 X.obj.left) r.hom d.i
            (r.i_hom.trans (Category.id_comp d.i).symm)).app M) ≫
        (conjugateIsoEquiv
          ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) d.g).comp
            (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) r.hom))
          (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) (r.hom ≫ d.g))
          (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) r.hom d.g)).hom.app
            ((openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapDerivedCategory.obj M) ≫
          (indexIso (fun q : c.Z ⟶ Y.obj.left ↦
            (lowerStar (ModuleCat.{u + 1} A) q).rightDerivedFunctor) r.hom_g).hom.app
            ((openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapDerivedCategory.obj M))
    (ordinary_identity_inv D A X M)

private theorem mateIsoTransport
    {C D : Type*} [Category C] [Category D] {F G : C ⥤ D}
    (γ : F ⟶ G) {K M : C} (a : K ≅ M) (b : F.obj K ≅ G.obj K)
    (hb : b.hom = γ.app K) :
    (F.mapIso a.symm ≪≫ b ≪≫ G.mapIso a).hom = γ.app M := by
  simpa only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, hb] using mateTransport γ a

private theorem witness_normalization
    (A : Type (u + 1)) [CommRing A] [Finite A]
    [TopologicalSpace A] [DiscreteTopology A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f]
    {c d : Compactification f} (r : c.Refinement d)
    (O : EtaleOriginDerivedCategory X A) :
    (refinementProperOpenIso A r O).hom =
      (purityRefinementMate A r).app (refinementFixedObject X A O) := by
  let := c.quasiCompact_openImmersion (inferInstance : QuasiCompact f)
  let := d.quasiCompact_openImmersion (inferInstance : QuasiCompact f)
  have hs := (refinementMate_eq_siteWord A r O.2.L).trans
    (refinementSiteWord_eq A r O.2.L)
  exact mateIsoTransport (purityRefinementMate A r) (refinementFixedWitnessIso X A O)
    (properOpenProEtaleIso A r.hom c.i d.i r.i_hom O.2.L) hs.symm

attribute [local irreducible] DerivedCategory refinementFixedObject
  refinementProperOpenIso refinementComparisonAtWitness finiteDirectImageComposition

private theorem normalize_iso_word
    {C C₁ C₂ T : Type*} [Category C] [Category C₁] [Category C₂] [Category T]
    {J : C ⥤ C₁} {H : C ⥤ C₂} {R : C₁ ⥤ C₂}
    {P P' : C₁ ⥤ T} {Q : C₂ ⥤ T}
    (α : P ≅ P') (β : P' ≅ R ⋙ Q) (Γ : H ⟶ J ⋙ R)
    {κ : R ⋙ Q ⟶ P'} {η : P' ⟶ P} (hβ : β.inv = κ) (hα : α.inv = η)
    (M : C) (χ : H.obj M ≅ R.obj (J.obj M)) (hχ : χ.hom = Γ.app M) :
    (α.app (J.obj M) ≪≫ β.app (J.obj M) ≪≫ Q.mapIso χ.symm).inv =
      Q.map (Γ.app M) ≫ κ.app (J.obj M) ≫ η.app (J.obj M) := by
  simp only [Iso.trans_inv, Iso.app_inv, Functor.mapIso_inv, Iso.symm_inv,
    hχ, hβ, hα, Category.assoc]

/-- The inverse of the origin-witness refinement arrow is the ambient mate comparison.
Source: latest blueprint, fix-prop-projection-formula.proof.md, refinement sentence;
lem-sf-finite-refinement-projection-realization step 2; Stacks Tags 0F7B and 0F7G.
(blueprint: lem-sf-finite-refinement-ambient-normalization).

Proof: the bounded-below mate compatibility and finite clopen site-transport equation
identify the normalized ambient mate on an etale comparison input with the etale
proper/open word. The identity direct-image comparison cancels the inserted identity.
The refinement clause of proper/open interchange identifies this word with the specified
properOpenProEtaleIso. Include through the canonical D-plus comparisons and transport
along refinementFixedWitnessIso using naturality. This identifies refinementProperOpenIso
with the ambient normalized mate. The inverse finiteDirectImageComposition is the
right-adjoint conjugate of leftDerivedUpperStarComp: derive the ordinary conjugacy
and compare the exact-map-derived and K-flat-derived adjunctions using their localization
factorizations. Finally invert the three factors of refinementComparisonAtWitness and
use equality induction to identify inverse transport with indexIso for r.hom_g. These
are exactly the three factors of finiteComparison. This calculation precedes tensoring
and uses no operation datum, intrinsic coefficient equivalence or projection map.
Identity refinements, empty schemes and the zero ring obey the same equations. -/
theorem refinementComparisonAtWitness_inv_eq
    (D : FiniteFieldDatum.{u}) (A : Type (u + 1)) [CommRing A] [Finite A]
    [TopologicalSpace A] [DiscreteTopology A]
    {X Y : Spaces D} {f : X ⟶ Y} [QuasiCompact f.hom.left]
    {c d : Compactification f.hom.left} (r : c.Refinement d)
    (O : EtaleOriginDerivedCategory X.obj.left A) :
    (refinementComparisonAtWitness A r O).inv =
      RefinementProjection.finiteComparison D A r
        (refinementFixedObject X.obj.left A O) := by
  unfold refinementComparisonAtWitness
  exact (normalize_iso_word
    (J := (openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapDerivedCategory)
    (H := (openImmersionLowerShriek (ModuleCat.{u + 1} A) d.i).mapDerivedCategory)
    (R := (lowerStar (ModuleCat.{u + 1} A) r.hom).rightDerivedFunctor)
    (P := (lowerStar (ModuleCat.{u + 1} A) c.g).rightDerivedFunctor)
    (P' := (lowerStar (ModuleCat.{u + 1} A) (r.hom ≫ d.g)).rightDerivedFunctor)
    (Q := (lowerStar (ModuleCat.{u + 1} A) d.g).rightDerivedFunctor)
    (eqToIso (congrArg (fun q : c.Z ⟶ Y.obj.left ↦
      (lowerStar (ModuleCat.{u + 1} A) q).rightDerivedFunctor) r.hom_g.symm))
    (finiteDirectImageComposition A r.hom d.g) (purityRefinementMate A r)
    (derived_compositor_conjugate_iso A r.hom d.g)
    (inverse_indexIso (fun q : c.Z ⟶ Y.obj.left ↦
      (lowerStar (ModuleCat.{u + 1} A) q).rightDerivedFunctor) r.hom_g)
    (refinementFixedObject X.obj.left A O) (refinementProperOpenIso A r O)
    (witness_normalization A r O)).trans
      (finiteComparison_word D A r (refinementFixedObject X.obj.left A O)).symm

end WeilConjectures.CompactSupportFiniteProjection
