/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q04
-/
module

public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Sheaf.AlgebraicGeometry.ProEtaleFiniteModules
public import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
public import Sheaf.AlgebraicGeometry.CompactSupportComparisonUnit
public import Sheaf.AlgebraicGeometry.ComparisonDerivedPullbackFixed
public import Sheaf.AlgebraicGeometry.EtaleClosedAmbientAdjoint
public import Sheaf.AlgebraicGeometry.FixedFiniteExceptionalAt
public import Sheaf.AlgebraicGeometry.SpecifiedExceptionalClassHom
public import Sheaf.AlgebraicGeometry.FixedEtaleOriginWitness
public import Sheaf.AlgebraicGeometry.CanonicalCompactSupportSiteComparison
public import Sheaf.AlgebraicGeometry.FixedComparisonDirectImageMate
import Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison

/-! # The closed identity-open exceptional Hom chain

Source: main-20261015 blueprint, thm-sf-ambient-adjoint-class.proof.md, displayed
four-factor Hom chain at (id_Z,i)
(blueprint: lem-coef-closed-identity-open-hom-normalization).

The identity-open identifications below are constructed by adjunction uniqueness and
termwise descent. The property retains the actual comparison maps and Hom bijection.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory
open scoped CategoryTheory.Functor

private lemma homEquiv_change_left
    {C D : Type*} [Category C] [Category D]
    {Fc F : C ⥤ D} {Ic I : D ⥤ C} (a : Fc ⊣ Ic) (b : F ⊣ I)
    (e : Fc ≅ F) {X : C} {Y : D} (f : Fc.obj X ⟶ Y) :
    a.homEquiv X Y f ≫ ((a.ofNatIsoLeft e).rightAdjointUniq b).hom.app Y =
      b.homEquiv X Y (e.inv.app X ≫ f) := by
  have h (g : F.obj X ⟶ Y) :
      (a.ofNatIsoLeft e).homEquiv X Y g ≫
          ((a.ofNatIsoLeft e).rightAdjointUniq b).hom.app Y = b.homEquiv X Y g := by
    simp only [Adjunction.homEquiv_unit, Category.assoc]
    rw [((a.ofNatIsoLeft e).rightAdjointUniq b).hom.naturality g,
      ← Category.assoc, Adjunction.unit_rightAdjointUniq_hom_app]
  simpa only [Adjunction.homEquiv_ofNatIsoLeft_apply,
    Iso.hom_inv_id_app_assoc] using h (e.inv.app X ≫ f)

private lemma homEquiv_cancel_left
    {C D : Type*} [Category C] [Category D]
    {S : C ⥤ D} {U : D ⥤ C} (a : S ⊣ U)
    {X Y : C} (e : X ≅ Y) {M : D} (f : S.obj Y ⟶ M) :
    e.inv ≫ a.homEquiv X M (S.map e.hom ≫ f) = a.homEquiv Y M f := by
  rw [Adjunction.homEquiv_naturality_left, Iso.inv_hom_id_assoc]

open CategoryTheory.Limits
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private lemma derive_identity_square
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (S : C ⥤ D) (E : C ⥤ C) (P : D ⥤ D)
    [S.Additive] [E.Additive] [P.Additive]
    [PreservesFiniteLimits S] [PreservesFiniteColimits S]
    [PreservesFiniteLimits E] [PreservesFiniteColimits E]
    [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    (o : E ⋙ S ≅ S ⋙ P) (e : E ≅ 𝟭 C) (p : P ≅ 𝟭 D)
    (h : o ≪≫ Functor.isoWhiskerLeft S p = Functor.isoWhiskerRight e S) :
    (Functor.mapDerivedCategoryCompIso E S).inv ≫
      (Functor.mapDerivedCategoryNatIso o).hom ≫
      (Functor.mapDerivedCategoryCompIso S P).hom ≫
      Functor.whiskerLeft S.mapDerivedCategory
        (Functor.mapDerivedCategoryNatIso p ≪≫ Functor.mapDerivedCategoryIdIso D).hom =
    Functor.whiskerRight
      (Functor.mapDerivedCategoryNatIso e ≪≫ Functor.mapDerivedCategoryIdIso C).hom
        S.mapDerivedCategory := by
  simp only [Iso.trans_hom, Functor.whiskerLeft_comp, Functor.whiskerRight_comp]
  have hd := congrArg (fun z ↦ (Functor.mapDerivedCategoryNatIso z).hom) h
  rw [Functor.mapDerivedCategoryNatIso_trans] at hd
  rw [← cancel_epi (Functor.mapDerivedCategoryCompIso E S).hom]
  simp only [Iso.hom_inv_id_assoc]
  rw [← reassoc_of% (Functor.mapDerivedCategoryNatIso_isoWhiskerLeft S p),
    Functor.mapDerivedCategoryCompIso_comp_id S]
  rw [← reassoc_of% (Functor.mapDerivedCategoryNatIso_isoWhiskerRight e S),
    Functor.mapDerivedCategoryCompIso_id_comp S]
  simpa only [Category.assoc, Iso.trans_hom, NatTrans.comp_app,
    Functor.whiskerLeft_comp, Functor.whiskerRight_comp] using
      congrArg (· ≫ 𝟙 S.mapDerivedCategory) hd

private lemma inclusion_comp_inv
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (K : DerivedCategory.Plus C) :
    DerivedCategory.Plus.ι.map ((Functor.mapDerivedCategoryPlusCompIso F G).inv.app K) =
      (Functor.mapDerivedCategoryCompIso F G).inv.app K.obj := by
  change (DerivedCategory.Plus.ι.mapIso
    ((Functor.mapDerivedCategoryPlusCompIso F G).app K)).inv =
      ((Functor.mapDerivedCategoryCompIso F G).app K.obj).inv
  congr 1
  apply Iso.ext
  exact Functor.ι_map_mapDerivedCategoryPlusCompIso_hom_app F G K

private lemma inclusion_nat_inv
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    {F G : C ⥤ D} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (e : F ≅ G) (K : DerivedCategory.Plus C) :
    DerivedCategory.Plus.ι.map ((Functor.mapDerivedCategoryPlusNatIso e).inv.app K) =
      (Functor.mapDerivedCategoryNatIso e).inv.app K.obj := by
  change (DerivedCategory.Plus.ι.mapIso
    ((Functor.mapDerivedCategoryPlusNatIso e).app K)).inv =
      ((Functor.mapDerivedCategoryNatIso e).app K.obj).inv
  congr 1
  apply Iso.ext
  exact Functor.ι_map_mapDerivedCategoryPlusNatIso_hom_app e K

namespace AlgebraicGeometry.ProEtale

/-- Remove identity etale extension by zero using its specified adjunction.
Source: identity-open specialization of thm-sf-ambient-adjoint-class.proof.md
(blueprint: lem-coef-closed-identity-open-hom-normalization). -/
def closedIdentityOpenEtaleIso (A : Type (u + 1)) [CommRing A] [Finite A]
    {Z P : Scheme.{u}} (i : Z ⟶ P) [IsClosedImmersion i] :
    Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A)
        (Compactification.ofIsProper i) ≅
      (Etale.lowerStar (ModuleCat.{u + 1} A) i).rightDerivedFunctor :=
  Functor.isoWhiskerRight
      (Functor.mapDerivedCategoryNatIso
          (Adjunction.leftAdjointIdIso
            (Etale.openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) (𝟙 Z))
            (Etale.upperStarId (ModuleCat.{u + 1} A) Z)) ≪≫
        Functor.mapDerivedCategoryIdIso _) _ ≪≫
    Functor.leftUnitor _

/-- Remove identity pro-etale extension by zero using its specified adjunction.
Source: identity-open specialization of thm-sf-ambient-adjoint-class.proof.md
(blueprint: lem-coef-closed-identity-open-hom-normalization). -/
def closedIdentityOpenProEtaleIso (A : Type (u + 1)) [CommRing A] [Finite A]
    {Z P : Scheme.{u}} (i : Z ⟶ P) [IsClosedImmersion i] :
    rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A)
        (Compactification.ofIsProper i) ≅
      (lowerStar (ModuleCat.{u + 1} A) i).rightDerivedFunctor :=
  Functor.isoWhiskerRight
      (Functor.mapDerivedCategoryNatIso
          (Adjunction.leftAdjointIdIso
            (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) (𝟙 Z))
            (upperStarId (ModuleCat.{u + 1} A) Z)) ≪≫
        Functor.mapDerivedCategoryIdIso _) _ ≪≫
    Functor.leftUnitor _

private lemma compactSupportComparison_eq_fixed
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (compactSupportSiteComparison A c).hom.app L =
      (fixedCompactSupportComparisonIso A c).hom.app L := by
  simp only [compactSupportSiteComparison, compactSupportSiteComparisonPlus,
    fixedCompactSupportComparisonIso, fixedDirectImageComparisonIso,
    properOpenSiteExtensionIso, Iso.trans_hom, Iso.trans_inv,
    Iso.symm_hom, Iso.symm_inv, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerLeft_inv,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerRight_inv,
    Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id, Category.assoc,
    Functor.map_comp, Functor.mapDerivedCategoryPlusCompatibility,
    Etale.rightDerivedLowerShriekOfCompactificationPlusCompatibility,
    rightDerivedLowerShriekOfCompactificationPlusCompatibility]
  simp only [Iso.refl_inv, Iso.refl_hom, NatTrans.id_app, Functor.comp_map]
  let R := (lowerStar (ModuleCat.{u + 1} A) c.g)
  have hn (K K' : DerivedCategory.Plus
      (Sheaf (Scheme.ProEt.topology c.Z) (ModuleCat.{u + 1} A))) (f : K ⟶ K') :
      R.rightDerivedFunctorPlusCompatibility.inv.app K ≫
          DerivedCategory.Plus.ι.map (R.rightDerivedFunctorPlus.map f) =
        R.rightDerivedFunctor.map (DerivedCategory.Plus.ι.map f) ≫
          R.rightDerivedFunctorPlusCompatibility.inv.app K' := by
    exact (R.rightDerivedFunctorPlusCompatibility.inv.naturality f).symm
  dsimp only [Functor.mapDerivedCategoryPlus, ObjectProperty.lift,
    DerivedCategory.Plus.ι, ObjectProperty.ι, inducedFunctor, Functor.comp_obj,
    Functor.id_obj]
  simp only [Category.id_comp, Category.comp_id]
  erw [reassoc_of% (hn _ _ _), reassoc_of% (hn _ _ _), reassoc_of% (hn _ _ _)]
  simp only [inclusion_comp_inv, inclusion_nat_inv,
    Functor.ι_map_mapDerivedCategoryPlusCompIso_hom_app,
    Functor.mapDerivedCategoryNatIso_symm]
  dsimp only [DerivedCategory.Plus.ι, ObjectProperty.ι, inducedFunctor, Functor.comp_obj]
  dsimp only [R]
  simp only [(openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapDerivedCategory.map_id,
    (comparisonUpperStar (ModuleCat.{u + 1} A) c.Z).mapDerivedCategory.map_id,
    (lowerStar (ModuleCat.{u + 1} A) c.g).rightDerivedFunctor.map_id,
    (Etale.lowerStar (ModuleCat.{u + 1} A) c.g).rightDerivedFunctor.map_id,
    (comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory.map_id,
    Category.id_comp, Category.comp_id]

private lemma closedIdentityOpenComparison_fixed
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {Z P : Scheme.{u}} (i : Z ⟶ P) [IsClosedImmersion i]
    (L : DerivedCategory.Plus (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (closedIdentityOpenProEtaleIso A i).inv.app
        ((comparisonUpperStar (ModuleCat.{u + 1} A) Z).mapDerivedCategory.obj L.obj) ≫
      (fixedCompactSupportComparisonIso A (Compactification.ofIsProper i)).hom.app L ≫
      (comparisonUpperStar (ModuleCat.{u + 1} A) P).mapDerivedCategory.map
        ((closedIdentityOpenEtaleIso A i).hom.app L.obj) =
      (fixedDirectImageComparisonIso A i).inv.app L := by
  let C := ModuleCat.{u + 1} A
  let c := Compactification.ofIsProper i
  let F := (Etale.lowerStar C i).rightDerivedFunctor
  let Q := (lowerStar C i).rightDerivedFunctor
  let SZ := (comparisonUpperStar C Z).mapDerivedCategory
  let SP := (comparisonUpperStar C P).mapDerivedCategory
  let e := closedIdentityOpenEtaleIso A i
  let q := closedIdentityOpenProEtaleIso A i
  change q.inv.app (SZ.obj L.obj) ≫ (fixedCompactSupportComparisonIso A c).hom.app L ≫
    SP.map (e.hom.app L.obj) = _
  let et := Adjunction.leftAdjointIdIso
    (Etale.openImmersionLowerShriekUpperStarAdjunction C (𝟙 Z))
    (Etale.upperStarId C Z)
  let pro := Adjunction.leftAdjointIdIso
    (openImmersionLowerShriekUpperStarAdjunction C (𝟙 Z)) (upperStarId C Z)
  let od := (Functor.mapDerivedCategoryCompIso
    (Etale.openImmersionLowerShriek C (𝟙 Z)) (comparisonUpperStar C Z)).symm ≪≫
    Functor.mapDerivedCategoryNatIso
      (openImmersionLowerShriekComparisonUpperStarIso C (𝟙 Z)) ≪≫
    Functor.mapDerivedCategoryCompIso (comparisonUpperStar C Z)
      (openImmersionLowerShriek C (𝟙 Z))
  let te := Functor.mapDerivedCategoryNatIso et ≪≫ Functor.mapDerivedCategoryIdIso _
  let tp := Functor.mapDerivedCategoryNatIso pro ≪≫ Functor.mapDerivedCategoryIdIso _
  have hs : openImmersionLowerShriekComparisonUpperStarIso C (𝟙 Z) ≪≫
      Functor.isoWhiskerLeft (comparisonUpperStar C Z) pro =
      Functor.isoWhiskerRight et (comparisonUpperStar C Z) := by
    apply Iso.ext
    ext M : 2
    exact (openImmersionLowerShriekComparison_coherence A).2.2 Z M
  have hd := NatTrans.congr_app (derive_identity_square (comparisonUpperStar C Z)
    (Etale.openImmersionLowerShriek C (𝟙 Z))
    (openImmersionLowerShriek C (𝟙 Z))
    (openImmersionLowerShriekComparisonUpperStarIso C (𝟙 Z)) et pro hs) L.obj
  have hdL : od.hom.app L.obj ≫ tp.hom.app (SZ.obj L.obj) =
      SZ.map (te.hom.app L.obj) := by
    simpa only [od, tp, te, SZ, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
      Functor.whiskerLeft_app, Functor.whiskerRight_app, Category.assoc] using hd
  let teplus := Functor.mapDerivedCategoryPlusNatIso et ≪≫
    Functor.mapDerivedCategoryPlusIdIso _
  have hte : DerivedCategory.Plus.ι.map (teplus.hom.app L) = te.hom.app L.obj := by
    simp only [teplus, te, Iso.trans_hom, NatTrans.comp_app, Functor.map_comp,
      Functor.ι_map_mapDerivedCategoryPlusNatIso_hom_app,
      Functor.ι_map_mapDerivedCategoryPlusIdIso_hom_app]
    rfl
  have hb := (fixedDirectImageComparisonIso A i).inv.naturality (teplus.hom.app L)
  simp only [Functor.comp_map, hte] at hb
  have hresult : Q.map (tp.inv.app (SZ.obj L.obj)) ≫ Q.map (od.inv.app L.obj) ≫
      (fixedDirectImageComparisonIso A i).inv.app
        ((Etale.openImmersionLowerShriek C (𝟙 Z)).mapDerivedCategoryPlus.obj L) ≫
      SP.map (F.map (te.hom.app L.obj)) = (fixedDirectImageComparisonIso A i).inv.app L := by
    rw [← hb]
    have hi : tp.inv.app (SZ.obj L.obj) ≫ od.inv.app L.obj ≫
        SZ.map (te.hom.app L.obj) = 𝟙 _ := by
      rw [← hdL, Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app]
    rw [← Q.map_comp_assoc, ← Q.map_comp_assoc, Category.assoc, hi, Q.map_id,
      Category.id_comp]
    rfl
  simp only [q, e, closedIdentityOpenEtaleIso, closedIdentityOpenProEtaleIso,
    fixedCompactSupportComparisonIso, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom,
    NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerRight_inv,
    Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.leftUnitor_hom_app, Functor.leftUnitor_inv_app,
    Functor.map_comp, Functor.mapDerivedCategoryPlusCompatibility,
    Category.id_comp, Category.comp_id, Category.assoc]
  simp only [Iso.refl_inv, Iso.refl_hom, NatTrans.id_app]
  simp only [Functor.comp_map]
  dsimp only [Functor.mapDerivedCategoryPlus, ObjectProperty.lift,
    DerivedCategory.Plus.ι, ObjectProperty.ι, inducedFunctor, Functor.comp_obj,
    Functor.id_obj]
  simp only [Category.id_comp, Category.comp_id, ← Functor.map_comp]
  dsimp only [c, Compactification.ofIsProper] at *
  dsimp only [C] at *
  simp only [(comparisonUpperStar (ModuleCat.{u + 1} A) Z).mapDerivedCategory.map_id,
    (lowerStar (ModuleCat.{u + 1} A) i).rightDerivedFunctor.map_id,
    (Etale.lowerStar (ModuleCat.{u + 1} A) i).rightDerivedFunctor.map_id,
    (comparisonUpperStar (ModuleCat.{u + 1} A) P).mapDerivedCategory.map_id,
    Category.id_comp]
  simpa only [tp, od, te, Iso.trans_inv, Iso.trans_hom, Iso.symm_inv,
    Iso.symm_hom, NatTrans.comp_app, Functor.map_comp,
    Functor.mapDerivedCategoryNatIso_symm, Functor.comp_obj,
    Functor.mapDerivedCategoryPlus, ObjectProperty.lift,
    DerivedCategory.Plus.ι, ObjectProperty.ι, inducedFunctor, C, c,
    Compactification.ofIsProper, F, Q, SZ, SP, et, pro, Category.assoc] using hresult

/-- The exact assertions of the identity-open normalization, in the fixed ordinary
constant-module presentation. The scalar lift is only the site's coefficient-size
convention. All functors, units, comparisons and relative bijections are existing
specified constructions; the two right adjoints are identified by the counit-compatible
adjunction comparison. Source: displayed chain in thm-sf-ambient-adjoint-class.proof.md
(blueprint: lem-coef-closed-identity-open-hom-normalization). -/
def closedIdentityOpenHomNormalizationProperty
    (D : WeilConjectures.FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (n : ℕ) (hn : 1 ≤ n) {Z P : Scheme.{u}}
    (aZ : Z ⟶ Spec (.of D.k)) (aP : P ⟶ Spec (.of D.k))
    [LocallyOfFiniteType aZ] [QuasiCompact aZ] [IsSeparated aZ]
    [LocallyOfFiniteType aP] [QuasiCompact aP] [IsSeparated aP]
    (i : Z ⟶ P) [IsClosedImmersion i] : Prop :=
  let A := ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)
  letI : Finite (Padic.coefficientExtensionRing l E n) :=
    Padic.finite_coefficientExtensionRing l E n hn
  letI : Finite A := inferInstance
  letI : CompactSpace P := QuasiCompact.compactSpace_of_compactSpace aP
  let c := Compactification.ofIsProper i
  let C := ModuleCat.{u + 1} A
  let F := (Etale.lowerStar C i).rightDerivedFunctor
  let Q := (lowerStar C i).rightDerivedFunctor
  let I := F.rightAdjoint
  let SZ := (comparisonUpperStar C Z).mapDerivedCategory
  let SP := (comparisonUpperStar C P).mapDerivedCategory
  let UP := (comparisonLowerStar C P).rightDerivedFunctor
  let J := UP ⋙ I ⋙ SZ
  let β := Adjunction.ofIsLeftAdjoint F
  let η := (derivedComparisonAdjunction C P).unit
  let e := closedIdentityOpenEtaleIso A i
  let q := closedIdentityOpenProEtaleIso A i
  letI := Etale.isLeftAdjoint_rightDerivedLowerShriekOfCompactification A c
  let adjc := Adjunction.ofIsLeftAdjoint
    (Etale.rightDerivedLowerShriekOfCompactification C c)
  let r := (adjc.ofNatIsoLeft e).rightAdjointUniq β
  ∀ (H : DerivedCategory.Plus (Sheaf P.smallEtaleTopology C))
    (hIH : DerivedCategory.TStructure.t.plus (I.obj H.obj)),
    DerivedCategory.TStructure.t.plus (I.obj (UP.obj (SP.obj H.obj))) ∧
    IsIso (SZ.map (I.map (η.app H.obj))) ∧
    (∃ hJ : DerivedCategory.TStructure.t.plus (J.obj (SP.obj H.obj)),
      ∃ W : Scheme.FixedEtaleOriginWitness Z A ⟨J.obj (SP.obj H.obj), hJ⟩,
        W.complex = ⟨I.obj H.obj, hIH⟩ ∧
        HEq W.iso.hom (SZ.map (I.map (η.app H.obj)))) ∧
    ∀ L : DerivedCategory.Plus (Sheaf Z.smallEtaleTopology C),
      q.inv.app (SZ.obj L.obj) ≫ (compactSupportSiteComparison A c).hom.app L ≫
          SP.map (e.hom.app L.obj) = (fixedDirectImageComparisonIso A i).inv.app L ∧
      ∀ g : Q.obj (SZ.obj L.obj) ⟶ SP.obj H.obj,
        specifiedExceptionalHomEquiv A c
            ((siteComparisonDerivedPullbackPlus Z A).obj L)
            ⟨L, Iso.refl _⟩ ((siteComparisonDerivedPullbackPlus P A).obj H)
            (q.hom.app (SZ.obj L.obj) ≫ g) ≫
          SZ.map (r.hom.app (UP.obj (SP.obj H.obj))) =
        SZ.map ((β.homEquiv L.obj (UP.obj (SP.obj H.obj)))
          (η.app (F.obj L.obj) ≫
            UP.map ((fixedDirectImageComparisonIso A i).hom.app L ≫ g)))

/-- Identity-open normalization and domains of the closed exceptional Hom chain.
Source: main-20261015 blueprint, thm-sf-ambient-adjoint-class.proof.md, displayed
four-factor chain (blueprint: lem-coef-closed-identity-open-hom-normalization).

Proof:
1. The coefficient quotient is finite. The closed immersion is proper, hence qcqs;
   the identity-open compactification applies. Finite type over k gives finite
   dimension (including the empty source) and quasi-compactness of P.
2. The actual comparison unit at H is invertible. Applying I identifies IU_PS_PH
   with the assumed bounded-below IH. Applying exact S_Z gives alpha and its inverse,
   with retained antecedent IH, and proves boundedness of its target.
3. Composition coherence for the exact open comparison makes its identity-open
   component idempotent; invertibility makes it the identity. Thus the forward
   compact-support comparison is precisely the named direct-image counit mate delta,
   and the comparison in the statement is delta inverse.
4. Expand the specified relative bijection at the identity witness. Its factors are
   precomposition by delta, the comparison adjunction with formula eta followed by
   U_P on morphisms, the ordinary exceptional adjunction beta, and S_Z on morphisms.
   The counit-compatible uniqueness comparison identifies the two etale adjoints.
   The intermediate target IU_PS_PH is bounded below by step 2, and FL is bounded
   below by ordinary direct image, so full faithfulness applies. These are exactly
   the four factors of the boundary exceptional Hom transport, with no conjugation
   from the identity witness. -/
theorem closedIdentityOpenHomNormalization
    (D : WeilConjectures.FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (_hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (n : ℕ) (hn : 1 ≤ n) {Z P : Scheme.{u}}
    (aZ : Z ⟶ Spec (.of D.k)) (aP : P ⟶ Spec (.of D.k))
    [LocallyOfFiniteType aZ] [QuasiCompact aZ] [IsSeparated aZ]
    [LocallyOfFiniteType aP] [QuasiCompact aP] [IsSeparated aP]
    (i : Z ⟶ P) [IsClosedImmersion i] (_hi : i ≫ aP = aZ) :
    closedIdentityOpenHomNormalizationProperty D l E n hn aZ aP i := by
  let A := ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)
  let : Finite (Padic.coefficientExtensionRing l E n) :=
    Padic.finite_coefficientExtensionRing l E n hn
  let : Finite A := inferInstance
  let : CompactSpace P := QuasiCompact.compactSpace_of_compactSpace aP
  let C := ModuleCat.{u + 1} A
  let c := Compactification.ofIsProper i
  let F := (Etale.lowerStar C i).rightDerivedFunctor
  let Q := (lowerStar C i).rightDerivedFunctor
  let I := F.rightAdjoint
  let SZ := (comparisonUpperStar C Z).mapDerivedCategory
  let SP := (comparisonUpperStar C P).mapDerivedCategory
  let UP := (comparisonLowerStar C P).rightDerivedFunctor
  let J := UP ⋙ I ⋙ SZ
  let β := Adjunction.ofIsLeftAdjoint F
  let η := (derivedComparisonAdjunction C P).unit
  let e := closedIdentityOpenEtaleIso A i
  let q := closedIdentityOpenProEtaleIso A i
  let := Etale.isLeftAdjoint_rightDerivedLowerShriekOfCompactification A c
  let adjc := Adjunction.ofIsLeftAdjoint
    (Etale.rightDerivedLowerShriekOfCompactification C c)
  let r := (adjc.ofNatIsoLeft e).rightAdjointUniq β
  change ∀ H hIH, _
  intro H hIH
  have : IsIso (η.app H.obj) :=
    isIso_derivedComparisonAdjunction_unit_app C P H.obj H.property
  have hIU : DerivedCategory.TStructure.t.plus (I.obj (UP.obj (SP.obj H.obj))) :=
    DerivedCategory.TStructure.t.plus.prop_of_iso (I.mapIso (asIso (η.app H.obj))) hIH
  have hsource : DerivedCategory.TStructure.t.plus (SZ.obj (I.obj H.obj)) :=
    DerivedCategory.plusEtaleOrigin.plus
      (DerivedCategory.plusEtaleOrigin_mapDerivedCategory_obj hIH)
  have hJ : DerivedCategory.TStructure.t.plus (J.obj (SP.obj H.obj)) :=
    DerivedCategory.TStructure.t.plus.prop_of_iso
      (SZ.mapIso (I.mapIso (asIso (η.app H.obj)))) hsource
  refine ⟨hIU, inferInstance, ?_, ?_⟩
  · refine ⟨hJ, ⟨⟨I.obj H.obj, hIH⟩, SZ.mapIso (I.mapIso (asIso (η.app H.obj)))⟩,
      rfl, ?_⟩
    rfl
  · intro L
    have hcanonical :
        (compactSupportSiteComparison A c).hom.app L =
          (fixedCompactSupportComparisonIso A c).hom.app L := by
      exact compactSupportComparison_eq_fixed A c L
    have hfixed : q.inv.app (SZ.obj L.obj) ≫
        (fixedCompactSupportComparisonIso A c).hom.app L ≫
          SP.map (e.hom.app L.obj) = (fixedDirectImageComparisonIso A i).inv.app L := by
      exact closedIdentityOpenComparison_fixed A i L
    refine ⟨by rw [hcanonical]; exact hfixed, ?_⟩
    intro g
    have hb : (fixedCompactSupportComparisonIso A c).inv.app L ≫
        q.hom.app (SZ.obj L.obj) =
        SP.map (e.hom.app L.obj) ≫ (fixedDirectImageComparisonIso A i).hom.app L := by
      apply (cancel_epi ((fixedCompactSupportComparisonIso A c).hom.app L)).mp
      apply (cancel_epi (q.inv.app (SZ.obj L.obj))).mp
      simp only [Iso.hom_inv_id_app_assoc]
      simpa only [Category.assoc, Iso.inv_hom_id_app, Functor.comp_obj,
        DerivedCategory.Plus.ι, ObjectProperty.ι, inducedFunctor, SZ] using
        congrArg (· ≫ (fixedDirectImageComparisonIso A i).hom.app L) hfixed.symm
    simp only [specifiedExceptionalHomEquiv, Equiv.trans_apply, Iso.homFromEquiv,
      Equiv.ofBijective_apply, Functor.mapIso_refl, Iso.symm_inv, Iso.refl_hom,
      Iso.refl_inv, Category.id_comp]
    dsimp only [Equiv.coe_fn_mk, siteComparisonDerivedPullbackPlus,
      Functor.mapDerivedCategoryPlus, ObjectProperty.lift, DerivedCategory.Plus.ι,
      ObjectProperty.ι, inducedFunctor, Functor.comp_obj, Functor.id_obj]
    simp only [Category.id_comp]
    change SZ.map (adjc.homEquiv L.obj _
        ((derivedComparisonAdjunction C P).homEquiv _ _
          ((fixedCompactSupportComparisonIso A c).inv.app L ≫
            q.hom.app (SZ.obj L.obj) ≫ g))) ≫ SZ.map (r.hom.app _) = _
    rw [← SZ.map_comp]
    rw [homEquiv_change_left]
    congr 1
    rw [← Category.assoc, hb]
    rw [Category.assoc]
    have heq := homEquiv_cancel_left (derivedComparisonAdjunction C P)
      (e.app L.obj) ((fixedDirectImageComparisonIso A i).hom.app L ≫ g)
    exact congrArg (β.homEquiv L.obj _) heq

end AlgebraicGeometry.ProEtale
