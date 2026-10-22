/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups NY and Q86
-/
module

public import Sheaf.AlgebraicGeometry.NormalizedSupportTriangle
public import Sheaf.AlgebraicGeometry.SupportLongExact
public import Sheaf.AlgebraicGeometry.ProEtaleSupportedExteriorProduct
public import Sheaf.AlgebraicGeometry.ComparisonGlobalCohomologyFiniteNormalized
public import Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Monoidal
public import WeilConjectures.SixFunctors.ProEtale.Comparison.Flat
public import WeilConjectures.SixFunctors.ProEtale.Comparison.Monoidal
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusBaseChange
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated

import all Sheaf.AlgebraicGeometry.SupportedCoefficientDerivedOpenMate
import all Sheaf.AlgebraicGeometry.SupportedCoefficientOpenMateQuotient
import all Sheaf.AlgebraicGeometry.ProEtaleSupportedExteriorProduct
import all Sheaf.AlgebraicGeometry.SupportedExteriorProduct
import all Sheaf.AlgebraicGeometry.SupportedProductLocalization
import all Sheaf.AlgebraicGeometry.SupportedCoefficientTensorQuotientSquare
import all Sheaf.AlgebraicGeometry.SupportedCoefficientOpenTensor
import all Sheaf.AlgebraicGeometry.ProEtaleSupportedProductNaturality
import all Sheaf.AlgebraicGeometry.SupportQuotientPairPullback
import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
import WeilConjectures.SixFunctors.ProEtale.Comparison.CohomologicalDimension
import Sheaf.AlgebraicGeometry.CompactSupportComparisonUnit
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback
import WeilConjectures.SixFunctors.ProEtale.BaseChange.WeaklyEtale
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.ClosedImmersion
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Conservative
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Restriction

/-!
# Comparison of ordinary supported sections between the two sites

Source: Stacks Project, Tags 099W, 099V, 09B1 and 09XP, with the supported
refinement of blueprint `lem-pur-support-site-comparison`
(blueprint: lem-pur-support-site-comparison).

## Main definitions and statements

* `ProEtale.supportComparison`: the natural bounded-below comparison map.
* `ProEtale.supportComparison_isIso`: invertibility under the node's hypotheses.
* `ProEtale.supportComparison_forget`, `ProEtale.fullSupportForget_isIso`, and
  `ProEtale.supportComparison_open`: forgetting, full-support normalization, and restriction.
* `ProEtale.supportExteriorCoefficientIso`: the specified tensor/pullback comparison theta.
* `ProEtale.supportComparison_exterior`: equality of the supported exterior-product maps.
-/

@[expose] public section

set_option autoImplicit false

universe u u₁ u₂ u₃ v₁ v₂ v₃ w₁ w₂ w₃

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale

variable (A : Type (u + 1)) [CommRing A]
  {Z T : Scheme.{u}} (i : Z ⟶ T) [IsClosedImmersion i]

/-- The etale support kernel used by the canonical comparison unit.
Source: blueprint proof paragraph 1 (blueprint: lem-pur-support-site-comparison). -/
noncomputable abbrev etaleSupportKernel :=
  Sheaf.supportedSectionsFunctor T.smallEtaleTopology (ModuleCat.{u + 1} A)
    (Etale.supportRestrictionArrow i)

/-- The support comparison unit is uniquely normalized by the adjunction-unit
map on sections and the kernel inclusion.
Source: blueprint proof paragraph 1 (blueprint: lem-pur-support-site-comparison).
Proof: sections identify with evaluation at the final object.  The comparison
adjunction unit commutes with restriction, so it maps the etale support kernel
into the pro-etale kernel.  The kernel universal property gives the map and its
inclusion equation gives uniqueness. -/
theorem supportComparisonUnit_existsUnique :
    ∃! c : etaleSupportKernel A i ⟶
      comparisonUpperStar (ModuleCat.{u + 1} A) T ⋙ supportSections i A,
      ∀ F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A),
        c.app F ≫ kernel.ι
          (((comparisonUpperStar (ModuleCat.{u + 1} A) T).obj F).obj.map
            (supportRestrictionArrow i).op) =
        (Sheaf.supportedSectionsInclusion T.smallEtaleTopology
          (ModuleCat.{u + 1} A) (Etale.supportRestrictionArrow i)).app F ≫
          (((comparisonAdjunction (ModuleCat.{u + 1} A) T).unit.app F).hom.app
            (op (Scheme.Etale.mk (𝟙 T)))) := by
  let c : etaleSupportKernel A i ⟶
      comparisonUpperStar (ModuleCat.{u + 1} A) T ⋙ supportSections i A :=
    { app := fun F ↦ (etaleSupportKernel A i).map
        ((comparisonAdjunction (ModuleCat.{u + 1} A) T).unit.app F)
      naturality := by
        intro F G f
        change (etaleSupportKernel A i).map f ≫
            (etaleSupportKernel A i).map
              ((comparisonAdjunction (ModuleCat.{u + 1} A) T).unit.app G) =
          (etaleSupportKernel A i).map
              ((comparisonAdjunction (ModuleCat.{u + 1} A) T).unit.app F) ≫
            (etaleSupportKernel A i).map
              ((comparisonLowerStar (ModuleCat.{u + 1} A) T).map
                ((comparisonUpperStar (ModuleCat.{u + 1} A) T).map f))
        rw [← Functor.map_comp, ← Functor.map_comp]
        exact congrArg (etaleSupportKernel A i).map
          ((comparisonAdjunction (ModuleCat.{u + 1} A) T).unit.naturality f) }
  refine ⟨c, ?_, ?_⟩
  · intro F
    exact kernel.lift_ι _ _ _
  · intro c' hc'
    apply NatTrans.ext
    funext F
    apply (cancel_mono (kernel.ι
      (((comparisonUpperStar (ModuleCat.{u + 1} A) T).obj F).obj.map
        (supportRestrictionArrow i).op))).mp
    exact (hc' F).trans (kernel.lift_ι _ _ _).symm

/-- The canonical ordinary support comparison unit.
Source: blueprint proof paragraph 1 (blueprint: lem-pur-support-site-comparison). -/
noncomputable def supportComparisonUnit :=
  Classical.choose (supportComparisonUnit_existsUnique A i)

/-- The canonical bounded-below derived support comparison induced by the unit.
Source: blueprint proof paragraph 1 (blueprint: lem-pur-support-site-comparison).
Proof: apply the right-derived-functor-plus base-change construction to the
unit-normalized ordinary support map, inserting the canonical identity
unitors and the derived-category-plus identity comparison. -/
noncomputable def supportComparison :
    (etaleSupportKernel A i).rightDerivedFunctorPlus ⟶
      (comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategoryPlus ⋙
        (supportSections i A).rightDerivedFunctorPlus :=
  (Functor.rightUnitor _).inv ≫
    (Functor.isoWhiskerLeft _ (Functor.mapDerivedCategoryPlusIdIso
      (ModuleCat.{u + 1} A))).inv ≫
    Functor.rightDerivedFunctorPlusBaseChange
      (G := etaleSupportKernel A i) (G' := supportSections i A)
      (β := comparisonUpperStar (ModuleCat.{u + 1} A) T)
      (γ := 𝟭 (ModuleCat.{u + 1} A))
      ((Functor.rightUnitor _).hom ≫ supportComparisonUnit A i)

section SupportDerivedNormalization

variable {C : Type u₁} {D : Type u₂} {E : Type u₃}
  [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E]
  [Abelian C] [Abelian D] [Abelian E]
  [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
  [EnoughInjectives C] [EnoughInjectives D]
  {L : C ⥤ D} {G : C ⥤ E} {H : D ⥤ E}
  [L.Additive] [G.Additive] [H.Additive]
  [PreservesFiniteLimits L] [PreservesFiniteColimits L]

private noncomputable def normalizedBaseChange (e : G ⟶ L ⋙ H) :
    G.rightDerivedFunctorPlus ⟶ L.mapDerivedCategoryPlus ⋙ H.rightDerivedFunctorPlus :=
  (Functor.rightUnitor _).inv ≫
    (Functor.isoWhiskerLeft _ (Functor.mapDerivedCategoryPlusIdIso E)).inv ≫
    Functor.rightDerivedFunctorPlusBaseChange
      (G := G) (G' := H) (β := L) (γ := 𝟭 E) ((Functor.rightUnitor G).hom ≫ e)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types true in
set_option backward.defeqAttrib.useBackward true in
private lemma normalizedBaseChange_fac (e : G ⟶ L ⋙ H) (K : HomotopyCategory.Plus C) :
    G.rightDerivedFunctorPlusUnit.app K ≫
      (normalizedBaseChange e).app (DerivedCategory.Plus.Qh.obj K) =
    DerivedCategory.Plus.Qh.map ((NatTrans.mapHomotopyCategoryPlus e).app K) ≫
      H.rightDerivedFunctorPlusUnit.app (L.mapHomotopyCategoryPlus.obj K) ≫
      H.rightDerivedFunctorPlus.map (L.mapDerivedCategoryPlusFactorsh.inv.app K) := by
  simp only [normalizedBaseChange, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.isoWhiskerLeft_inv, Functor.rightUnitor_inv_app, Category.id_comp]
  have hi := (Functor.mapDerivedCategoryPlusIdIso E).inv.naturality
    (G.rightDerivedFunctorPlusUnit.app K)
  simp only [Functor.id_map] at hi
  rw [reassoc_of% hi]
  have hfac := NatTrans.congr_app (Functor.rightDerivedFunctorPlusBaseChange_fac
    (G := G) (G' := H) (β := L) (γ := 𝟭 E)
    ((Functor.rightUnitor G).hom ≫ e)) K
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Category.comp_id] at hfac
  rw [hfac]
  simp only [Functor.rightDerivedFunctorPlusBaseChangeAux, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.mapHomotopyCategoryPlusCompIso_refl_hom_app,
    Functor.mapHomotopyCategoryPlusCompIso_refl_inv_app,
    CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
  rw [← Functor.mapDerivedCategoryPlusIdIso_hom_app_factorsh]
  simp only [Iso.inv_hom_id_app_assoc]
  have hu : (Functor.rightUnitor G).hom ≫ e = e := by
    ext X
    exact Category.id_comp _
  rw [hu]
  erw [Category.id_comp, Category.id_comp]

variable (R : D ⥤ C) [R.Additive] [R.PreservesInjectiveObjects] (adj : L ⊣ R)

omit [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    [EnoughInjectives C] [EnoughInjectives D]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [R.PreservesInjectiveObjects] in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types true in
set_option backward.defeqAttrib.useBackward true in
private theorem liftedUnit (K : HomotopyCategory.Plus C) :
    (NatTrans.mapHomotopyCategoryPlus
      (Functor.whiskerRight adj.unit G)).app K =
    G.mapHomotopyCategoryPlus.map (adj.mapHomotopyCategoryPlus.unit.app K) := by
  apply (HomotopyCategory.Plus.ι E).map_injective
  change (NatTrans.mapHomotopyCategory
      (Functor.whiskerRight adj.unit G)
      (ComplexShape.up ℤ)).app K.obj =
    (G.mapHomotopyCategory (ComplexShape.up ℤ)).map
      ((HomotopyCategory.Plus.ι C).map (adj.mapHomotopyCategoryPlus.unit.app K))
  rw [Adjunction.ι_map_mapHomotopyCategoryPlus_unit_app]
  have hη (Y : HomotopyCategory C (ComplexShape.up ℤ)) :
      (NatTrans.mapHomotopyCategory
        (Functor.whiskerRight adj.unit G)
        (ComplexShape.up ℤ)).app Y =
      (G.mapHomotopyCategory (ComplexShape.up ℤ)).map
        ((adj.mapHomotopyCategory (ComplexShape.up ℤ)).unit.app Y) := by
    obtain ⟨X, rfl⟩ := HomotopyCategory.quotient_obj_surjective Y
    rw [Adjunction.mapHomotopyCategory_unit_app_quotient]
    simp only [NatTrans.mapHomotopyCategory_app, Functor.mapHomotopyCategory_map]
    congr 1
  exact hη K.obj

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types true in
set_option backward.defeqAttrib.useBackward true in
private theorem supportBaseChange_unit :
    normalizedBaseChange (G := G) (L := L) (H := R ⋙ G) (Functor.whiskerRight adj.unit G) ≫
      Functor.whiskerLeft L.mapDerivedCategoryPlus
        (Functor.rightDerivedFunctorPlusCompIso R G).hom =
    Functor.whiskerRight adj.derivedPlus.unit G.rightDerivedFunctorPlus := by
  refine Functor.rightDerived_ext G.rightDerivedFunctorPlus
    G.rightDerivedFunctorPlusUnit (HomotopyCategory.Plus.quasiIso C) _ _ _ ?_
  ext K : 2
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
  rw [← Category.assoc, normalizedBaseChange_fac]
  simp only [Category.assoc]
  erw [(Functor.rightDerivedFunctorPlusCompIso R G).hom.naturality]
  rw [Functor.rightDerivedFunctorPlusCompIso_fac_app_assoc,
    Functor.rightDerivedFunctorPlusCompUnit_app]
  rw [liftedUnit]
  have hn := G.rightDerivedFunctorPlusUnit.naturality
    (adj.mapHomotopyCategoryPlus.unit.app K)
  simp only [Functor.comp_map] at hn
  rw [Category.assoc, reassoc_of% hn]
  simp only [Functor.comp_map]
  rw [← G.rightDerivedFunctorPlus.map_comp_assoc,
    ← G.rightDerivedFunctorPlus.map_comp]
  rw [← adj.derivedPlus_unit_app_fac]
  simp only [Category.assoc, ← CategoryTheory.Functor.map_comp, Iso.hom_inv_id_app]
  erw [CategoryTheory.Functor.map_id, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types true in
set_option backward.defeqAttrib.useBackward true in
private theorem normalizedBaseChange_naturality
    {G₂ : C ⥤ E} {H₂ : D ⥤ E} [G₂.Additive] [H₂.Additive]
    (e : G ⟶ L ⋙ H) (e₂ : G₂ ⟶ L ⋙ H₂) (a : G ⟶ G₂) (b : H ⟶ H₂)
    (h : e ≫ Functor.whiskerLeft L b = a ≫ e₂) :
    normalizedBaseChange e ≫
        Functor.whiskerLeft L.mapDerivedCategoryPlus
          (Functor.rightDerivedFunctorPlusNatTrans b) =
      Functor.rightDerivedFunctorPlusNatTrans a ≫ normalizedBaseChange e₂ := by
  refine Functor.rightDerived_ext G.rightDerivedFunctorPlus
    G.rightDerivedFunctorPlusUnit (HomotopyCategory.Plus.quasiIso C) _ _ _ ?_
  ext K : 2
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app]
  rw [← Category.assoc, normalizedBaseChange_fac]
  simp only [Category.assoc]
  erw [(Functor.rightDerivedFunctorPlusNatTrans b).naturality]
  rw [Functor.rightDerivedFunctorPlusNatTrans_app_assoc]
  erw [Functor.rightDerivedFunctorPlusNatTrans_app_assoc, normalizedBaseChange_fac]
  have hh := NatTrans.congr_app (congrArg NatTrans.mapHomotopyCategoryPlus h) K
  simp only [NatTrans.mapHomotopyCategoryPlus_comp, NatTrans.comp_app] at hh
  have heq : (NatTrans.mapHomotopyCategoryPlus e).app K ≫
        (NatTrans.mapHomotopyCategoryPlus b).app (L.mapHomotopyCategoryPlus.obj K) =
      (NatTrans.mapHomotopyCategoryPlus a).app K ≫
        (NatTrans.mapHomotopyCategoryPlus e₂).app K := hh
  erw [← DerivedCategory.Plus.Qh.map_comp_assoc,
    heq, CategoryTheory.Functor.map_comp, Category.assoc]

variable [Abelian.HasKInjectiveResolutions C] [Abelian.HasKInjectiveResolutions D]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types true in
set_option backward.defeqAttrib.useBackward true in
private lemma compatibility_fac (F : C ⥤ E) [F.Additive]
    (K : HomotopyCategory.Plus C) :
    DerivedCategory.Plus.ι.map (F.rightDerivedFunctorPlusUnit.app K) ≫
        F.rightDerivedFunctorPlusCompatibility.hom.app (DerivedCategory.Plus.Qh.obj K) =
      F.rightDerivedFunctorUnit.app K.obj := by
  have h := NatTrans.congr_app (Functor.rightDerivedNatTrans_fac
    (F.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι)
    (DerivedCategory.Plus.ι ⋙ F.rightDerivedFunctor)
    F.rightDerivedFunctorPlusιUnit F.ιRightDerivedFunctorUnit
    (HomotopyCategory.Plus.quasiIso C) (𝟙 _)) K
  simpa only [Functor.rightDerivedFunctorPlusCompatibility,
    Functor.rightDerivedUnique, Functor.rightDerivedNatIso_hom,
    Iso.refl_hom, ObjectProperty.ι_obj,
    Functor.rightDerivedFunctorPlusιUnit, Functor.ιRightDerivedFunctorUnit,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    NatTrans.id_app, Category.id_comp] using h

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types true in
set_option backward.defeqAttrib.useBackward true in
private theorem baseChange_compatibility (e : G ⟶ L ⋙ H)
    (α : G.rightDerivedFunctor ⟶ L.mapDerivedCategory ⋙ H.rightDerivedFunctor)
    (hα : ∀ K : HomotopyCategory C (.up ℤ),
      G.rightDerivedFunctorUnit.app K ≫ α.app (DerivedCategory.Qh.obj K) =
        DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory e (.up ℤ)).app K) ≫
          H.rightDerivedFunctorUnit.app ((L.mapHomotopyCategory (.up ℤ)).obj K) ≫
          H.rightDerivedFunctor.map (L.mapDerivedCategoryFactorsh.inv.app K)) :
    Functor.whiskerRight (normalizedBaseChange e) DerivedCategory.Plus.ι ≫
        Functor.whiskerLeft L.mapDerivedCategoryPlus
          H.rightDerivedFunctorPlusCompatibility.hom =
      G.rightDerivedFunctorPlusCompatibility.hom ≫
        Functor.whiskerLeft DerivedCategory.Plus.ι α := by
  refine Functor.rightDerived_ext (G.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι)
    G.rightDerivedFunctorPlusιUnit (HomotopyCategory.Plus.quasiIso C) _ _ _ ?_
  ext K : 2
  simp only [Functor.rightDerivedFunctorPlusιUnit, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app]
  rw [← DerivedCategory.Plus.ι.map_comp_assoc, normalizedBaseChange_fac]
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  have hn := H.rightDerivedFunctorPlusCompatibility.hom.naturality
    (L.mapDerivedCategoryPlusFactorsh.inv.app K)
  dsimp only [Functor.comp_map] at hn
  erw [hn]
  erw [reassoc_of% compatibility_fac H, reassoc_of% compatibility_fac G, hα]
  have hf : DerivedCategory.Plus.ι.map (L.mapDerivedCategoryPlusFactorsh.inv.app K) =
      L.mapDerivedCategoryFactorsh.inv.app K.obj := by
    apply (cancel_mono (L.mapDerivedCategoryFactorsh.hom.app K.obj)).mp
    erw [← L.ι_map_mapDerivedCategoryPlusFactorsh_hom_app K,
      ← DerivedCategory.Plus.ι.map_comp, Iso.inv_hom_id_app,
      CategoryTheory.Functor.map_id]
    erw [L.ι_map_mapDerivedCategoryPlusFactorsh_hom_app K, Iso.inv_hom_id_app]
    rfl
  rw [hf]
  rfl

omit [EnoughInjectives C] [EnoughInjectives D] in
private theorem rightDerivedPullback_fac (e : G ⟶ L ⋙ H)
    (K : HomotopyCategory C (.up ℤ)) :
    G.rightDerivedFunctorUnit.app K ≫
        (Functor.rightDerivedPullback L e).app (DerivedCategory.Qh.obj K) =
      DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory e (.up ℤ)).app K) ≫
        H.rightDerivedFunctorUnit.app ((L.mapHomotopyCategory (.up ℤ)).obj K) ≫
        H.rightDerivedFunctor.map (L.mapDerivedCategoryFactorsh.inv.app K) := by
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
  exact Functor.rightDerivedPullback_fac_app L e K

private theorem baseChange_rightDerivedPullback (e : G ⟶ L ⋙ H) :
    Functor.whiskerRight (normalizedBaseChange e) DerivedCategory.Plus.ι ≫
        Functor.whiskerLeft L.mapDerivedCategoryPlus
          H.rightDerivedFunctorPlusCompatibility.hom =
      G.rightDerivedFunctorPlusCompatibility.hom ≫
        Functor.whiskerLeft DerivedCategory.Plus.ι (Functor.rightDerivedPullback L e) :=
  baseChange_compatibility e _ (rightDerivedPullback_fac e)

end SupportDerivedNormalization

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types true in
set_option backward.defeqAttrib.useBackward true in
private theorem compatibility_naturality
    {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
    [Abelian C] [Abelian D] [HasDerivedCategory C] [HasDerivedCategory D]
    [EnoughInjectives C] [Abelian.HasKInjectiveResolutions C]
    {F G : C ⥤ D} [F.Additive] [G.Additive] (τ : F ⟶ G) :
    Functor.whiskerRight (Functor.rightDerivedFunctorPlusNatTrans τ) DerivedCategory.Plus.ι ≫
      G.rightDerivedFunctorPlusCompatibility.hom =
    F.rightDerivedFunctorPlusCompatibility.hom ≫
      Functor.whiskerLeft DerivedCategory.Plus.ι (Functor.rightDerivedFunctorNatTrans τ) := by
  refine Functor.rightDerived_ext (F.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι)
    F.rightDerivedFunctorPlusιUnit (HomotopyCategory.Plus.quasiIso C) _ _ _ ?_
  ext K : 2
  simp only [Functor.rightDerivedFunctorPlusιUnit, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app]
  rw [← DerivedCategory.Plus.ι.map_comp_assoc,
    Functor.rightDerivedFunctorPlusNatTrans_app, CategoryTheory.Functor.map_comp, Category.assoc]
  have hc (H : C ⥤ D) [H.Additive] :
      DerivedCategory.Plus.ι.map (H.rightDerivedFunctorPlusUnit.app K) ≫
          H.rightDerivedFunctorPlusCompatibility.hom.app (DerivedCategory.Plus.Qh.obj K) =
        H.rightDerivedFunctorUnit.app K.obj := by
    have h := NatTrans.congr_app (Functor.rightDerivedNatTrans_fac
      (H.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι)
      (DerivedCategory.Plus.ι ⋙ H.rightDerivedFunctor)
      H.rightDerivedFunctorPlusιUnit H.ιRightDerivedFunctorUnit
      (HomotopyCategory.Plus.quasiIso C) (𝟙 _)) K
    simpa only [Functor.rightDerivedFunctorPlusCompatibility,
      Functor.rightDerivedUnique, Functor.rightDerivedNatIso_hom,
      Iso.refl_hom, ObjectProperty.ι_obj,
      Functor.rightDerivedFunctorPlusιUnit, Functor.ιRightDerivedFunctorUnit,
      NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      NatTrans.id_app, Category.id_comp] using h
  rw [hc G, reassoc_of% hc F]
  exact (Functor.rightDerivedNatTrans_app F.rightDerivedFunctor G.rightDerivedFunctor
    F.rightDerivedFunctorUnit G.rightDerivedFunctorUnit
    (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))
    (Functor.whiskerRight (NatTrans.mapHomotopyCategory τ (ComplexShape.up ℤ))
      DerivedCategory.Qh) K.obj).symm


private theorem supportRightDerived_comp
    {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
    [Abelian C] [Abelian D] [HasDerivedCategory C] [HasDerivedCategory D]
    [Abelian.HasKInjectiveResolutions C]
    {F G H : C ⥤ D} [F.Additive] [G.Additive] [H.Additive]
    (a : F ⟶ G) (b : G ⟶ H) :
    Functor.rightDerivedFunctorNatTrans (a ≫ b) =
      Functor.rightDerivedFunctorNatTrans a ≫ Functor.rightDerivedFunctorNatTrans b := by
  simp only [Functor.rightDerivedFunctorNatTrans, NatTrans.mapHomotopyCategory_comp,
    Functor.whiskerRight_comp, Functor.rightDerivedNatTrans_comp]

/-- Under finite algebraically closed field hypotheses this canonical support map
is an isomorphism.
Source: Stacks Tags 099V(2), 099W(2), 09B1(2), 09XP and blueprint
proof paragraph 1 (blueprint: lem-pur-support-site-comparison).
Proof: direct image restricts to the etale subsite, so the support kernels are
termwise the same on injective resolutions.  Exact comparison inverse image makes
its right adjoint preserve injectives, and the bounded-below comparison unit is
invertible.  The derived support map is therefore invertible. -/
theorem supportComparison_isIso (k : Type u) [Field k] [IsAlgClosed k]
    [T.Over (Spec (.of k))] [LocallyOfFiniteType (T ↘ Spec (.of k))]
    [QuasiCompact (T ↘ Spec (.of k))] [IsSeparated (T ↘ Spec (.of k))]
    [Finite A] : IsIso (supportComparison A i) := by
  let L := comparisonUpperStar (ModuleCat.{u + 1} A) T
  let R := comparisonLowerStar (ModuleCat.{u + 1} A) T
  let G := etaleSupportKernel A i
  let adj := comparisonAdjunction (ModuleCat.{u + 1} A) T
  have : R.PreservesInjectiveObjects :=
    Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms adj
  have hη := isIso_compactSupportComparisonUnit T A
  change IsIso adj.derivedAdjunctionPlus.unit at hη
  rw [adj.derivedAdjunctionPlus_eq_derivedPlus] at hη
  have : IsIso adj.derivedPlus.unit := hη
  have hu : Functor.whiskerRight adj.unit G = supportComparisonUnit A i := by
    apply (Classical.choose_spec (supportComparisonUnit_existsUnique A i)).2
    intro F
    exact kernel.lift_ι _ _ _
  have h := supportBaseChange_unit (L := L) (G := G) R adj
  have hn : supportComparison A i ≫
      Functor.whiskerLeft L.mapDerivedCategoryPlus
        (Functor.rightDerivedFunctorPlusCompIso R G).hom =
      Functor.whiskerRight adj.derivedPlus.unit G.rightDerivedFunctorPlus := by
    simpa only [normalizedBaseChange, hu, supportComparison] using h
  have : IsIso (supportComparison A i ≫
      Functor.whiskerLeft L.mapDerivedCategoryPlus
        (Functor.rightDerivedFunctorPlusCompIso R G).hom) := by
    rw [hn]
    infer_instance
  exact IsIso.of_isIso_comp_right (supportComparison A i)
    (Functor.whiskerLeft L.mapDerivedCategoryPlus
      (Functor.rightDerivedFunctorPlusCompIso R G).hom)

set_option backward.isDefEq.respectTransparency.types true in
private theorem supportEvaluation_hom (A : Type (u + 1)) [CommRing A]
    (X : Scheme.{u}) (M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    (Sheaf.ΓNatIsoSheafSections X.smallEtaleTopology (ModuleCat.{u + 1} A)
      (MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale X)).hom.app M =
      M.ΓRes (op (Scheme.Etale.mk (𝟙 X))) := by
  let adj := constantSheafΓAdj X.smallEtaleTopology (ModuleCat.{u + 1} A)
  let adj' := constantSheafAdj X.smallEtaleTopology (ModuleCat.{u + 1} A)
    (MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale X)
  have hc := Adjunction.homEquiv_symm_rightAdjointUniq_hom_app adj adj' M
  apply (adj'.homEquiv _ M).symm.injective
  change (adj'.homEquiv _ M).symm ((adj.rightAdjointUniq adj').hom.app M) = _
  rw [hc]
  apply (adj'.homEquiv _ M).injective
  rw [Equiv.apply_symm_apply]
  change (CategoryTheory.constantPresheafAdj (ModuleCat.{u + 1} A)
      (MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale X)).homEquiv _ _
    ((sheafificationAdjunction X.smallEtaleTopology (ModuleCat.{u + 1} A)).homEquiv _ _
      (adj.counit.app M)) = _
  rw [Adjunction.homEquiv_unit]
  change (𝟙 _) ≫ ((sheafificationAdjunction X.smallEtaleTopology
      (ModuleCat.{u + 1} A)).homEquiv _ _ (adj.counit.app M)).app
        (Opposite.op (Scheme.Etale.mk (𝟙 X))) =
    ((sheafificationAdjunction X.smallEtaleTopology (ModuleCat.{u + 1} A)).homEquiv _ _
      ((adj.homEquiv _ M).symm (𝟙 _))).app (Opposite.op (Scheme.Etale.mk (𝟙 X)))
  rw [Category.id_comp, adj.homEquiv_symm_id]
  rfl


set_option backward.isDefEq.respectTransparency.types true in
/-- The canonical identification of the global-section kernel with the restriction
kernel used by the support long exact sequence.
Source: blueprint proof paragraph 1 (blueprint: lem-pur-support-site-comparison).
Proof: the terminal-evaluation isomorphism identifies global restriction with
restriction from the terminal object. It induces an isomorphism of kernels.
The kernel inclusion determines its forward map and hence the isomorphism uniquely. -/
theorem supportKernelEvaluationIso_existsUnique :
    ∃! e : Etale.supportedEtaleSections A T i.openComplement ≅ etaleSupportKernel A i,
      e.hom ≫ Sheaf.supportedSectionsInclusion T.smallEtaleTopology
        (ModuleCat.{u + 1} A) (Etale.supportRestrictionArrow i) =
      Etale.supportedEtaleSectionsι A T i.openComplement ≫
        (Sheaf.ΓNatIsoSheafSections T.smallEtaleTopology (ModuleCat.{u + 1} A)
          (MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale T)).hom := by
  let r := Sheaf.natTransΓRes T.smallEtaleTopology (ModuleCat.{u + 1} A)
    (op (Scheme.Etale.mk i.openComplement.ι))
  let e := Sheaf.ΓNatIsoSheafSections T.smallEtaleTopology (ModuleCat.{u + 1} A)
    (MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale T)
  have he (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) :
      r.app F ≫ 𝟙 _ = e.hom.app F ≫ F.obj.map (Etale.supportRestrictionArrow i).op := by
    change F.ΓRes (op (Scheme.Etale.mk i.openComplement.ι)) ≫ 𝟙 _ = _
    rw [supportEvaluation_hom]
    simpa only [Category.comp_id] using
      (Sheaf.ΓRes_map F (Etale.supportRestrictionArrow i).op).symm
  let b (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) :
      (Etale.supportedEtaleSections A T i.openComplement).obj F ≅
        (etaleSupportKernel A i).obj F :=
    PreservesKernel.iso ((evaluation _ (ModuleCat.{u + 1} A)).obj F) r ≪≫
      kernel.mapIso (r.app F) (F.obj.map (Etale.supportRestrictionArrow i).op)
        (e.app F) (Iso.refl _) (he F)
  have hb (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) :
      (b F).hom ≫ kernel.ι (F.obj.map (Etale.supportRestrictionArrow i).op) =
        (Etale.supportedEtaleSectionsι A T i.openComplement).app F ≫ e.hom.app F := by
    change ((PreservesKernel.iso ((evaluation _ (ModuleCat.{u + 1} A)).obj F) r).hom ≫
      (kernel.mapIso (r.app F) (F.obj.map (Etale.supportRestrictionArrow i).op)
        (e.app F) (Iso.refl _) (he F)).hom) ≫
          kernel.ι (F.obj.map (Etale.supportRestrictionArrow i).op) = _
    rw [Category.assoc, kernel.mapIso_hom, kernel.lift_ι]
    rw [← Category.assoc, PreservesKernel.iso_hom]
    erw [kernelComparison_comp_ι]
    rfl
  let n : Etale.supportedEtaleSections A T i.openComplement ≅ etaleSupportKernel A i :=
    NatIso.ofComponents b (by
      intro F G f
      apply (cancel_mono (kernel.ι (G.obj.map (Etale.supportRestrictionArrow i).op))).mp
      change ((Etale.supportedEtaleSections A T i.openComplement).map f ≫
          (b G).hom) ≫ kernel.ι (G.obj.map (Etale.supportRestrictionArrow i).op) =
        ((b F).hom ≫ (etaleSupportKernel A i).map f) ≫
          kernel.ι (G.obj.map (Etale.supportRestrictionArrow i).op)
      rw [Category.assoc, hb]
      change (kernel r).map f ≫ (kernel.ι r).app G ≫ e.hom.app G =
        ((b F).hom ≫ kernel.map _ _ (f.hom.app (op (Scheme.Etale.mk (𝟙 T))))
          (f.hom.app (op (Scheme.Etale.mk i.openComplement.ι)))
          (f.hom.naturality (Etale.supportRestrictionArrow i).op)) ≫
            kernel.ι (G.obj.map (Etale.supportRestrictionArrow i).op)
      rw [Category.assoc, kernel.lift_ι]
      rw [← Category.assoc (b F).hom, hb]
      calc
        (kernel r).map f ≫ (kernel.ι r).app G ≫ e.hom.app G =
            (kernel.ι r).app F ≫ (Sheaf.Γ T.smallEtaleTopology
              (ModuleCat.{u + 1} A)).map f ≫ e.hom.app G := by
          rw [← Category.assoc, (kernel.ι r).naturality f, Category.assoc]
        _ = ((kernel.ι r).app F ≫ e.hom.app F) ≫
            f.hom.app (op (Scheme.Etale.mk (𝟙 T))) := by
          rw [e.hom.naturality f, Category.assoc]
          rfl)
  refine ⟨n, ?_, ?_⟩
  · apply NatTrans.ext
    funext F
    exact hb F
  · intro n' hn'
    apply Iso.ext
    apply NatTrans.ext
    funext F
    apply (cancel_mono (kernel.ι (F.obj.map (Etale.supportRestrictionArrow i).op))).mp
    exact (NatTrans.congr_app hn' F).trans (hb F).symm

/-- The uniquely kernel-normalized terminal-evaluation transport.
Source: blueprint proof paragraph 1 (blueprint: lem-pur-support-site-comparison). -/
noncomputable def supportKernelEvaluationIso :=
  Classical.choose (supportKernelEvaluationIso_existsUnique A i)

/-- The existing global-section presentation of the etale support functor.
Source: blueprint proof paragraph 1 (blueprint: lem-pur-support-site-comparison). -/
noncomputable abbrev globalEtaleSupportKernel :=
  Etale.supportedEtaleSections A T i.openComplement

/-- The bounded-below comparison viewed in unbounded `D(A)`, using the canonical
compatibility of the two right-derived-functor constructions.
Source: blueprint proof paragraph 1 (blueprint: lem-pur-support-site-comparison). -/
noncomputable def supportComparisonUnbounded
    (M : DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (globalEtaleSupportKernel A i).rightDerivedFunctor.obj M.obj ⟶
      (supportSections i A).rightDerivedFunctor.obj
        ((comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory.obj M.obj) :=
  (Functor.rightDerivedFunctorNatTrans (supportKernelEvaluationIso A i).hom).app M.obj ≫
    (etaleSupportKernel A i).rightDerivedFunctorPlusCompatibility.inv.app M ≫
    DerivedCategory.Plus.ι.map ((supportComparison A i).app M) ≫
    (supportSections i A).rightDerivedFunctorPlusCompatibility.hom.app
      ((comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategoryPlus.obj M)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types true in
set_option backward.defeqAttrib.useBackward true in
private theorem comparisonUnbounded_eq (A : Type (u + 1)) [CommRing A]
    {Z T : Scheme.{u}} (i : Z ⟶ T) [IsClosedImmersion i]
    (M : DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    supportComparisonUnbounded A i M =
      (Functor.rightDerivedFunctorNatTrans (supportKernelEvaluationIso A i).hom).app M.obj ≫
        (Functor.rightDerivedPullback
          (comparisonUpperStar (ModuleCat.{u + 1} A) T) (supportComparisonUnit A i)).app M.obj := by
  have h := NatTrans.congr_app (baseChange_rightDerivedPullback (supportComparisonUnit A i)) M
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] at h
  dsimp only [supportComparisonUnbounded]
  change _ ≫ _ ≫ DerivedCategory.Plus.ι.map
      ((normalizedBaseChange (supportComparisonUnit A i)).app M) ≫ _ = _
  rw [h, Iso.inv_hom_id_app_assoc]
  rfl

/-- The published inclusion of the ordinary etale support kernel into global sections.
Source: blueprint proof paragraph 1 (blueprint: lem-pur-support-site-comparison). -/
noncomputable abbrev etaleSupportForget := Etale.supportedEtaleSectionsι A T i.openComplement

/-- Reuse the published inclusion of pro-etale supported sections.
Source: blueprint proof paragraph 1 (blueprint: lem-pur-support-site-comparison). -/
noncomputable abbrev proEtaleSupportForget := supportedModuleSectionsι A i

/-- Terminal evaluation for etale modules, with its explicit additive functor type.
Source: blueprint full-support normalization (blueprint: lem-pur-support-site-comparison). -/
noncomputable def supportEtaleGlobalEvaluationIso (T : Scheme.{u}) :
    Sheaf.Γ T.smallEtaleTopology (ModuleCat.{u + 1} A) ≅
      sheafToPresheaf T.smallEtaleTopology (ModuleCat.{u + 1} A) ⋙
        (evaluation _ _).obj (op (Scheme.Etale.mk (𝟙 T))) :=
  Sheaf.ΓNatIsoSheafSections T.smallEtaleTopology (ModuleCat.{u + 1} A)
    (MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale T)

/-- Terminal evaluation for pro-etale modules in the same additive presentation.
Source: blueprint full-support normalization (blueprint: lem-pur-support-site-comparison). -/
noncomputable def supportProEtaleGlobalEvaluationIso (T : Scheme.{u}) :
    Sheaf.Γ (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A) ≅
      sheafToPresheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A) ⋙
        (evaluation _ _).obj (op (Scheme.ProEt.mk (𝟙 T))) :=
  Sheaf.ΓNatIsoSheafSections (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A)
    (Scheme.ProEt.isTerminalMkId T)

/-- The specified finite global comparison, in the global-sections presentation.
The only inserted maps are terminal evaluation and D+/unbounded derived compatibility.
Source: blueprint full-support normalization (blueprint: lem-pur-support-site-comparison). -/
noncomputable def supportGlobalComparison [Finite A]
    (M : DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (Sheaf.Γ T.smallEtaleTopology (ModuleCat.{u + 1} A)).rightDerivedFunctor.obj M.obj ⟶
      (Sheaf.Γ (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A)).rightDerivedFunctor.obj
        ((comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory.obj M.obj) :=
  (Functor.rightDerivedFunctorNatTrans
    (supportEtaleGlobalEvaluationIso A T).hom).app M.obj ≫
  (sheafToPresheaf T.smallEtaleTopology (ModuleCat.{u + 1} A) ⋙
    (evaluation _ _).obj (op (Scheme.Etale.mk (𝟙 T)))).rightDerivedFunctorPlusCompatibility.inv.app
      M ≫
  DerivedCategory.Plus.ι.map
    (((Functor.rightUnitor _).inv ≫
      (Functor.isoWhiskerLeft _ (Functor.mapDerivedCategoryPlusIdIso
        (ModuleCat.{u + 1} A))).inv ≫ finiteComparisonGlobalSections T A).app M) ≫
  (sheafToPresheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A) ⋙
    (evaluation _ _).obj
      (op (Scheme.ProEt.mk (𝟙 T)))).rightDerivedFunctorPlusCompatibility.hom.app
        ((comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategoryPlus.obj M) ≫
  (Functor.rightDerivedFunctorNatTrans
    (supportProEtaleGlobalEvaluationIso A T).inv).app
        ((comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory.obj M.obj)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types true in
set_option backward.defeqAttrib.useBackward true in
/-- The square for forgetting support commutes with the existing adjunction-unit
comparison of global sections.
Source: Stacks Tags 099W and 09XP; blueprint proof paragraph 1
(blueprint: lem-pur-support-site-comparison).
Proof: compose the ordinary comparison kernel map with its kernel inclusion.
Kernel functoriality gives evaluation of the ordinary comparison unit at `T`.
Apply the right-derived universal property to this commuting square; on
K-injective direct images it is literally the same square in each degree.
The terminal-evaluation transport in `supportGlobalComparison` has this normalization. -/
theorem supportComparison_forget [Finite A]
    (M : DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    supportComparisonUnbounded A i M ≫
      (Functor.rightDerivedFunctorNatTrans (proEtaleSupportForget A i)).app
        ((comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory.obj M.obj) =
    (Functor.rightDerivedFunctorNatTrans (etaleSupportForget A i)).app M.obj ≫
      supportGlobalComparison A (T := T) M := by
  let G := etaleSupportKernel A i
  let H := supportSections i A
  let L := comparisonUpperStar (ModuleCat.{u + 1} A) T
  let GE := sheafToPresheaf T.smallEtaleTopology (ModuleCat.{u + 1} A) ⋙
    (evaluation _ _).obj (op (Scheme.Etale.mk (𝟙 T)))
  let HP := sheafToPresheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A) ⋙
    (evaluation _ _).obj (op (Scheme.ProEt.mk (𝟙 T)))
  let a : G ⟶ GE := Sheaf.supportedSectionsInclusion T.smallEtaleTopology
    (ModuleCat.{u + 1} A) (Etale.supportRestrictionArrow i)
  let b : H ⟶ HP := supportedModuleSectionsToSections A i
  let e : GE ⟶ L ⋙ HP := finiteComparisonGlobalSectionsUnit T A
  have he : (Functor.rightUnitor GE).hom ≫ e = finiteComparisonGlobalSectionsUnit T A := by
    change (𝟙 GE) ≫ e = e
    exact Category.id_comp e
  have ho : supportComparisonUnit A i ≫ Functor.whiskerLeft L b = a ≫ e := by
    apply NatTrans.ext
    funext F
    exact (Classical.choose_spec (supportComparisonUnit_existsUnique A i)).1 F
  have hd := normalizedBaseChange_naturality (L := L)
    (supportComparisonUnit A i) e a b ho
  have hd' : (supportComparison A i).app M ≫
      (Functor.rightDerivedFunctorPlusNatTrans b).app (L.mapDerivedCategoryPlus.obj M) =
    (Functor.rightDerivedFunctorPlusNatTrans a).app M ≫
      (((Functor.rightUnitor GE.rightDerivedFunctorPlus).inv ≫
        (Functor.isoWhiskerLeft GE.rightDerivedFunctorPlus
          (Functor.mapDerivedCategoryPlusIdIso (ModuleCat.{u + 1} A))).inv ≫
        finiteComparisonGlobalSections T A).app M) := by
    simpa only [NatTrans.comp_app, Functor.whiskerLeft_app, normalizedBaseChange,
      he, finiteComparisonGlobalSections, supportComparison] using NatTrans.congr_app hd M
  let MP := L.mapDerivedCategoryPlus.obj M
  have hb := NatTrans.congr_app (compatibility_naturality b) MP
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app] at hb
  have ha := NatTrans.congr_app (compatibility_naturality a) M
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app] at ha
  have ha' : G.rightDerivedFunctorPlusCompatibility.inv.app M ≫
      DerivedCategory.Plus.ι.map ((Functor.rightDerivedFunctorPlusNatTrans a).app M) =
    (Functor.rightDerivedFunctorNatTrans a).app M.obj ≫
      GE.rightDerivedFunctorPlusCompatibility.inv.app M := by
    apply (cancel_mono (GE.rightDerivedFunctorPlusCompatibility.hom.app M)).mp
    simp only [Category.assoc, Iso.inv_hom_id_app]
    rw [ha]
    simp only [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]
    exact (Category.comp_id _).symm
  have heval := (Classical.choose_spec (supportKernelEvaluationIso_existsUnique A i)).1
  have hEt : Functor.rightDerivedFunctorNatTrans (supportKernelEvaluationIso A i).hom ≫
      Functor.rightDerivedFunctorNatTrans a =
    Functor.rightDerivedFunctorNatTrans (etaleSupportForget A i) ≫
      Functor.rightDerivedFunctorNatTrans (supportEtaleGlobalEvaluationIso A T).hom := by
    have hh := congrArg (fun t ↦ Functor.rightDerivedFunctorNatTrans t) heval
    simpa only [supportRightDerived_comp, supportKernelEvaluationIso,
      supportEtaleGlobalEvaluationIso] using hh
  have hPro : Functor.rightDerivedFunctorNatTrans (proEtaleSupportForget A i) =
      Functor.rightDerivedFunctorNatTrans b ≫
        Functor.rightDerivedFunctorNatTrans (supportProEtaleGlobalEvaluationIso A T).inv := by
    rw [← supportRightDerived_comp]
    rfl
  have hEtM := NatTrans.congr_app hEt M.obj
  simp only [NatTrans.comp_app] at hEtM
  dsimp only [supportComparisonUnbounded, supportGlobalComparison]
  rw [hPro, NatTrans.comp_app]
  simp only [Category.assoc]
  erw [← reassoc_of% hb]
  rw [← DerivedCategory.Plus.ι.map_comp_assoc, hd', CategoryTheory.Functor.map_comp]
  simp only [Category.assoc]
  erw [reassoc_of% ha', reassoc_of% hEtM]


/-- With full support, the forgetful maps are isomorphisms. Together with the
preceding square this states that the full-support comparison is exactly the
existing global-sections comparison induced by the adjunction unit.
Source: blueprint proof paragraph 1 (blueprint: lem-pur-support-site-comparison).
Proof: the complement of the identity immersion is empty. A module sheaf has zero
sections over the empty scheme, so each restriction kernel is its source and its
kernel inclusion is invertible. Derive these natural isomorphisms. The preceding
square identifies the full-support comparison with the specified global one. -/
theorem fullSupportForget_isIso (T : Scheme.{u}) :
    IsIso (Functor.rightDerivedFunctorNatTrans (etaleSupportForget A (𝟙 T))) ∧
      IsIso (Functor.rightDerivedFunctorNatTrans (proEtaleSupportForget A (𝟙 T))) := by
  let : IsEmpty (𝟙 T : T ⟶ T).openComplement.toScheme :=
    ⟨fun x ↦ x.property ⟨x.val, rfl⟩⟩
  let : IsEmpty (Scheme.Etale.mk (𝟙 T : T ⟶ T).openComplement.ι).left :=
    inferInstanceAs (IsEmpty (𝟙 T : T ⟶ T).openComplement.toScheme)
  let : IsEmpty (Scheme.ProEt.mk (𝟙 T : T ⟶ T).openComplement.ι).left :=
    inferInstanceAs (IsEmpty (𝟙 T : T ⟶ T).openComplement.toScheme)
  have het : IsIso (etaleSupportForget A (𝟙 T)) := by
    apply kernel.ι_of_zero
    apply NatTrans.ext
    funext F
    exact (Scheme.Etale.isTerminalSectionsOfIsEmpty F
      (Scheme.Etale.mk (𝟙 T : T ⟶ T).openComplement.ι)).isZero.eq_of_tgt _ _
  have hpro : IsIso (supportedModuleSectionsToSections A (𝟙 T)) := by
    apply (NatTrans.isIso_iff_isIso_app _).mpr
    intro F
    change IsIso (kernel.ι (F.obj.map (supportRestrictionArrow (𝟙 T)).op))
    exact kernel.ι_of_zero ((Scheme.ProEt.isTerminalSectionsOfIsEmpty F
      (Scheme.ProEt.mk (𝟙 T : T ⟶ T).openComplement.ι)).isZero.eq_of_tgt _ _)
  have : IsIso (proEtaleSupportForget A (𝟙 T)) := by
    change IsIso (supportedModuleSectionsToSections A (𝟙 T) ≫ _)
    infer_instance
  constructor <;> infer_instance

/-- Derive the recorded coefficient pullback comparison before specializing coefficients.
Source: blueprint comparison-pullback clause (blueprint: lem-pur-support-site-comparison). -/
noncomputable def supportDerivedCoefficientPullbackIso
    (D : Type v₁) [Category.{u + 1} D] [Abelian D] [IsGrothendieckAbelian.{u + 1} D]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (Etale.upperStar D f).mapDerivedCategory ⋙
        (comparisonUpperStar D X).mapDerivedCategory ≅
      (comparisonUpperStar D Y).mapDerivedCategory ⋙ (upperStar D f).mapDerivedCategory :=
  let e : Etale.upperStar D f ⋙ comparisonUpperStar D X ≅
      comparisonUpperStar D Y ⋙ upperStar D f :=
    supportSiteComparisonCoefficientPullbackIso D f
  (Functor.mapDerivedCategoryCompIso (Etale.upperStar D f)
    (comparisonUpperStar D X)).symm ≪≫
  Functor.mapDerivedCategoryNatIso e ≪≫
  Functor.mapDerivedCategoryCompIso (comparisonUpperStar D Y) (upperStar D f)

/-- Exact coefficient pullback comparison on unbounded derived categories, formed
from the recorded, unit-normalized comparison-pullback isomorphism.
Source: blueprint comparison-pullback clause (blueprint: lem-pur-support-site-comparison). -/
noncomputable def supportDerivedPullbackIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (Etale.upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory ⋙
        (comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory ≅
      (comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory ⋙
        (upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory :=
  supportDerivedCoefficientPullbackIso (ModuleCat.{u + 1} A) f

open MonoidalCategory

/-- Apply the existing bifunctor to two isomorphisms without unfolding a
scheme-indexed monoidal instance.
Source: blueprint tensor comparison (blueprint: lem-pur-support-site-comparison). -/
noncomputable def supportBifunctorIso
    {C : Type v₁} {D : Type v₂} {E : Type v₃}
    [Category.{w₁} C] [Category.{w₂} D] [Category.{w₃} E]
    (B : C ⥤ D ⥤ E) {M M' : C} {N N' : D} (a : M ≅ M') (b : N ≅ N') :
    (B.obj M).obj N ≅ (B.obj M').obj N' :=
  (B.mapIso a).app N ≪≫ (B.obj M').mapIso b

/-- The canonical derived monoidal comparison, assembled from the general
left-derived tensor comparison and exact/left-derived identifications. Generic
coefficients keep their categorical structures abstract during elaboration.
Source: blueprint specified theta (blueprint: lem-pur-support-site-comparison). -/
noncomputable def supportDerivedComparisonTensorIso
    (D : Type v₁) [Category.{u + 1} D] [Abelian D] [IsGrothendieckAbelian.{u + 1} D]
    [MonoidalCategory D] [MonoidalPreadditive D] [SymmetricCategory D] [MonoidalClosed D]
    [Abelian.HasFunctorialFlatResolution D]
    (T : Scheme.{u}) [(comparisonUpperStar D T).PreservesFlat]
    (K L : DerivedCategory (Sheaf T.smallEtaleTopology D)) :
    (comparisonUpperStar D T).mapDerivedCategory.obj (((Etale.derivedTensor D T).obj K).obj L) ≅
      ((derivedTensor D T).obj ((comparisonUpperStar D T).mapDerivedCategory.obj K)).obj
        ((comparisonUpperStar D T).mapDerivedCategory.obj L) :=
  (comparisonUpperStar D T).leftDerivedFunctorIsoMapDerivedCategory.symm.app
      (((Etale.derivedTensor D T).obj K).obj L) ≪≫
    ((asIso (comparisonUpperStar D T).leftDerivedTensorComparison).app K).app L ≪≫
    supportBifunctorIso (derivedTensor D T)
      ((comparisonUpperStar D T).leftDerivedFunctorIsoMapDerivedCategory.app K)
      ((comparisonUpperStar D T).leftDerivedFunctorIsoMapDerivedCategory.app L)

/-- The specified exterior-product coefficient comparison: tensor comparison followed
by the two canonical comparison-pullback identifications.
Source: blueprint displayed `theta` (blueprint: lem-pur-support-site-comparison). -/
noncomputable def supportExteriorCoefficientIso [Finite A]
    {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (L : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (comparisonUpperStar (ModuleCat.{u + 1} A) (pullback f g)).mapDerivedCategory.obj
      (Etale.externalProduct (ModuleCat.{u + 1} A) f g K L) ≅
    externalProduct (ModuleCat.{u + 1} A) f g
      ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj K)
      ((comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory.obj L) :=
  (comparisonUpperStar (ModuleCat.{u + 1} A) (pullback f g)).mapDerivedCategory.mapIso
    (supportBifunctorIso (Etale.derivedTensor (ModuleCat.{u + 1} A) (pullback f g))
      ((Etale.leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A)
        (pullback.fst f g)).app K)
      ((Etale.leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A)
        (pullback.snd f g)).app L)) ≪≫
  supportDerivedComparisonTensorIso (ModuleCat.{u + 1} A) (pullback f g)
    ((Etale.upperStar (ModuleCat.{u + 1} A) (pullback.fst f g)).mapDerivedCategory.obj K)
    ((Etale.upperStar (ModuleCat.{u + 1} A) (pullback.snd f g)).mapDerivedCategory.obj L) ≪≫
  supportBifunctorIso (derivedTensor (ModuleCat.{u + 1} A) (pullback f g))
    ((supportDerivedPullbackIso A (pullback.fst f g)).app K)
    ((supportDerivedPullbackIso A (pullback.snd f g)).app L) ≪≫
  supportBifunctorIso (derivedTensor (ModuleCat.{u + 1} A) (pullback f g))
    ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A)
      (pullback.fst f g)).symm.app
        ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj K))
    ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A)
      (pullback.snd f g)).symm.app
        ((comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory.obj L)) ≪≫
  eqToIso (supportedExternalProduct_eq A f g
    ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj K)
    ((comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory.obj L))

private theorem rightDerivedPullback_precomp
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    [Abelian.HasKInjectiveResolutions C] [Abelian.HasKInjectiveResolutions D]
    (P : C ⥤ D) [P.Additive] [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    {F G : C ⥤ E} {H : D ⥤ E} [F.Additive] [G.Additive] [H.Additive]
    (e : F ⟶ G) (r : G ⟶ P ⋙ H) :
    Functor.rightDerivedFunctorNatTrans e ≫ Functor.rightDerivedPullback P r =
      Functor.rightDerivedPullback P (e ≫ r) := by
  have h := Functor.rightDerivedFunctorNatTrans_comp_rightDerivedPullback P
    e (𝟙 H) (e ≫ r) r (by simp)
  simpa only [Functor.rightDerivedFunctorNatTrans, NatTrans.mapHomotopyCategory_id,
    Functor.whiskerRight_id, Functor.whiskerRight_id', Functor.rightDerivedNatTrans_id,
    Functor.whiskerLeft_id, Functor.whiskerLeft_id', Category.comp_id] using h

private theorem comparisonUnbounded_eq_global (A : Type (u + 1)) [CommRing A]
    {Z T : Scheme.{u}} (i : Z ⟶ T) [IsClosedImmersion i]
    (M : DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    supportComparisonUnbounded A i M =
      (Functor.rightDerivedPullback (comparisonUpperStar (ModuleCat.{u + 1} A) T)
        ((supportKernelEvaluationIso A i).hom ≫ supportComparisonUnit A i)).app M.obj := by
  rw [comparisonUnbounded_eq]
  exact NatTrans.congr_app (rightDerivedPullback_precomp _ _ _) M.obj

section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true
set_option backward.defeqAttrib.useBackward true
private noncomputable def coefficientComparison (A : Type (u + 1)) [CommRing A] [Finite A]
    {C T : Scheme.{u}} (i : C ⟶ T) [IsClosedImmersion i] [IsLocallyNoetherian T] :
    Etale.supportedCoefficients A i ⋙ comparisonUpperStar (ModuleCat.{u + 1} A) T ≅
      supportedCoefficients A i := by
  let ae : Etale.supportedCoefficients A i ⊣ etaleSupportKernel A i :=
    (Etale.supportedCoefficientAdjunction A i).ofNatIsoRight (supportKernelEvaluationIso A i)
  let a : Etale.supportedCoefficients A i ⋙ comparisonUpperStar (ModuleCat.{u + 1} A) T ⊣
      supportSections i A := ae.comp (comparisonAdjunction (ModuleCat.{u + 1} A) T)
  exact a.leftAdjointUniq (supportedCoefficientAdjunction A i)

private theorem comparisonMate_eq (A : Type (u + 1)) [CommRing A] [Finite A]
    {C T : Scheme.{u}} (i : C ⟶ T) [IsClosedImmersion i] [IsLocallyNoetherian T] :
    Etale.supportCoefficientMate (Etale.supportedCoefficientAdjunction A i)
        (supportedCoefficientAdjunction A i) (comparisonUpperStar (ModuleCat.{u + 1} A) T)
        ((supportKernelEvaluationIso A i).hom ≫ supportComparisonUnit A i) =
      (coefficientComparison A i).inv := by
  let ae : Etale.supportedCoefficients A i ⊣ etaleSupportKernel A i :=
    (Etale.supportedCoefficientAdjunction A i).ofNatIsoRight (supportKernelEvaluationIso A i)
  let ac := ae.comp (comparisonAdjunction (ModuleCat.{u + 1} A) T)
  let ap := supportedCoefficientAdjunction A i
  apply NatTrans.ext
  funext M
  apply (ap.homEquiv _ _).injective
  rw [Etale.supportMate_unit]
  have hn := Adjunction.homEquiv_leftAdjointUniq_hom_app ap ac M
  rw [← Adjunction.leftAdjointUniq_inv_app] at hn
  change ap.homEquiv _ _ ((coefficientComparison A i).inv.app M) = ac.unit.app M at hn
  rw [hn]
  change _ = ae.unit.app M ≫ (etaleSupportKernel A i).map
    ((comparisonAdjunction (ModuleCat.{u + 1} A) T).unit.app
      ((Etale.supportedCoefficients A i).obj M))
  dsimp only [ae, Adjunction.ofNatIsoRight_unit, NatTrans.comp_app,
    Functor.whiskerLeft_app]
  rw [Category.assoc]
  congr 1
  apply (cancel_mono (kernel.ι
    (((comparisonUpperStar (ModuleCat.{u + 1} A) T).obj
      ((Etale.supportedCoefficients A i).obj M)).obj.map (supportRestrictionArrow i).op))).mp
  simp only [Category.assoc]
  erw [(supportComparisonUnit_existsUnique A i).choose_spec.1, kernel.lift_ι]
  rfl

private theorem derivedComparisonMate_eq (A : Type (u + 1)) [CommRing A] [Finite A]
    {C T : Scheme.{u}} (i : C ⟶ T) [IsClosedImmersion i] [IsLocallyNoetherian T] :
    Etale.supportCoefficientMate (Etale.supportedCoefficientDerivedAdjunction A i)
        (supportedCoefficientDerivedAdjunction A i)
        (comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory
        (Functor.rightDerivedPullback (comparisonUpperStar (ModuleCat.{u + 1} A) T)
          ((supportKernelEvaluationIso A i).hom ≫ supportComparisonUnit A i)) =
      Functor.exactDerivedMap (coefficientComparison A i).inv ≫
        (Functor.mapDerivedCategoryCompIso (Etale.supportedCoefficients A i)
          (comparisonUpperStar (ModuleCat.{u + 1} A) T)).hom := by
  dsimp only [Etale.supportedCoefficientDerivedAdjunction, supportedCoefficientDerivedAdjunction]
  rw [Etale.derivedMate_eq, comparisonMate_eq]

end

section GenericOpenComparison
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true
set_option backward.defeqAttrib.useBackward true
private lemma mateSquareDirect
    {B C C' D D' : Type*}
    [Category B] [Category C] [Category C'] [Category D] [Category D']
    {F : B ⥤ C} {R : C ⥤ B} {F' : B ⥤ C'} {R' : C' ⥤ B}
    {G : B ⥤ D} {S : D ⥤ B} {G' : B ⥤ D'} {S' : D' ⥤ B}
    (a : F ⊣ R) (a' : F' ⊣ R') (b : G ⊣ S) (b' : G' ⊣ S')
    (P : C ⥤ C') (Q : D ⥤ D') (H : C ⥤ D) (J : C' ⥤ D')
    (r : R ⟶ H ⋙ S) (r' : R' ⟶ J ⋙ S')
    (t : R ⟶ P ⋙ R') (γ : G' ⟶ G ⋙ Q) (e : P ⋙ J ≅ H ⋙ Q)
    (h : ∀ M,
      γ.app M ≫
          Q.map ((AlgebraicGeometry.Etale.supportCoefficientMate a b H r).app M) =
        (AlgebraicGeometry.Etale.supportCoefficientMate a' b' J r').app M ≫
          J.map ((AlgebraicGeometry.Etale.supportCoefficientMate a a' P t).app M) ≫
          e.hom.app (F.obj M)) (K : C) :
    r.app K ≫ b'.homEquiv _ _ (γ.app (S.obj (H.obj K)) ≫
      Q.map (b.counit.app (H.obj K))) =
      t.app K ≫ r'.app (P.obj K) ≫ S'.map (e.hom.app K) := by
  let α := AlgebraicGeometry.Etale.supportCoefficientMate a b H r
  let α' := AlgebraicGeometry.Etale.supportCoefficientMate a' b' J r'
  let β := AlgebraicGeometry.Etale.supportCoefficientMate a a' P t
  have hr : b.homEquiv _ _ (α.app (R.obj K) ≫ H.map (a.counit.app K)) = r.app K := by
    rw [AlgebraicGeometry.Etale.coefficientMate_transpose]
    simp only [Adjunction.homEquiv_apply, Adjunction.right_triangle_components,
      Category.id_comp, Functor.id_obj]
  have ht : a'.homEquiv _ _ (β.app (R.obj K) ≫ P.map (a.counit.app K)) = t.app K := by
    rw [AlgebraicGeometry.Etale.coefficientMate_transpose]
    simp only [Adjunction.homEquiv_apply, Adjunction.right_triangle_components,
      Category.id_comp, Functor.id_obj]
  calc
    r.app K ≫ b'.homEquiv _ _ (γ.app (S.obj (H.obj K)) ≫
      Q.map (b.counit.app (H.obj K))) =
        b'.homEquiv _ _ (γ.app (R.obj K) ≫
          Q.map (α.app (R.obj K) ≫ H.map (a.counit.app K))) := by
      rw [← b'.homEquiv_naturality_left]
      congr 1
      have hn := γ.naturality (r.app K)
      simp only [Functor.comp_obj, Functor.comp_map] at hn
      rw [reassoc_of% hn]
      rw [← Q.map_comp, AlgebraicGeometry.Etale.coefficientMate_counit]
    _ = b'.homEquiv _ _ (α'.app (R.obj K) ≫
        J.map (β.app (R.obj K) ≫ P.map (a.counit.app K)) ≫ e.hom.app K) := by
      congr 1
      simp only [Functor.map_comp, Category.assoc]
      rw [← Category.assoc, h, Category.assoc, Category.assoc]
      have he := e.hom.naturality (a.counit.app K)
      simp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj] at he
      rw [← he]
    _ = t.app K ≫ r'.app (P.obj K) ≫ S'.map (e.hom.app K) := by
      rw [← Category.assoc, b'.homEquiv_naturality_right,
        AlgebraicGeometry.Etale.coefficientMate_transpose, ht]
      exact Category.assoc _ _ _

private noncomputable def coefficientRightMate
    {B C D : Type*} [Category B] [Category C] [Category D]
    {F : B ⥤ C} {R : C ⥤ B} {F' : B ⥤ D} {R' : D ⥤ B}
    (a : F ⊣ R) (a' : F' ⊣ R') (H : C ⥤ D) (α : F' ⟶ F ⋙ H) :
    R ⟶ H ⋙ R' :=
  (Functor.rightUnitor R).inv ≫
    (mateEquiv a a' (TwoSquare.mk _ _ _ _ ((Functor.leftUnitor F').hom ≫ α))).natTrans

private lemma coefficientRightMate_app
    {B C D : Type*} [Category B] [Category C] [Category D]
    {F : B ⥤ C} {R : C ⥤ B} {F' : B ⥤ D} {R' : D ⥤ B}
    (a : F ⊣ R) (a' : F' ⊣ R') (H : C ⥤ D) (α : F' ⟶ F ⋙ H) (K : C) :
    (coefficientRightMate a a' H α).app K =
      a'.homEquiv _ _ (α.app (R.obj K) ≫ H.map (a.counit.app K)) := by
  simp [coefficientRightMate, mateEquiv_apply, Adjunction.homEquiv_apply]

private lemma coefficientLeftRight
    {B C D : Type*} [Category B] [Category C] [Category D]
    {F : B ⥤ C} {R : C ⥤ B} {F' : B ⥤ D} {R' : D ⥤ B}
    (a : F ⊣ R) (a' : F' ⊣ R') (H : C ⥤ D) (α : F' ⟶ F ⋙ H) :
    AlgebraicGeometry.Etale.supportCoefficientMate a a' H
      (coefficientRightMate a a' H α) = α := by
  unfold AlgebraicGeometry.Etale.supportCoefficientMate coefficientRightMate
  simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  have h := (mateEquiv a a').symm_apply_apply
    (TwoSquare.mk _ _ _ _ ((Functor.leftUnitor F').hom ≫ α))
  rw [h]
  simp

private lemma coefficientRightLeft
    {B C D : Type*} [Category B] [Category C] [Category D]
    {F : B ⥤ C} {R : C ⥤ B} {F' : B ⥤ D} {R' : D ⥤ B}
    (a : F ⊣ R) (a' : F' ⊣ R') (H : C ⥤ D) (r : R ⟶ H ⋙ R') :
    coefficientRightMate a a' H
      (AlgebraicGeometry.Etale.supportCoefficientMate a a' H r) = r := by
  unfold AlgebraicGeometry.Etale.supportCoefficientMate coefficientRightMate
  simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  have h := (mateEquiv a a').apply_symm_apply
    (TwoSquare.mk _ _ _ _ ((Functor.rightUnitor R).hom ≫ r))
  rw [h]
  simp

private lemma exactMap_iso
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    {F G : C ⥤ D} [F.Additive] [G.Additive]
    [CategoryTheory.Limits.PreservesFiniteLimits F]
    [CategoryTheory.Limits.PreservesFiniteColimits F]
    [CategoryTheory.Limits.PreservesFiniteLimits G]
    [CategoryTheory.Limits.PreservesFiniteColimits G] (e : F ≅ G) :
    Functor.exactDerivedMap e.hom = (Functor.mapDerivedCategoryNatIso e).hom := by
  apply Localization.natTrans_ext DerivedCategory.Qh (HomotopyCategory.quasiIso C (.up ℤ))
  intro K
  apply (cancel_mono (G.mapDerivedCategoryFactorsh.hom.app K)).mp
  rw [AlgebraicGeometry.Etale.exactMap_fac, Functor.mapDerivedCategoryNatIso_fach]

private lemma derivedRightMate
    {B C D : Type*} [Category B] [Category C] [Category D]
    [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory B] [HasDerivedCategory C] [HasDerivedCategory D]
    [CategoryTheory.Abelian.HasKInjectiveResolutions C]
    [CategoryTheory.Abelian.HasKInjectiveResolutions D]
    {F : B ⥤ C} {R : C ⥤ B} {F' : B ⥤ D} {R' : D ⥤ B}
    [F.Additive] [R.Additive] [F'.Additive] [R'.Additive]
    [CategoryTheory.Limits.PreservesFiniteLimits F]
    [CategoryTheory.Limits.PreservesFiniteColimits F]
    [CategoryTheory.Limits.PreservesFiniteLimits F']
    [CategoryTheory.Limits.PreservesFiniteColimits F']
    (a : F ⊣ R) (a' : F' ⊣ R') (H : C ⥤ D) [H.Additive]
    [CategoryTheory.Limits.PreservesFiniteLimits H]
    [CategoryTheory.Limits.PreservesFiniteColimits H] (α : F' ⟶ F ⋙ H) :
    coefficientRightMate a.mapDerivedCategoryRightDerivedAdjunction
      a'.mapDerivedCategoryRightDerivedAdjunction H.mapDerivedCategory
      (Functor.exactDerivedMap α ≫ (Functor.mapDerivedCategoryCompIso F H).hom) =
      Functor.rightDerivedPullback H (coefficientRightMate a a' H α) := by
  have h := AlgebraicGeometry.Etale.derivedMate_eq a a' H
    (coefficientRightMate a a' H α)
  rw [coefficientLeftRight] at h
  rw [← h, coefficientRightLeft]

private lemma derivedPullbackSquare
    {C₀ C₁ C₂ C₃ D : Type*}
    [Category C₀] [Category C₁] [Category C₂] [Category C₃] [Category D]
    [Abelian C₀] [Abelian C₁] [Abelian C₂] [Abelian C₃] [Abelian D]
    [HasDerivedCategory C₀] [HasDerivedCategory C₁] [HasDerivedCategory C₂]
    [HasDerivedCategory C₃] [HasDerivedCategory D]
    [CategoryTheory.Abelian.HasKInjectiveResolutions C₀]
    [CategoryTheory.Abelian.HasKInjectiveResolutions C₁]
    [CategoryTheory.Abelian.HasKInjectiveResolutions C₂]
    [CategoryTheory.Abelian.HasKInjectiveResolutions C₃]
    (P : C₀ ⥤ C₁) (Q : C₁ ⥤ C₃) (R : C₀ ⥤ C₂) (S : C₂ ⥤ C₃)
    [P.Additive] [Q.Additive] [R.Additive] [S.Additive]
    [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    [PreservesFiniteLimits Q] [PreservesFiniteColimits Q]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    [PreservesFiniteLimits S] [PreservesFiniteColimits S]
    (F : C₀ ⥤ D) (F₁ : C₁ ⥤ D) (F₂ : C₂ ⥤ D) (F₃ : C₃ ⥤ D)
    [F.Additive] [F₁.Additive] [F₂.Additive] [F₃.Additive]
    (α : F ⟶ P ⋙ F₁) (β : F₁ ⟶ Q ⋙ F₃)
    (γ : F ⟶ R ⋙ F₂) (δ : F₂ ⟶ S ⋙ F₃) (e : P ⋙ Q ≅ R ⋙ S)
    (h : ∀ K, α.app K ≫ β.app (P.obj K) ≫ F₃.map (e.hom.app K) =
      γ.app K ≫ δ.app (R.obj K)) (M : DerivedCategory C₀) :
    (Functor.rightDerivedPullback R γ).app M ≫
        (Functor.rightDerivedPullback S δ).app (R.mapDerivedCategory.obj M) =
      (Functor.rightDerivedPullback P α).app M ≫
        (Functor.rightDerivedPullback Q β).app (P.mapDerivedCategory.obj M) ≫
        F₃.rightDerivedFunctor.map
          ((Functor.mapDerivedCategoryCompIso P Q).inv.app M ≫
            (Functor.mapDerivedCategoryNatIso e).hom.app M ≫
            (Functor.mapDerivedCategoryCompIso R S).hom.app M) := by
  let t : F ⟶ (P ⋙ Q) ⋙ F₃ :=
    α ≫ Functor.whiskerLeft P β ≫ (Functor.associator P Q F₃).inv
  have h₁ := Functor.rightDerivedPullback_comp P Q (P ⋙ Q) (Iso.refl _)
    α β t (by ext K; simp [t]) M
  have h₂ := Functor.rightDerivedPullback_comp R S (P ⋙ Q) e
    γ δ t (by ext K; simpa [t] using h K) M
  simp only [Iso.trans_hom, NatTrans.comp_app,
    Functor.mapDerivedCategoryNatIso_refl, Category.id_comp] at h₁ h₂
  rw [← h₂]
  have h₁' := congrArg (fun f ↦ f ≫ F₃.rightDerivedFunctor.map
    ((Functor.mapDerivedCategoryCompIso P Q).inv.app M ≫
      (Functor.mapDerivedCategoryNatIso e).hom.app M ≫
      (Functor.mapDerivedCategoryCompIso R S).hom.app M)) h₁
  simp only [Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app_assoc] at h₁'
  exact h₁'

end GenericOpenComparison

section CoefficientNormalization
open Scheme
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true
set_option backward.defeqAttrib.useBackward true

private theorem quotient_mate
    {B C D : Type*} [Category B] [Category C] [Category D]
    {F : B ⥤ C} {R : C ⥤ B} {F' : B ⥤ D} {R' : D ⥤ B}
    {G : B ⥤ C} {S : C ⥤ B} {G' : B ⥤ D} {S' : D ⥤ B}
    (a : F ⊣ R) (a' : F' ⊣ R') (c : G ⊣ S) (c' : G' ⊣ S')
    (H : C ⥤ D) (r : R ⟶ H ⋙ R') (s : S ⟶ H ⋙ S')
    (ι : R ⟶ S) (ι' : R' ⟶ S')
    (hr : r ≫ Functor.whiskerLeft H ι' = ι ≫ s)
    (M : B) (q : G.obj M ⟶ F.obj M) (q' : G'.obj M ⟶ F'.obj M)
    (hq : c.homEquiv _ _ q = a.unit.app M ≫ ι.app (F.obj M))
    (hq' : ∀ K (f : F'.obj M ⟶ K),
      c'.homEquiv _ _ (q' ≫ f) = a'.homEquiv _ _ f ≫ ι'.app K) :
    q' ≫ (Etale.supportCoefficientMate a a' H r).app M =
      (Etale.supportCoefficientMate c c' H s).app M ≫ H.map q := by
  apply (c'.homEquiv _ _).injective
  rw [hq', Etale.supportMate_unit]
  erw [Etale.coefficientMate_transpose c c' H s q, hq]
  simpa only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.comp_obj, Functor.id_obj,
    Category.assoc] using
    congrArg (fun t ↦ a.unit.app M ≫ t.app (F.obj M)) hr
private theorem quotient_mate_normalized
    {B C D : Type*} [Category B] [Category C] [Category D]
    {F : B ⥤ C} {R : C ⥤ B} {F' : B ⥤ D} {R' : D ⥤ B}
    {G : B ⥤ C} {S : C ⥤ B} {G' : B ⥤ D} {S' : D ⥤ B}
    (a : F ⊣ R) (a' : F' ⊣ R') (c : G ⊣ S) (c' : G' ⊣ S')
    (H : C ⥤ D) (r : R ⟶ H ⋙ R') (s : S ⟶ H ⋙ S')
    (ι : R ⟶ S) (ι' : R' ⟶ S')
    (hr : r ≫ Functor.whiskerLeft H ι' = ι ≫ s)
    (M : B) (q : G.obj M ⟶ F.obj M) (q' : G'.obj M ⟶ F'.obj M)
    (hq : ∀ K (f : M ⟶ R.obj K),
      q ≫ (a.homEquiv _ _).symm f = (c.homEquiv _ _).symm (f ≫ ι.app K))
    (hq' : ∀ K (f : M ⟶ R'.obj K),
      q' ≫ (a'.homEquiv _ _).symm f = (c'.homEquiv _ _).symm (f ≫ ι'.app K)) :
    q' ≫ (Etale.supportCoefficientMate a a' H r).app M =
      (Etale.supportCoefficientMate c c' H s).app M ≫ H.map q := by
  apply quotient_mate a a' c c' H r s ι ι' hr M q q'
  · have h := hq (F.obj M) (a.unit.app M)
    rw [Adjunction.homEquiv_symm_unit, Category.comp_id] at h
    exact (congrArg (c.homEquiv _ _) h).trans (Equiv.apply_symm_apply _ _)
  · intro K f
    have h := hq' K (a'.homEquiv _ _ f)
    rw [Equiv.symm_apply_apply] at h
    exact (congrArg (c'.homEquiv _ _) h).trans (Equiv.apply_symm_apply _ _)

namespace CachedConstantCoherence
section
attribute [-instance] supportedSheaf_isMonoidal supportedSheaf_monoidalPreadditive
  supportedSheaf_isMonoidalGeneric supportedSheaf_monoidalPreadditiveGeneric
private noncomputable def constantComparison (D : Type v₁) [Category.{u + 1} D] [Abelian D]
    [IsGrothendieckAbelian.{u + 1} D]
    (T : Scheme.{u}) :
    constantSheaf T.smallEtaleTopology D ⋙
      comparisonUpperStar D T ≅
    constantSheaf (Scheme.ProEt.topology T) D :=
  (((constantSheafΓAdj T.smallEtaleTopology D).comp
    (comparisonAdjunction D T)).ofNatIsoRight
      (comparisonLowerStarCompGlobalSectionsIso D T)).leftAdjointUniq
    (constantSheafΓAdj (Scheme.ProEt.topology T) D)

private noncomputable def constantComparisonTerminal (D : Type v₁) [Category.{u + 1} D] [Abelian D]
    [IsGrothendieckAbelian.{u + 1} D]
    (T : Scheme.{u}) :
    constantSheaf T.smallEtaleTopology D ⋙
      comparisonUpperStar D T ≅
    constantSheaf (Scheme.ProEt.topology T) D :=
  ((constantSheafAdj T.smallEtaleTopology D
    (Scheme.Etale.isTerminalMkId T)).comp
    (comparisonAdjunction D T)).leftAdjointUniq
    (constantSheafAdj (Scheme.ProEt.topology T) D
      (Scheme.ProEt.isTerminalMkId T))

private lemma constantComparisonTerminal_eq_inverse (D : Type v₁) [Category.{u + 1} D] [Abelian D]
    [IsGrothendieckAbelian.{u + 1} D]
    (T : Scheme.{u}) (M : D) :
    (constantComparisonTerminal D T).hom.app M =
      Scheme.constantInverse T.smallEtaleTopology (Scheme.ProEt.topology T) (Scheme.toProEt T)
        (comparisonAdjunction D T) M := by
  let ae := constantSheafAdj T.smallEtaleTopology D (Scheme.Etale.isTerminalMkId T)
  let ap := constantSheafAdj (Scheme.ProEt.topology T) D (Scheme.ProEt.isTerminalMkId T)
  let p := comparisonAdjunction D T
  apply (p.homEquiv _ _).injective
  unfold Scheme.constantInverse
  conv_rhs => erw [Equiv.apply_symm_apply]
  apply (ae.homEquiv _ _).injective
  have hc : (ae.comp p).homEquiv _ _ ((constantComparisonTerminal D T).hom.app M) =
      ae.homEquiv _ _ (p.homEquiv _ _ ((constantComparisonTerminal D T).hom.app M)) := by
    rw [Adjunction.comp_homEquiv]
    rfl
  rw [← hc]
  erw [Adjunction.homEquiv_leftAdjointUniq_hom_app]
  simp only [Adjunction.homEquiv_apply, ae, constantSheafAdj, Adjunction.comp_unit_app,
    constantPresheafAdj_unit_app, sheafificationAdjunction_unit_app, Category.id_comp]
  change (toSheafify (Scheme.ProEt.topology T)
      ((Functor.const (Scheme.ProEt T)ᵒᵖ).obj M)).app
        (op ((Scheme.toProEt T).obj (Scheme.Etale.mk (𝟙 T)))) =
    (toSheafify T.smallEtaleTopology ((Functor.const T.Etaleᵒᵖ).obj M)).app
      (op (Scheme.Etale.mk (𝟙 T))) ≫
        (Scheme.constantDirect T.smallEtaleTopology (Scheme.ProEt.topology T)
          (Scheme.toProEt T) M).hom.app (op (Scheme.Etale.mk (𝟙 T)))
  exact (Scheme.constantDirect_unit T.smallEtaleTopology (Scheme.ProEt.topology T)
    (Scheme.toProEt T) M (op (Scheme.Etale.mk (𝟙 T)))).symm

private lemma transportedHom
    {B C D : Type*} [Category B] [Category C] [Category D]
    {L : B ⥤ C} {R : C ⥤ B} {P : C ⥤ D} {Q : D ⥤ C} {S : D ⥤ B}
    (a : L ⊣ R) (p : P ⊣ Q) (d : Q ⋙ R ≅ S)
    (M : B) (N : D) (t : L.obj M ⟶ Q.obj N) :
    ((a.comp p).ofNatIsoRight d).homEquiv M N ((p.homEquiv _ _).symm t) =
      a.homEquiv _ _ t ≫ d.hom.app N := by
  rw [Adjunction.homEquiv_ofNatIsoRight_apply, Adjunction.comp_homEquiv]
  change a.homEquiv _ _ (p.homEquiv _ _ ((p.homEquiv _ _).symm t)) ≫ d.hom.app N = _
  rw [Equiv.apply_symm_apply]


private lemma constantComparison_eq_terminal (D : Type v₁) [Category.{u + 1} D] [Abelian D]
    [IsGrothendieckAbelian.{u + 1} D]
    (T : Scheme.{u}) : constantComparison D T = constantComparisonTerminal D T := by
  let ae := constantSheafΓAdj T.smallEtaleTopology D
  let ap := constantSheafΓAdj (Scheme.ProEt.topology T) D
  let aet := constantSheafAdj T.smallEtaleTopology D (Scheme.Etale.isTerminalMkId T)
  let apt := constantSheafAdj (Scheme.ProEt.topology T) D (Scheme.ProEt.isTerminalMkId T)
  let ac := (ae.comp (comparisonAdjunction D T)).ofNatIsoRight
    (comparisonLowerStarCompGlobalSectionsIso D T)
  let act := aet.comp (comparisonAdjunction D T)
  apply Iso.ext
  apply NatTrans.ext
  funext M
  apply (act.homEquiv _ _).injective
  have hn := Adjunction.homEquiv_leftAdjointUniq_hom_app ac ap M
  change ac.homEquiv _ _ ((constantComparison D T).hom.app M) = ap.unit.app M at hn
  have hn' := Adjunction.homEquiv_leftAdjointUniq_hom_app act apt M
  change act.homEquiv _ _ ((constantComparisonTerminal D T).hom.app M) = apt.unit.app M at hn'
  rw [hn']
  have he := ae.unit_rightAdjointUniq_hom_app aet M
  have hp := ap.unit_rightAdjointUniq_hom_app apt M
  rw [← hp, ← hn]
  have hac : ac.unit.app M =
      (ae.comp (comparisonAdjunction D T)).unit.app M ≫
        (comparisonLowerStarCompGlobalSectionsIso D T).hom.app _ := rfl
  have hact : act.unit.app M = (aet.comp (comparisonAdjunction D T)).unit.app M := by
    simp [act]
  simp only [Adjunction.homEquiv_apply, Category.assoc]
  change act.unit.app M ≫ _ = ac.unit.app M ≫ _ ≫ _
  rw [hac, hact, Adjunction.comp_unit_app, Adjunction.comp_unit_app]
  rw [← he]
  let e := Sheaf.ΓNatIsoSheafSections T.smallEtaleTopology D
    (Scheme.Etale.isTerminalMkId T)
  let ep := Sheaf.ΓNatIsoSheafSections (Scheme.ProEt.topology T) D
    (Scheme.ProEt.isTerminalMkId T)
  let t := (constantComparison D T).hom.app M
  let η := (comparisonAdjunction D T).unit.app
    ((constantSheaf T.smallEtaleTopology D).obj M)
  simp only [Category.assoc]
  change ae.unit.app M ≫ e.hom.app _ ≫
      ((sheafSections T.smallEtaleTopology D).obj (op (Scheme.Etale.mk (𝟙 T)))).map η ≫
      ((sheafSections T.smallEtaleTopology D).obj (op (Scheme.Etale.mk (𝟙 T)))).map
        ((comparisonLowerStar D T).map t) =
    ae.unit.app M ≫ (Sheaf.Γ T.smallEtaleTopology D).map η ≫
      (comparisonLowerStarCompGlobalSectionsIso D T).hom.app _ ≫
      (Sheaf.Γ (Scheme.ProEt.topology T) D).map t ≫ ep.hom.app _
  have hd : (comparisonLowerStarCompGlobalSectionsIso D T).hom =
      Functor.whiskerLeft (comparisonLowerStar D T) e.hom ≫ ep.inv := by
    simp only [comparisonLowerStarCompGlobalSectionsIso, Iso.trans_hom,
      Functor.isoWhiskerLeft_hom, Iso.refl_hom, Iso.symm_hom, Category.id_comp]
    have hterm : Scheme.Etale.isTerminalMkId T =
        MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale T := Subsingleton.elim _ _
    simp only [e, ep, hterm]
  have hdm := congrArg (fun α ↦ α.app
    ((comparisonUpperStar D T).obj ((constantSheaf T.smallEtaleTopology D).obj M))) hd
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app] at hdm
  rw [hdm]
  simp only [Category.assoc]
  rw [← reassoc_of% ep.inv.naturality t, Iso.inv_hom_id_app, Category.comp_id]
  have ht :
      ((sheafSections T.smallEtaleTopology D).obj (op (Scheme.Etale.mk (𝟙 T)))).map
        ((comparisonLowerStar D T).map t) =
      ((sheafSections (Scheme.ProEt.topology T) D).obj
        (op (Scheme.ProEt.mk (𝟙 T)))).map t := rfl
  rw [← ht]
  rw [reassoc_of% e.hom.naturality η]


private lemma etConstant_eq_inverse (D : Type v₁) [Category.{u + 1} D] [Abelian D]
    [IsGrothendieckAbelian.{u + 1} D]
    {X Y : Scheme.{u}} (h : X ⟶ Y) (M : D) :
    (Scheme.upperStarConstantSheafIso D h).hom.app M =
      Scheme.constantInverse Y.smallEtaleTopology X.smallEtaleTopology
        h.Etale (Etale.upperStarLowerStarAdjunction D h) M := by
  let ay := constantSheafAdj Y.smallEtaleTopology D terminalIsTerminal
  let ax := constantSheafAdj X.smallEtaleTopology D terminalIsTerminal
  let p := Etale.upperStarLowerStarAdjunction D h
  let d := Etale.lowerStarCompSheafSectionsTerminalIso D h
  let ac := (ay.comp p).ofNatIsoRight d
  apply (ac.homEquiv _ _).injective
  have hn := Adjunction.homEquiv_leftAdjointUniq_hom_app ac ax M
  change ac.homEquiv _ _ ((Scheme.upperStarConstantSheafIso D h).hom.app M) =
    ax.unit.app M at hn
  rw [hn]
  unfold Scheme.constantInverse
  conv_rhs => erw [transportedHom ay p d]
  simp only [Adjunction.homEquiv_apply, ax, ay, constantSheafAdj, Adjunction.comp_unit_app,
    constantPresheafAdj_unit_app, sheafificationAdjunction_unit_app,
    Category.id_comp, Category.assoc]
  change (toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj M)).app
      (op (⊤_ X.Etale)) =
    (toSheafify Y.smallEtaleTopology ((Functor.const Y.Etaleᵒᵖ).obj M)).app
      (op (⊤_ Y.Etale)) ≫
      (Scheme.constantDirect Y.smallEtaleTopology X.smallEtaleTopology h.Etale M).hom.app
        (op (⊤_ Y.Etale)) ≫
      ((constantSheaf X.smallEtaleTopology D).obj M).obj.map
        (PreservesTerminal.iso h.Etale).inv.op
  rw [← Category.assoc, Scheme.constantDirect_unit]
  have hn := (toSheafify X.smallEtaleTopology
    ((Functor.const X.Etaleᵒᵖ).obj M)).naturality (PreservesTerminal.iso h.Etale).inv.op
  simpa only [constantSheaf, Functor.comp_obj, Functor.const_obj_map,
    Functor.const_obj_obj, Functor.op_obj, Category.id_comp] using hn

private lemma proConstant_eq_inverse (D : Type v₁) [Category.{u + 1} D]
    [Abelian D] [IsGrothendieckAbelian.{u + 1} D]
    {X Y : Scheme.{u}} (h : X ⟶ Y) (M : D) :
    (constantSheafCompUpperStarIso D h).hom.app M =
      Scheme.constantInverse (D := D) (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)
        (proEtaleBaseChange h) (upperStarLowerStarAdjunction D h) M := by
  let ay := constantSheafΓAdj (Scheme.ProEt.topology Y) D
  let ax := constantSheafΓAdj (Scheme.ProEt.topology X) D
  let p := upperStarLowerStarAdjunction D h
  let d := globalSectionsLowerStarIso D h
  let ac := (ay.comp p).ofNatIsoRight d
  apply (ac.homEquiv _ _).injective
  have hn := Adjunction.homEquiv_leftAdjointUniq_hom_app ac ax M
  change ac.homEquiv _ _ ((constantSheafCompUpperStarIso D h).hom.app M) = ax.unit.app M at hn
  rw [hn]
  unfold Scheme.constantInverse
  conv_rhs => erw [transportedHom ay p d]
  let ex : Sheaf.Γ (Scheme.ProEt.topology X) D ≅
      (sheafSections (Scheme.ProEt.topology X) D).obj
        (op (Scheme.ProEt.mk (𝟙 X))) :=
    Sheaf.ΓNatIsoSheafSections (Scheme.ProEt.topology X) D
      (Scheme.ProEt.isTerminalMkId X)
  let ey := Sheaf.ΓNatIsoSheafSections (Scheme.ProEt.topology Y) D
    (Scheme.ProEt.isTerminalMkId Y)
  apply (cancel_mono (ex.hom.app ((constantSheaf (Scheme.ProEt.topology X) D).obj M))).mp
  have hx := ax.unit_rightAdjointUniq_hom_app
    (constantSheafAdj (Scheme.ProEt.topology X) D (Scheme.ProEt.isTerminalMkId X)) M
  have hy := ay.unit_rightAdjointUniq_hom_app
    (constantSheafAdj (Scheme.ProEt.topology Y) D (Scheme.ProEt.isTerminalMkId Y)) M
  dsimp only [d, globalSectionsLowerStarIso, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Iso.symm_hom]
  simp only [Category.assoc]
  erw [Iso.inv_hom_id_app]
  simp only [Category.comp_id, Adjunction.homEquiv_apply, Category.assoc]
  erw [ey.hom.naturality_assoc]
  rw [← Category.assoc]
  erw [hx, hy]
  simp only [constantSheafAdj, Adjunction.comp_unit_app,
    constantPresheafAdj_unit_app, sheafificationAdjunction_unit_app, Category.id_comp]
  simp only [NatIso.ofComponents_hom_app, Iso.refl_hom, Category.id_comp,
    Functor.mapIso_inv]
  dsimp only [sheafSections, Functor.flip, CategoryTheory.evaluation]
  change (toSheafify (Scheme.ProEt.topology X)
      ((Functor.const (Scheme.ProEt X)ᵒᵖ).obj M)).app (op (Scheme.ProEt.mk (𝟙 X))) =
    (toSheafify (Scheme.ProEt.topology Y)
      ((Functor.const (Scheme.ProEt Y)ᵒᵖ).obj M)).app (op (Scheme.ProEt.mk (𝟙 Y))) ≫
      (Scheme.constantDirect (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)
        (proEtaleBaseChange h) M).hom.app (op (Scheme.ProEt.mk (𝟙 Y))) ≫
      ((constantSheaf (Scheme.ProEt.topology X) D).obj M).obj.map
        (overPullbackObjMkIdIso h).inv.op
  rw [← Category.assoc, Scheme.constantDirect_unit]
  have hn := (toSheafify (Scheme.ProEt.topology X)
    ((Functor.const (Scheme.ProEt X)ᵒᵖ).obj M)).naturality
      (overPullbackObjMkIdIso h).inv.op
  simpa only [constantSheaf, Functor.comp_obj, Functor.const_obj_map,
    Functor.const_obj_obj, Functor.op_obj, Category.id_comp] using hn

private theorem constantComparisonTerminal_square (D : Type v₁) [Category.{u + 1} D] [Abelian D]
    [IsGrothendieckAbelian.{u + 1} D]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (M : D) :
    (ProEtale.upperStar D f).map ((constantComparisonTerminal D Y).hom.app M) ≫
        (constantSheafCompUpperStarIso D f).hom.app M =
      (ProEtale.supportSiteComparisonCoefficientPullbackIso D f).inv.app
          ((constantSheaf Y.smallEtaleTopology D).obj M) ≫
        (ProEtale.comparisonUpperStar D X).map
          ((Scheme.upperStarConstantSheafIso D f).hom.app
            M) ≫ (constantComparisonTerminal D X).hom.app M := by
  let ap := (ProEtale.comparisonAdjunction D Y).comp
    (proEtaleSheafAdjunction f D)
  let ae := (Etale.upperStarLowerStarAdjunction D f).comp
    (ProEtale.comparisonAdjunction D X)
  let d := ProEtale.supportSiteComparisonCoefficientDirectImageIso D f
  have hd (S : Sheaf (ProEt.topology X) D) (W : Y.Etaleᵒᵖ) :
      ((d.inv.app S).hom.app W) = 𝟙 _ := by
    dsimp only [d, supportSiteComparisonCoefficientDirectImageIso]
    change ((𝟙 _ ≫ S.obj.map (𝟙 _)) ≫ 𝟙 _) = 𝟙 _
    simp only [Category.id_comp, Category.comp_id]
    exact S.obj.map_id _
  simp only [constantComparisonTerminal_eq_inverse, proConstant_eq_inverse, etConstant_eq_inverse]
  apply (ap.homEquiv _ _).injective
  change _ = ap.homEquiv _ _
    (((conjugateIsoEquiv ap ae).symm d).inv.app _ ≫ _)
  have hm := Scheme.homEquiv_mate ap ae d.symm
    ((ProEtale.comparisonUpperStar D X).map
      (Scheme.constantInverse Y.smallEtaleTopology X.smallEtaleTopology f.Etale
        (Etale.upperStarLowerStarAdjunction D f) M) ≫
      Scheme.constantInverse X.smallEtaleTopology (ProEt.topology X) (toProEt X)
        (ProEtale.comparisonAdjunction D X) M)
  simp only [Iso.symm_symm_eq] at hm
  erw [hm]
  have hp := Scheme.constantInverse_composite_adjunct Y.smallEtaleTopology
    (ProEt.topology Y) (ProEt.topology X) (toProEt Y) (proEtaleBaseChange f)
    (ProEtale.comparisonAdjunction D Y) (proEtaleSheafAdjunction f D)
    M
  have he := Scheme.constantInverse_composite_adjunct Y.smallEtaleTopology
    X.smallEtaleTopology (ProEt.topology X) f.Etale (toProEt X)
    (Etale.upperStarLowerStarAdjunction D f)
    (ProEtale.comparisonAdjunction D X) M
  erw [hp, he]
  apply ((sheafificationAdjunction Y.smallEtaleTopology D).homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit]
  apply NatTrans.ext
  funext W
  simp only [sheafificationAdjunction_unit_app, NatTrans.comp_app, Category.assoc]
  change (toSheafify Y.smallEtaleTopology
      ((Functor.const Y.Etaleᵒᵖ).obj M)).app W ≫
      (Scheme.constantDirect Y.smallEtaleTopology (ProEt.topology Y) (toProEt Y)
        M).hom.app W ≫
      (Scheme.constantDirect (ProEt.topology Y) (ProEt.topology X) (proEtaleBaseChange f)
        M).hom.app ((toProEt Y).op.obj W) =
    (toSheafify Y.smallEtaleTopology
      ((Functor.const Y.Etaleᵒᵖ).obj M)).app W ≫
      (Scheme.constantDirect Y.smallEtaleTopology X.smallEtaleTopology f.Etale
        M).hom.app W ≫
      (Scheme.constantDirect X.smallEtaleTopology (ProEt.topology X) (toProEt X)
        M).hom.app (f.Etale.op.obj W) ≫
      ((d.inv.app ((constantSheaf (ProEt.topology X) D).obj
        M)).hom.app W)
  rw [hd]
  rw [← Category.assoc, Scheme.constantDirect_unit, Scheme.constantDirect_unit,
    ← Category.assoc, ← Category.assoc, Scheme.constantDirect_unit, Scheme.constantDirect_unit]
  erw [Category.comp_id]
  rfl


attribute [local instance] Etale.evaluationMonoidal Etale.sectionsMonoidal
  Etale.constantPresheafAdj_monoidal Etale.constantSheafAdj_monoidal
@[instance_reducible]
private noncomputable def canonicalConstantEt (D : Type v₁) [Category.{u + 1} D] [Abelian D]
    [IsGrothendieckAbelian.{u + 1} D]
    [HasSmallSiteSheafify D] [MonoidalCategory D] [MonoidalPreadditive D]
    [SymmetricCategory D] [MonoidalClosed D] [Abelian.HasFunctorialFlatResolution D]
    (T : Scheme.{u}) : (constantSheaf T.smallEtaleTopology D).Monoidal :=
  monoidalConstantSheaf _ _
@[instance_reducible]
private noncomputable def canonicalConstantPro (D : Type v₁) [Category.{u + 1} D] [Abelian D]
    [IsGrothendieckAbelian.{u + 1} D]
    [HasSmallSiteSheafify D] [MonoidalCategory D] [MonoidalPreadditive D]
    [SymmetricCategory D] [MonoidalClosed D] [Abelian.HasFunctorialFlatResolution D]
    (T : Scheme.{u}) :
    (constantSheaf (Scheme.ProEt.topology T) D).Monoidal :=
  monoidalConstantSheaf _ _
attribute [local instance] canonicalConstantEt canonicalConstantPro

private lemma constantComparisonTerminal_monoidal (D : Type v₁) [Category.{u + 1} D] [Abelian D]
    [IsGrothendieckAbelian.{u + 1} D]
    [HasSmallSiteSheafify D] [MonoidalCategory D] [MonoidalPreadditive D]
    [SymmetricCategory D] [MonoidalClosed D] [Abelian.HasFunctorialFlatResolution D]
    (T : Scheme.{u}) : NatTrans.IsMonoidal (constantComparisonTerminal D T).inv := by
  let ae := (constantSheafAdj T.smallEtaleTopology D (Scheme.Etale.isTerminalMkId T)).comp
    (comparisonAdjunction D T)
  let ap := constantSheafAdj (Scheme.ProEt.topology T) D (Scheme.ProEt.isTerminalMkId T)
  let e : comparisonLowerStar D T ⋙
      (sheafSections T.smallEtaleTopology D).obj (op (Scheme.Etale.mk (𝟙 T))) ≅
    (sheafSections (Scheme.ProEt.topology T) D).obj (op (Scheme.ProEt.mk (𝟙 T))) := Iso.refl _
  have hm := Etale.pushforwardSections_monoidal (A := D) (Scheme.toProEt T)
    T.smallEtaleTopology (Scheme.ProEt.topology T) (Scheme.Etale.mk (𝟙 T))
  have hem : (Etale.pushforwardSectionsIso (A := D) (Scheme.toProEt T)
      T.smallEtaleTopology (Scheme.ProEt.topology T) (Scheme.Etale.mk (𝟙 T))).hom = e.hom := by
    apply NatTrans.ext
    funext P
    simp [Etale.pushforwardSectionsIso, Etale.precomposeEvaluationIso,
      Etale.pushforwardUnderlying_inv_app, e]
    rfl
  rw [hem] at hm
  let : NatTrans.IsMonoidal e.hom := hm
  have h := isMonoidal_conjugateEquiv_symm ae ap e.hom
  have he : (conjugateEquiv ae ap).symm e.hom =
      (constantComparisonTerminal D T).inv := rfl
  rw [he] at h
  exact h


end
end CachedConstantCoherence

private noncomputable def constantComparison (A : Type (u + 1)) [CommRing A]
    (T : Scheme.{u}) :
    constantSheaf T.smallEtaleTopology (ModuleCat.{u + 1} A) ⋙
      comparisonUpperStar (ModuleCat.{u + 1} A) T ≅
    constantSheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A) :=
  CachedConstantCoherence.constantComparison (ModuleCat.{u + 1} A) T

private noncomputable def constantComparisonTerminal (A : Type (u + 1)) [CommRing A]
    (T : Scheme.{u}) :
    constantSheaf T.smallEtaleTopology (ModuleCat.{u + 1} A) ⋙
      comparisonUpperStar (ModuleCat.{u + 1} A) T ≅
    constantSheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A) :=
  CachedConstantCoherence.constantComparisonTerminal (ModuleCat.{u + 1} A) T

private lemma constantComparison_eq_terminal (A : Type (u + 1)) [CommRing A]
    (T : Scheme.{u}) : constantComparison A T = constantComparisonTerminal A T := by
  exact CachedConstantCoherence.constantComparison_eq_terminal (ModuleCat.{u + 1} A) T

private noncomputable local instance canonicalConstantEt (A : Type (u + 1)) [CommRing A]
    (T : Scheme.{u}) :
    (constantSheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)).Monoidal :=
  CachedConstantCoherence.canonicalConstantEt (ModuleCat.{u + 1} A) T
private noncomputable local instance canonicalConstantPro (A : Type (u + 1)) [CommRing A]
    (T : Scheme.{u}) :
    (constantSheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A)).Monoidal :=
  CachedConstantCoherence.canonicalConstantPro (ModuleCat.{u + 1} A) T

private lemma constantComparisonTerminal_monoidal (A : Type (u + 1)) [CommRing A]
    (T : Scheme.{u}) : NatTrans.IsMonoidal (constantComparisonTerminal A T).inv := by
  exact CachedConstantCoherence.constantComparisonTerminal_monoidal (ModuleCat.{u + 1} A) T

private theorem constantComparisonTerminal_square (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (M : ModuleCat.{u + 1} A) :
    (ProEtale.upperStar (ModuleCat.{u + 1} A) f).map ((constantComparisonTerminal A Y).hom.app M) ≫
        (constantSheafCompUpperStarIso (ModuleCat.{u + 1} A) f).hom.app M =
      (ProEtale.supportSiteComparisonCoefficientPullbackIso (ModuleCat.{u + 1} A) f).inv.app
          ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A)).obj M) ≫
        (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X).map
          ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) f).hom.app
            M) ≫ (constantComparisonTerminal A X).hom.app M := by
  exact CachedConstantCoherence.constantComparisonTerminal_square (ModuleCat.{u + 1} A) f M

private lemma constantComparison_square_inv (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (M : ModuleCat.{u + 1} A) :
    (constantSheafCompUpperStarIso (ModuleCat.{u + 1} A) f).inv.app M ≫
        (upperStar (ModuleCat.{u + 1} A) f).map ((constantComparison A Y).inv.app M) =
      (constantComparison A X).inv.app M ≫
        (comparisonUpperStar (ModuleCat.{u + 1} A) X).map
          ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) f).inv.app M) ≫
        (supportSiteComparisonCoefficientPullbackIso (ModuleCat.{u + 1} A) f).hom.app
          ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A)).obj M) := by
  let D := ModuleCat.{u + 1} A
  have h : (upperStar D f).mapIso ((constantComparison A Y).app M) ≪≫
      (constantSheafCompUpperStarIso D f).app M =
    ((supportSiteComparisonCoefficientPullbackIso D f).app
        ((constantSheaf Y.smallEtaleTopology D).obj M)).symm ≪≫
      (comparisonUpperStar D X).mapIso ((Scheme.upperStarConstantSheafIso D f).app M) ≪≫
      (constantComparison A X).app M := by
    apply Iso.ext
    simp only [constantComparison_eq_terminal]
    exact constantComparisonTerminal_square A f M
  exact congrArg Iso.inv h


private lemma quotientMateSquare
    {C C' D D' : Type*} [Category C] [Category C'] [Category D] [Category D']
    (P : C ⥤ C') (Q : D ⥤ D') (H : C ⥤ D) (J : C' ⥤ D')
    (e : P ⋙ J ≅ H ⋙ Q)
    {V W : C} {V' W' : C'} {K L : D} {K' L' : D'}
    (q : V ⟶ W) (q₁ : V' ⟶ W') (q' : K ⟶ L) (q₁' : K' ⟶ L') [Epi q₁']
    (c : P.obj V ≅ V') (d : Q.obj K ≅ K')
    (σ : K ⟶ H.obj V) (σ' : K' ⟶ J.obj V')
    (a : L ⟶ H.obj W) (a' : L' ⟶ J.obj W')
    (b : W' ⟶ P.obj W) (b' : L' ⟶ Q.obj L)
    (hq : q' ≫ a = σ ≫ H.map q) (hq₁ : q₁' ≫ a' = σ' ≫ J.map q₁)
    (hb : q₁ ≫ b = c.inv ≫ P.map q) (hb' : q₁' ≫ b' = d.inv ≫ Q.map q')
    (hc : d.inv ≫ Q.map σ = σ' ≫ J.map c.inv ≫ e.hom.app V) :
    b' ≫ Q.map a = a' ≫ J.map b ≫ e.hom.app W := by
  apply (cancel_epi q₁').mp
  simp only [← Category.assoc]
  rw [hb', hq₁]
  simp only [Category.assoc]
  rw [← Q.map_comp, hq, Q.map_comp]
  rw [← J.map_comp_assoc, hb, J.map_comp]
  rw [reassoc_of% hc]
  have hn := e.hom.naturality q
  simp only [Functor.comp_map] at hn
  rw [← hn]
  simp only [Category.assoc]

private noncomputable def globalComparisonUnit (A : Type (u + 1)) [CommRing A]
    (T : Scheme.{u}) :
    Sheaf.Γ T.smallEtaleTopology (ModuleCat.{u + 1} A) ⟶
      comparisonUpperStar (ModuleCat.{u + 1} A) T ⋙
        Sheaf.Γ (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A) :=
  Functor.whiskerRight (comparisonAdjunction (ModuleCat.{u + 1} A) T).unit
      (Sheaf.Γ T.smallEtaleTopology (ModuleCat.{u + 1} A)) ≫
    Functor.whiskerLeft (comparisonUpperStar (ModuleCat.{u + 1} A) T)
      (comparisonLowerStarCompGlobalSectionsIso (ModuleCat.{u + 1} A) T).hom

private lemma constantComparisonMate_eq (A : Type (u + 1)) [CommRing A] (T : Scheme.{u}) :
    Etale.supportCoefficientMate
        (constantSheafΓAdj T.smallEtaleTopology (ModuleCat.{u + 1} A))
        (constantSheafΓAdj (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A))
        (comparisonUpperStar (ModuleCat.{u + 1} A) T) (globalComparisonUnit A T) =
      (constantComparison A T).inv := by
  let ae := constantSheafΓAdj T.smallEtaleTopology (ModuleCat.{u + 1} A)
  let ap := constantSheafΓAdj (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A)
  let ac := (ae.comp (comparisonAdjunction (ModuleCat.{u + 1} A) T)).ofNatIsoRight
    (comparisonLowerStarCompGlobalSectionsIso (ModuleCat.{u + 1} A) T)
  apply NatTrans.ext
  funext M
  apply (ap.homEquiv _ _).injective
  rw [Etale.supportMate_unit]
  have hn := Adjunction.homEquiv_leftAdjointUniq_hom_app ap ac M
  rw [← Adjunction.leftAdjointUniq_inv_app] at hn
  change ap.homEquiv _ _ ((constantComparison A T).inv.app M) = ac.unit.app M at hn
  rw [hn]
  rfl

private lemma comparison_support_forget (A : Type (u + 1)) [CommRing A]
    {C T : Scheme.{u}} (i : C ⟶ T) [IsClosedImmersion i]
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    (((supportKernelEvaluationIso A i).hom ≫ supportComparisonUnit A i).app F) ≫
      (supportedModuleSectionsι A i).app
        ((comparisonUpperStar (ModuleCat.{u + 1} A) T).obj F) =
      (Etale.supportedEtaleSectionsι A T i.openComplement).app F ≫
        (Sheaf.Γ T.smallEtaleTopology (ModuleCat.{u + 1} A)).map
          ((comparisonAdjunction (ModuleCat.{u + 1} A) T).unit.app F) ≫
        (comparisonLowerStarCompGlobalSectionsIso (ModuleCat.{u + 1} A) T).hom.app
          ((comparisonUpperStar (ModuleCat.{u + 1} A) T).obj F) := by
  have he := NatTrans.congr_app (supportKernelEvaluationIso_existsUnique A i).choose_spec.1 F
  have hu := (supportComparisonUnit_existsUnique A i).choose_spec.1 F
  dsimp only [NatTrans.comp_app] at he hu ⊢
  change (supportKernelEvaluationIso A i).hom.app F ≫
    (supportComparisonUnit A i).app F ≫ kernel.ι _ ≫ _ = _
  erw [reassoc_of% hu, ← Category.assoc, he]
  simp only [Category.assoc]
  dsimp only [comparisonLowerStarCompGlobalSectionsIso, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Iso.symm_hom]
  congr 1
  rw [← Category.assoc]
  have hn := (Sheaf.ΓNatIsoSheafSections T.smallEtaleTopology (ModuleCat.{u + 1} A)
    (Scheme.Etale.isTerminalMkId T)).hom.naturality
      ((comparisonAdjunction (ModuleCat.{u + 1} A) T).unit.app F)
  exact congrArg (fun t ↦ t ≫ _) hn.symm

private lemma coefficientComparison_quotient (A : Type (u + 1)) [CommRing A] [Finite A]
    {C T : Scheme.{u}} (i : C ⟶ T) [IsClosedImmersion i] [IsLocallyNoetherian T]
    (M : ModuleCat.{u + 1} A) :
    supportedCoefficientQuotient A i M ≫ (coefficientComparison A i).inv.app M =
      (constantComparison A T).inv.app M ≫
        (comparisonUpperStar (ModuleCat.{u + 1} A) T).map
          (Etale.supportedCoefficientQuotient A i M) := by
  rw [← comparisonMate_eq, ← constantComparisonMate_eq]
  apply quotient_mate_normalized (Etale.supportedCoefficientAdjunction A i)
    (supportedCoefficientAdjunction A i)
    (constantSheafΓAdj T.smallEtaleTopology (ModuleCat.{u + 1} A))
    (constantSheafΓAdj (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A))
    (comparisonUpperStar (ModuleCat.{u + 1} A) T)
    ((supportKernelEvaluationIso A i).hom ≫ supportComparisonUnit A i)
    (globalComparisonUnit A T)
    (Etale.supportedEtaleSectionsι A T i.openComplement) (supportedModuleSectionsι A i)
  · apply NatTrans.ext
    funext F
    exact comparison_support_forget A i F
  · exact (Etale.exists_unique_supportedCoefficientAdjunction A i).choose_spec.1 M
  · exact (exists_unique_supportedCoefficientAdjunction A i).choose_spec.1 M

end CoefficientNormalization


section ExteriorComparisonProof
attribute [local instance] canonicalConstantEt canonicalConstantPro
universe w
open MonoidalCategory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true
set_option backward.defeqAttrib.useBackward true
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
attribute [local instance] supportedCoefficients_isLeftAdjoint
attribute [-instance] supportedSheaf_isMonoidal supportedSheaf_monoidalPreadditive
  supportedSheaf_isMonoidalGeneric supportedSheaf_monoidalPreadditiveGeneric

private lemma projectedQuotient
    {C C' D D' : Type*} [Category C] [Category C'] [Category D] [Category D']
    (P : C ⥤ C') (Q : D ⥤ D') (H : C ⥤ D) (J : C' ⥤ D')
    (e : P ⋙ J ≅ H ⋙ Q)
    {V W : C} {V' : C'} {K L : D} {K' : D'}
    (q : V ⟶ W) (q' : K ⟶ L)
    (c : P.obj V ≅ V') (d : Q.obj K ≅ K')
    (σ : K ⟶ H.obj V) (σ' : K' ⟶ J.obj V') (a : L ⟶ H.obj W)
    (hq : q' ≫ a = σ ≫ H.map q)
    (hc : d.inv ≫ Q.map σ = σ' ≫ J.map c.inv ≫ e.hom.app V) :
    (d.inv ≫ Q.map q') ≫ (Q.map a ≫ e.inv.app W) =
      σ' ≫ J.map (c.inv ≫ P.map q) := by
  simp only [Category.assoc]
  rw [← Q.map_comp_assoc, hq, Q.map_comp]
  simp only [Category.assoc]
  rw [reassoc_of% hc]
  have hn := e.hom.naturality q
  simp only [Functor.comp_map] at hn
  rw [← reassoc_of% hn]
  simp only [Iso.hom_inv_id_app, Functor.map_comp]
  simp only [Functor.comp_obj, Category.comp_id]

open MonoidalCategory
private lemma monoidalCompositeSquare
    {C D E : Type*} [Category C] [Category D] [Category E]
    [MonoidalCategory C] [MonoidalCategory D] [MonoidalCategory E]
    (F : C ⥤ D) (G : C ⥤ E) (H : D ⥤ E)
    [F.Monoidal] [G.Monoidal] [H.Monoidal]
    (e : F ⋙ H ≅ G) [NatTrans.IsMonoidal e.inv] (M N : C) :
    e.inv.app (M ⊗ N) ≫ H.map (Functor.OplaxMonoidal.δ F M N) ≫
        Functor.OplaxMonoidal.δ H (F.obj M) (F.obj N) =
      Functor.OplaxMonoidal.δ G M N ≫ (e.inv.app M ⊗ₘ e.inv.app N) := by
  apply (cancel_epi (Functor.LaxMonoidal.μ G M N)).mp
  have hm := NatTrans.IsMonoidal.tensor (τ := e.inv) M N
  dsimp only [Functor.LaxMonoidal.comp_μ] at hm
  rw [← Category.assoc, ← Category.assoc, hm]
  simp only [Category.assoc]
  rw [← Functor.map_comp_assoc, Functor.Monoidal.μ_δ]
  rw [CategoryTheory.Functor.map_id, Category.id_comp]
  erw [Functor.Monoidal.μ_δ_assoc, Functor.Monoidal.μ_δ, Category.comp_id]

namespace CachedConstantCoherence
attribute [local instance] canonicalConstantEt canonicalConstantPro
private lemma comparison_tensor
    (D : Type v₁) [Category.{u + 1} D] [Abelian D]
    [IsGrothendieckAbelian.{u + 1} D] [HasSmallSiteSheafify D]
    [MonoidalCategory D] [MonoidalPreadditive D] [SymmetricCategory D]
    [MonoidalClosed D] [Abelian.HasFunctorialFlatResolution D]
    (T : Scheme.{u}) (M N : D) :
    (constantComparison D T).inv.app (M ⊗ N) ≫
        (comparisonUpperStar D T).map
          (Functor.OplaxMonoidal.δ (constantSheaf T.smallEtaleTopology D) M N) ≫
        Functor.OplaxMonoidal.δ (comparisonUpperStar D T)
          ((constantSheaf T.smallEtaleTopology D).obj M)
          ((constantSheaf T.smallEtaleTopology D).obj N) =
      Functor.OplaxMonoidal.δ (constantSheaf (Scheme.ProEt.topology T) D) M N ≫
        ((constantComparison D T).inv.app M ⊗ₘ (constantComparison D T).inv.app N) := by
  rw [constantComparison_eq_terminal]
  let : NatTrans.IsMonoidal (constantComparisonTerminal D T).inv :=
    constantComparisonTerminal_monoidal D T
  exact monoidalCompositeSquare (constantSheaf T.smallEtaleTopology D)
    (constantSheaf (Scheme.ProEt.topology T) D)
    (comparisonUpperStar D T) (constantComparisonTerminal D T) M N
end CachedConstantCoherence

private lemma proConstantTensor_eq
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (T : Scheme.{u}) (M N : ModuleCat.{u + 1} A) :
    supportedConstantTensor A T M N =
      Functor.OplaxMonoidal.δ
        (constantSheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A)) M N := by
  rfl

private lemma constantComparison_tensor
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (T : Scheme.{u}) (M N : ModuleCat.{u + 1} A) :
    (constantComparison A T).inv.app (M ⊗ N) ≫
        (comparisonUpperStar (ModuleCat.{u + 1} A) T).map
          (Etale.supportedConstantTensor A T M N) ≫
        Functor.OplaxMonoidal.δ (comparisonUpperStar (ModuleCat.{u + 1} A) T)
          ((constantSheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)).obj M)
          ((constantSheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)).obj N) =
      supportedConstantTensor A T M N ≫
        ((constantComparison A T).inv.app M ⊗ₘ (constantComparison A T).inv.app N) := by
  rw [Etale.constantTensor_eq, proConstantTensor_eq]
  exact CachedConstantCoherence.comparison_tensor (ModuleCat.{u + 1} A) T M N

private noncomputable def projectedCoefficientComparison
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {C X P : Scheme.{u}} (i : C ⟶ X) [IsClosedImmersion i]
    [IsLocallyNoetherian X] (p : P ⟶ X) :
    supportedCoefficients A i ⋙ upperStar (ModuleCat.{u + 1} A) p ⟶
      (Etale.supportedCoefficients A i ⋙ Etale.upperStar (ModuleCat.{u + 1} A) p) ⋙
        comparisonUpperStar (ModuleCat.{u + 1} A) P :=
  Functor.whiskerRight (coefficientComparison A i).inv (upperStar (ModuleCat.{u + 1} A) p) ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (Etale.supportedCoefficients A i)
      (supportSiteComparisonCoefficientPullbackIso (ModuleCat.{u + 1} A) p).inv ≫
    (Functor.associator _ _ _).inv

private lemma projectedCoefficientComparison_quotient
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {C X P : Scheme.{u}} (i : C ⟶ X) [IsClosedImmersion i]
    [IsLocallyNoetherian X] (p : P ⟶ X) (M : ModuleCat.{u + 1} A) :
    ((constantSheafCompUpperStarIso (ModuleCat.{u + 1} A) p).inv.app M ≫
        (upperStar (ModuleCat.{u + 1} A) p).map (supportedCoefficientQuotient A i M)) ≫
        (projectedCoefficientComparison A i p).app M =
      (constantComparison A P).inv.app M ≫
        (comparisonUpperStar (ModuleCat.{u + 1} A) P).map
          ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) p).inv.app M ≫
            (Etale.upperStar (ModuleCat.{u + 1} A) p).map
              (Etale.supportedCoefficientQuotient A i M)) := by
  exact projectedQuotient (Etale.upperStar (ModuleCat.{u + 1} A) p)
    (upperStar (ModuleCat.{u + 1} A) p)
    (comparisonUpperStar (ModuleCat.{u + 1} A) X)
    (comparisonUpperStar (ModuleCat.{u + 1} A) P)
    (supportSiteComparisonCoefficientPullbackIso (ModuleCat.{u + 1} A) p)
    (Etale.supportedCoefficientQuotient A i M) (supportedCoefficientQuotient A i M)
    ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) p).app M)
    ((constantSheafCompUpperStarIso (ModuleCat.{u + 1} A) p).app M)
    ((constantComparison A X).inv.app M) ((constantComparison A P).inv.app M)
    ((coefficientComparison A i).inv.app M)
    (coefficientComparison_quotient A i M) (constantComparison_square_inv A p M)

private lemma coefficientComparison_tensor
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {S X Y Z W : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (i : Z ⟶ X) (j : W ⟶ Y) [IsClosedImmersion i] [IsClosedImmersion j]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsLocallyNoetherian (pullback f g)]
    (M N : ModuleCat.{u + 1} A) :
    (coefficientComparison A (Etale.supportedProductImmersion f g i j)).inv.app (M ⊗ N) ≫
        (comparisonUpperStar (ModuleCat.{u + 1} A) (pullback f g)).map
          (Etale.supportedCoefficientTensor A f g i j M N) ≫
        Functor.OplaxMonoidal.δ
          (comparisonUpperStar (ModuleCat.{u + 1} A) (pullback f g))
          ((Etale.supportedFirstCoefficients A f g i).obj M)
          ((Etale.supportedSecondCoefficients A f g j).obj N) =
      supportedCoefficientTensor A f g i j M N ≫
        ((projectedCoefficientComparison A i (pullback.fst f g)).app M ⊗ₘ
          (projectedCoefficientComparison A j (pullback.snd f g)).app N) := by
  let := coefficientQuotient_epi A (Etale.supportedProductImmersion f g i j) (M ⊗ N)
  exact Etale.tensorSquare_of_quotients
    (comparisonUpperStar (ModuleCat.{u + 1} A) (pullback f g))
    (Etale.supportedCoefficientQuotient A (Etale.supportedProductImmersion f g i j) (M ⊗ N))
    (Etale.supportFirstOrdinaryCoefficientQuotient A f g i M)
    (Etale.supportSecondOrdinaryCoefficientQuotient A f g j N)
    (supportedCoefficientQuotient A (Etale.supportedProductImmersion f g i j) (M ⊗ N))
    ((firstCoefficientQuotientNat A f g i).app M)
    ((secondCoefficientQuotientNat A f g j).app N)
    ((constantComparison A (pullback f g)).inv.app (M ⊗ N))
    ((constantComparison A (pullback f g)).inv.app M)
    ((constantComparison A (pullback f g)).inv.app N)
    ((coefficientComparison A (Etale.supportedProductImmersion f g i j)).inv.app (M ⊗ N))
    ((projectedCoefficientComparison A i (pullback.fst f g)).app M)
    ((projectedCoefficientComparison A j (pullback.snd f g)).app N)
    (Etale.supportedCoefficientTensor A f g i j M N)
    (supportedCoefficientTensor A f g i j M N)
    (Etale.supportedConstantTensor A (pullback f g) M N)
    (supportedConstantTensor A (pullback f g) M N)
    (Etale.coefficientTensor_quotient A f g i j M N)
    (coefficientTensor_spec A f g i j M N)
    (constantComparison_tensor A (pullback f g) M N)
    (coefficientComparison_quotient A (Etale.supportedProductImmersion f g i j) (M ⊗ N))
    (projectedCoefficientComparison_quotient A i (pullback.fst f g) M)
    (projectedCoefficientComparison_quotient A j (pullback.snd f g) N)

private lemma exactMapNormalized
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    (F : C ⥤ D) (H : D ⥤ E) (F' : C ⥤ E)
    [F.Additive] [H.Additive] [F'.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    [PreservesFiniteLimits F'] [PreservesFiniteColimits F']
    (α : F' ⟶ F ⋙ H) :
    mapNatNormalization F H F' α
      (Functor.exactDerivedMap α ≫ (Functor.mapDerivedCategoryCompIso F H).hom) := by
  apply comp_facQ_normalized_of_fach
  intro K
  simp only [NatTrans.comp_app, Category.assoc]
  rw [Functor.mapDerivedCategoryCompIso_hom_app_factorsh,
    AlgebraicGeometry.Etale.exactMap_fac]

section
variable {C D : Type*} [Category.{w + 1} C] [Category.{w + 1} D]
  [Abelian C] [Abelian D]
  [IsGrothendieckAbelian.{w + 1} C] [IsGrothendieckAbelian.{w + 1} D]
  [MonoidalCategory C] [MonoidalCategory D]
  [MonoidalPreadditive C] [MonoidalPreadditive D]
  [SymmetricCategory C] [SymmetricCategory D] [MonoidalClosed C] [MonoidalClosed D]
  [Abelian.HasFunctorialFlatResolution C] [Abelian.HasFunctorialFlatResolution D]
  (H : C ⥤ D) [H.Additive] [H.Monoidal] [H.PreservesFlat] [H.IsLeftAdjoint]
  [PreservesFiniteLimits H] [PreservesFiniteColimits H]
private noncomputable def exactTensor :=
  conjugateTensor H.leftDerivedFunctor H.mapDerivedCategory
    H.leftDerivedFunctorIsoMapDerivedCategory H.leftDerivedTensorComparison

private lemma exactTensor_fac_h :
    tensorNormalization DerivedCategory.Qh DerivedCategory.Qh
      (H.mapHomotopyCategory (.up ℤ)) (H.mapHomotopyCategory (.up ℤ))
      (H.mapHomotopyCategory (.up ℤ))
      H.mapDerivedCategory H.mapDerivedCategory H.mapDerivedCategory
      H.mapDerivedCategoryFactorsh.hom H.mapDerivedCategoryFactorsh.hom
      H.mapDerivedCategoryFactorsh.hom
      (fun P Q ↦ Functor.OplaxMonoidal.δ (H.mapHomotopyCategory (.up ℤ)) P Q)
      (fun M N ↦ ((exactTensor H).app M).app N) := by
  unfold tensorNormalization
  intro P Q
  exact conjugateTensor_fac DerivedCategory.Qh DerivedCategory.Qh
    (H.mapHomotopyCategory (.up ℤ)) H.leftDerivedFunctor H.mapDerivedCategory
    H.leftDerivedFunctorIsoMapDerivedCategory H.leftDerivedFunctorCounit
    H.mapDerivedCategoryFactorsh.hom
    (fun R ↦ NatTrans.congr_app (Functor.leftDerivedFunctorIsoMapDerivedCategory_hom_fac H) R)
    H.leftDerivedTensorComparison
    (fun R V ↦ Functor.OplaxMonoidal.δ (H.mapHomotopyCategory (.up ℤ)) R V)
    (Functor.leftDerivedTensorComparison_app_app_comp_tensorHom H) P Q

private lemma exactTensor_fac :
    tensorNatNormalization H H H
      (Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans (.up ℤ) H) (exactTensor H) := by
  unfold tensorNatNormalization
  exact tensor_facQ_normalized H (exactTensor H) (exactTensor_fac_h H)
end

section NativeTensorConstruction
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.leftDerivedFunctor
section
variable {C D : Type*} [Category.{w + 1} C] [Category.{w + 1} D]
  [Abelian C] [Abelian D]
  [IsGrothendieckAbelian.{w + 1} C] [IsGrothendieckAbelian.{w + 1} D]
  [HasDerivedCategory.{w + 1} C] [HasDerivedCategory.{w + 1} D]
  [MonoidalCategory C] [MonoidalCategory D]
  [MonoidalPreadditive C] [MonoidalPreadditive D]
  [BraidedCategory C] [BraidedCategory D] [MonoidalClosed C] [MonoidalClosed D]
  [Abelian.HasFunctorialFlatResolution C] [Abelian.HasFunctorialFlatResolution D]
  (G F₁ F₂ : C ⥤ D) [G.Additive] [F₁.Additive] [F₂.Additive]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
  [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂]
private noncomputable def natFromFamily
    (s : ∀ P Q, SupportedTensorDerivation.ComplexHom G F₁ F₂ P Q)
    (t : SupportedTensorDerivation.ComparisonHom G F₁ F₂)
    (h : SupportedTensorDerivation.ComparisonFamilyCondition G F₁ F₂ s t) :=
  comparisonNatTrans G.mapDerivedCategory F₁.mapDerivedCategory F₂.mapDerivedCategory t
    (by
      intro M M' N N' a b
      simpa only [MonoidalCategory.tensorHom_def, curriedTensor_map_app,
        curriedTensor_obj_map, Category.assoc] using h.1 M M' N N' a b)
end
private lemma transferDerivedCondition
    {C D : Type*} [Category.{w + 1} C] [Category.{w + 1} D]
    [Abelian C] [Abelian D]
    [IsGrothendieckAbelian.{w + 1} C] [IsGrothendieckAbelian.{w + 1} D]
    [HasDerivedCategory.{w + 1} C] [HasDerivedCategory.{w + 1} D]
    [MonoidalCategory C] [MonoidalCategory D]
    [MonoidalPreadditive C] [MonoidalPreadditive D]
    [SymmetricCategory C] [SymmetricCategory D] [MonoidalClosed C] [MonoidalClosed D]
    [Abelian.HasFunctorialFlatResolution C] [Abelian.HasFunctorialFlatResolution D]
    (G F₁ F₂ : C ⥤ D) [G.Additive] [F₁.Additive] [F₂.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
    [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂]
    (τ : (Functor.postcompose₂.obj (G.mapHomologicalComplex (.up ℤ))).obj
        (curriedTensor (CochainComplex C ℤ)) ⟶
      (((Functor.whiskeringLeft₂ _).obj (F₁.mapHomologicalComplex (.up ℤ))).obj
        (F₂.mapHomologicalComplex (.up ℤ))).obj (curriedTensor _))
    (t : SupportedTensorDerivation.ComparisonHom G F₁ F₂)
    (h : SupportedTensorDerivation.ComparisonCondition G F₁ F₂ τ t) :
    AlgebraicGeometry.Etale.supportedDerivedComparisonCondition G F₁ F₂ τ t := by
  simpa only [SupportedTensorDerivation.ComparisonCondition,
    SupportedTensorDerivation.ComparisonFamilyCondition,
    AlgebraicGeometry.Etale.supportedDerivedComparisonCondition,
    MonoidalCategory.tensorHom_def, curriedTensor_map_app, curriedTensor_obj_map,
    Functor.comp_obj] using h

section
variable {C D : Type*} [Category.{w + 1} C] [Category.{w + 1} D]
  [Abelian C] [Abelian D]
  [IsGrothendieckAbelian.{w + 1} C] [IsGrothendieckAbelian.{w + 1} D]
  [HasDerivedCategory.{w + 1} C] [HasDerivedCategory.{w + 1} D]
  [MonoidalCategory C] [MonoidalCategory D]
  [MonoidalPreadditive C] [MonoidalPreadditive D]
  [SymmetricCategory C] [SymmetricCategory D] [MonoidalClosed C] [MonoidalClosed D]
  [Abelian.HasFunctorialFlatResolution C] [Abelian.HasFunctorialFlatResolution D]
  (G F₁ F₂ : C ⥤ D) [G.Additive] [F₁.Additive] [F₂.Additive]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
  [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂]
private lemma natFromFamily_normalized
    (τ : (Functor.postcompose₂.obj (G.mapHomologicalComplex (.up ℤ))).obj
        (curriedTensor (CochainComplex C ℤ)) ⟶
      (((Functor.whiskeringLeft₂ _).obj (F₁.mapHomologicalComplex (.up ℤ))).obj
        (F₂.mapHomologicalComplex (.up ℤ))).obj (curriedTensor _))
    (s : ∀ P Q, SupportedTensorDerivation.ComplexHom G F₁ F₂ P Q)
    (hs : s = fun P Q ↦ (τ.app P).app Q)
    (t : SupportedTensorDerivation.ComparisonHom G F₁ F₂)
    (h : SupportedTensorDerivation.ComparisonFamilyCondition G F₁ F₂ s t) :
    tensorNatNormalization G F₁ F₂ τ (natFromFamily G F₁ F₂ s t h) := by
  subst s
  exact comparisonFromCondition_normalized G F₁ F₂ τ t
    (transferDerivedCondition G F₁ F₂ τ t h)
end
section NativeProTensor
variable (D : Type v₁) [Category.{u + 1} D] [Abelian D]
    [IsGrothendieckAbelian.{u + 1} D] [MonoidalCategory D] [MonoidalPreadditive D]
    [SymmetricCategory D] [MonoidalClosed D] [Abelian.HasFunctorialFlatResolution D]
    (X : Scheme.{u})
    (G F₁ F₂ : D ⥤ Sheaf (Scheme.ProEt.topology X) D)
    [G.Additive] [F₁.Additive] [F₂.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
    [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂]
private noncomputable def nativeProNat
    (s : ∀ P Q, SupportedTensorDerivation.ComplexHom G F₁ F₂ P Q)
    (t : SupportedTensorDerivation.ComparisonHom G F₁ F₂)
    (h : SupportedTensorDerivation.ComparisonFamilyCondition G F₁ F₂ s t) :
    (Functor.postcompose₂.obj G.mapDerivedCategory).obj (curriedTensor (DerivedCategory D)) ⟶
      (((Functor.whiskeringLeft₂ _).obj F₁.mapDerivedCategory).obj F₂.mapDerivedCategory).obj
        (derivedTensor D X) :=
  natFromFamily G F₁ F₂ s t h
private lemma nativeProNat_app
    (s : ∀ P Q, SupportedTensorDerivation.ComplexHom G F₁ F₂ P Q)
    (t : SupportedTensorDerivation.ComparisonHom G F₁ F₂)
    (h : SupportedTensorDerivation.ComparisonFamilyCondition G F₁ F₂ s t)
    (M N : DerivedCategory D) :
    ((nativeProNat D X G F₁ F₂ s t h).app M).app N =
      (cast (SupportedTensorDerivation.comparisonHom_tensor G F₁ F₂ (derivedTensor D X)
        (normalization_tensorHom_eq D X)) t) M N := by
  rfl
private lemma nativeProNat_normalized
    (τ : (Functor.postcompose₂.obj (G.mapHomologicalComplex (.up ℤ))).obj
        (curriedTensor (CochainComplex D ℤ)) ⟶
      (((Functor.whiskeringLeft₂ _).obj (F₁.mapHomologicalComplex (.up ℤ))).obj
        (F₂.mapHomologicalComplex (.up ℤ))).obj (curriedTensor _))
    (s : ∀ P Q, SupportedTensorDerivation.ComplexHom G F₁ F₂ P Q)
    (hs : s = fun P Q ↦ (τ.app P).app Q)
    (t : SupportedTensorDerivation.ComparisonHom G F₁ F₂)
    (h : SupportedTensorDerivation.ComparisonFamilyCondition G F₁ F₂ s t) :
    tensorNatNormalization G F₁ F₂ τ (nativeProNat D X G F₁ F₂ s t h) := by
  exact natFromFamily_normalized G F₁ F₂ τ s hs t h
end NativeProTensor
private noncomputable def proCoefficientDerivedNat
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {S X Y Z W : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (i : Z ⟶ X) (j : W ⟶ Y) [IsClosedImmersion i] [IsClosedImmersion j]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsLocallyNoetherian (pullback f g)] :=
  nativeProNat (ModuleCat.{u + 1} A) (pullback f g)
    (supportedCoefficients A (Etale.supportedProductImmersion f g i j))
    (supportedFirstCoefficients A f g i) (supportedSecondCoefficients A f g j)
    (supportedCoefficientTensorComplex A f g i j)
    (exists_unique_supportedCoefficientTensorDerived A f g i j).choose
    (exists_unique_supportedCoefficientTensorDerived A f g i j).choose_spec.1
private lemma proCoefficientDerivedNat_app
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {S X Y Z W : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (i : Z ⟶ X) (j : W ⟶ Y) [IsClosedImmersion i] [IsClosedImmersion j]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsLocallyNoetherian (pullback f g)]
    (M N : DerivedCategory (ModuleCat.{u + 1} A)) :
    ((proCoefficientDerivedNat A f g i j).app M).app N =
      supportedCoefficientTensorDerived A f g i j M N := by
  unfold proCoefficientDerivedNat
  erw [nativeProNat_app]
  rfl
end NativeTensorConstruction

private noncomputable def projectedDerivedCoefficientComparison
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {C X P : Scheme.{u}} (i : C ⟶ X) [IsClosedImmersion i]
    [IsLocallyNoetherian X] (p : P ⟶ X) :=
  squareCoefficient (Etale.supportedCoefficients A i) (supportedCoefficients A i)
    (comparisonUpperStar (ModuleCat.{u + 1} A) X)
    (Etale.upperStar (ModuleCat.{u + 1} A) p)
    (upperStar (ModuleCat.{u + 1} A) p)
    (comparisonUpperStar (ModuleCat.{u + 1} A) P)
    (supportSiteComparisonCoefficientPullbackIso (ModuleCat.{u + 1} A) p).symm
    (Etale.supportCoefficientMate (Etale.supportedCoefficientDerivedAdjunction A i)
      (supportedCoefficientDerivedAdjunction A i)
      (comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory
      (Functor.rightDerivedPullback (comparisonUpperStar (ModuleCat.{u + 1} A) X)
        ((supportKernelEvaluationIso A i).hom ≫ supportComparisonUnit A i)))

private lemma projectedDerivedCoefficientComparison_normalized
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {C X P : Scheme.{u}} (i : C ⟶ X) [IsClosedImmersion i]
    [IsLocallyNoetherian X] (p : P ⟶ X) :
    mapNatNormalization
      (Etale.supportedCoefficients A i ⋙ Etale.upperStar (ModuleCat.{u + 1} A) p)
      (comparisonUpperStar (ModuleCat.{u + 1} A) P)
      (supportedCoefficients A i ⋙ upperStar (ModuleCat.{u + 1} A) p)
      (projectedCoefficientComparison A i p) (projectedDerivedCoefficientComparison A i p) := by
  apply squareCoefficient_normalized
  rw [derivedComparisonMate_eq]
  exact exactMapNormalized _ _ _ _

private noncomputable def comparisonLeftPullbackIso
    (A : Type (u + 1)) [CommRing A] {P X : Scheme.{u}} (p : P ⟶ X) :
    (Etale.upperStar (ModuleCat.{u + 1} A) p).leftDerivedFunctor ⋙
        (comparisonUpperStar (ModuleCat.{u + 1} A) P).mapDerivedCategory ≅
      (comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory ⋙
        (upperStar (ModuleCat.{u + 1} A) p).leftDerivedFunctor :=
  Functor.isoWhiskerRight
      (Etale.leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) p)
      (comparisonUpperStar (ModuleCat.{u + 1} A) P).mapDerivedCategory ≪≫
    supportDerivedPullbackIso A p ≪≫
    Functor.isoWhiskerLeft (comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) p).symm

private noncomputable def proCoefficientProjectionIso
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {C X P : Scheme.{u}} (i : C ⟶ X) (p : P ⟶ X) [IsClosedImmersion i] [IsLocallyNoetherian X] :
    (supportedCoefficients A i ⋙ upperStar (ModuleCat.{u + 1} A) p).mapDerivedCategory ≅
      (supportedCoefficients A i).mapDerivedCategory ⋙
        (upperStar (ModuleCat.{u + 1} A) p).leftDerivedFunctor :=
  Functor.mapDerivedCategoryCompIso (supportedCoefficients A i)
      (upperStar (ModuleCat.{u + 1} A) p) ≪≫
    Functor.isoWhiskerLeft (supportedCoefficients A i).mapDerivedCategory
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) p).symm

private lemma exactTensor_comparison_app
    (D : Type v₁) [Category.{u + 1} D] [Abelian D]
    [IsGrothendieckAbelian.{u + 1} D] [MonoidalCategory D] [MonoidalPreadditive D]
    [SymmetricCategory D] [MonoidalClosed D] [Abelian.HasFunctorialFlatResolution D]
    (T : Scheme.{u}) [(comparisonUpperStar D T).PreservesFlat]
    (M N : DerivedCategory (Sheaf T.smallEtaleTopology D)) :
    ((exactTensor (comparisonUpperStar D T)).app M).app N =
      (supportDerivedComparisonTensorIso D T M N).hom := by
  rw [exactTensor, conjugateTensor_app]
  simp only [supportDerivedComparisonTensorIso, supportBifunctorIso,
    Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Functor.mapIso_hom,
    MonoidalCategory.tensorHom_def]
  rfl

section
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
private theorem schemeTensorSquareResult
  (D : Type v₁) [Category.{u + 1} D] [Abelian D]
  [IsGrothendieckAbelian.{u + 1} D] [MonoidalCategory D] [MonoidalPreadditive D]
  [SymmetricCategory D] [MonoidalClosed D] [Abelian.HasFunctorialFlatResolution D]
  (T : Scheme.{u}) [(comparisonUpperStar D T).PreservesFlat]
  (G F₁ F₂ : D ⥤ Sheaf T.smallEtaleTopology D)
  (G₀ F₁₀ F₂₀ : D ⥤ Sheaf (Scheme.ProEt.topology T) D)
  [G.Additive] [F₁.Additive] [F₂.Additive]
  [G₀.Additive] [F₁₀.Additive] [F₂₀.Additive]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
  [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂]
  [PreservesFiniteLimits G₀] [PreservesFiniteColimits G₀]
  [PreservesFiniteLimits F₁₀] [PreservesFiniteColimits F₁₀]
  [PreservesFiniteLimits F₂₀] [PreservesFiniteColimits F₂₀]
  [G.IsLeftAdjoint] [G₀.IsLeftAdjoint]
  [hflat : (F₂ ⋙ (comparisonUpperStar D T)).PreservesFlat]
  [hadj : (F₂ ⋙ (comparisonUpperStar D T)).IsLeftAdjoint]
    (τ : (Functor.postcompose₂.obj G).obj (curriedTensor D) ⟶
      (((Functor.whiskeringLeft₂ _).obj F₁).obj F₂).obj (curriedTensor _))
    (τ₀ : (Functor.postcompose₂.obj G₀).obj (curriedTensor D) ⟶
      (((Functor.whiskeringLeft₂ _).obj F₁₀).obj F₂₀).obj (curriedTensor _))
    (a₀ : G₀ ⟶ G ⋙ (comparisonUpperStar D T))
    (a₁ : F₁₀ ⟶ F₁ ⋙ (comparisonUpperStar D T))
    (a₂ : F₂₀ ⟶ F₂ ⋙ (comparisonUpperStar D T))
    (da₀ : G₀.mapDerivedCategory ⟶
      G.mapDerivedCategory ⋙ (comparisonUpperStar D T).mapDerivedCategory)
    (da₁ : F₁₀.mapDerivedCategory ⟶
      F₁.mapDerivedCategory ⋙ (comparisonUpperStar D T).mapDerivedCategory)
    (da₂ : F₂₀.mapDerivedCategory ⟶
      F₂.mapDerivedCategory ⋙ (comparisonUpperStar D T).mapDerivedCategory)
    (t : (Functor.postcompose₂.obj G.mapDerivedCategory).obj (curriedTensor _) ⟶
      (((Functor.whiskeringLeft₂ _).obj F₁.mapDerivedCategory).obj
        F₂.mapDerivedCategory).obj (Etale.derivedTensor D T))
    (s₀ : ∀ P Q, SupportedTensorDerivation.ComplexHom G₀ F₁₀ F₂₀ P Q)
    (hs₀ : s₀ = fun P Q ↦
      SupportedTensorDerivation.ComplexComparison G₀ F₁₀ F₂₀ τ₀ P Q)
    (t₀ : SupportedTensorDerivation.ComparisonHom G₀ F₁₀ F₂₀)
    (ht₀ : SupportedTensorDerivation.ComparisonFamilyCondition G₀ F₁₀ F₂₀ s₀ t₀)
    (ht : tensorNatNormalization G F₁ F₂
      (Etale.supportedComplexComparisonNatTrans G F₁ F₂ τ) t)
    (ha₀ : mapNatNormalization G (comparisonUpperStar D T) G₀ a₀ da₀)
    (ha₁ : mapNatNormalization F₁ (comparisonUpperStar D T) F₁₀ a₁ da₁)
    (ha₂ : mapNatNormalization F₂ (comparisonUpperStar D T) F₂₀ a₂ da₂)
    (hs : ∀ M N, a₀.app (M ⊗ N) ≫
      (comparisonUpperStar D T).map ((τ.app M).app N) ≫
      Functor.OplaxMonoidal.δ (comparisonUpperStar D T) (F₁.obj M) (F₂.obj N) =
      (τ₀.app M).app N ≫ (a₁.app M ⊗ₘ a₂.app N))
    (M N : DerivedCategory D) :
    da₀.app (M ⊗ N) ≫ (comparisonUpperStar D T).mapDerivedCategory.map ((t.app M).app N) ≫
        (supportDerivedComparisonTensorIso D T
          (F₁.mapDerivedCategory.obj M) (F₂.mapDerivedCategory.obj N)).hom =
      ((nativeProNat D T G₀ F₁₀ F₂₀ s₀ t₀ ht₀).app M).app N ≫
        Etale.bifunctorMap (derivedTensor D T) (da₁.app M) (da₂.app N) := by
  let : (F₂ ⋙ (comparisonUpperStar D T)).PreservesFlat := hflat
  let : (F₂ ⋙ (comparisonUpperStar D T)).IsLeftAdjoint := hadj
  have hs₀' : s₀ = fun P Q ↦
      ((Etale.supportedComplexComparisonNatTrans G₀ F₁₀ F₂₀ τ₀).app P).app Q := hs₀
  have hsq := derived_square G F₁ F₂ G₀ F₁₀ F₂₀ (comparisonUpperStar D T) τ τ₀ a₀ a₁ a₂
    da₀ da₁ da₂ t
    (nativeProNat D T G₀ F₁₀ F₂₀ s₀ t₀ ht₀) (exactTensor (comparisonUpperStar D T)) ht
    (nativeProNat_normalized D T G₀ F₁₀ F₂₀ _ s₀ hs₀' t₀ ht₀)
    (exactTensor_fac (comparisonUpperStar D T)) ha₀ ha₁ ha₂
    (Etale.supportedTensorComplex_square G F₁ F₂ G₀ F₁₀ F₂₀
      (comparisonUpperStar D T) τ τ₀ a₀ a₁ a₂ hs)
  have he := square_equality_app _ _ _ _ _ _ _ _ _ _ _ _ _ hsq M N
  rw [exactTensor_comparison_app] at he
  simpa only [Etale.bifunctorMap, derivedTensor, Etale.derivedTensor,
    curriedTensor_map_app, curriedTensor_obj_map, MonoidalCategory.tensorHom_def,
    Category.assoc] using he
end

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private lemma coefficientComparison_derived_tensor
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {S X Y Z W : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (i : Z ⟶ X) (j : W ⟶ Y) [IsClosedImmersion i] [IsClosedImmersion j]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsLocallyNoetherian (pullback f g)]
    (M N : DerivedCategory (ModuleCat.{u + 1} A)) :
    (Etale.supportCoefficientMate
        (Etale.supportedCoefficientDerivedAdjunction A (Etale.supportedProductImmersion f g i j))
        (supportedCoefficientDerivedAdjunction A (Etale.supportedProductImmersion f g i j))
        (comparisonUpperStar (ModuleCat.{u + 1} A) (pullback f g)).mapDerivedCategory
        (Functor.rightDerivedPullback (comparisonUpperStar (ModuleCat.{u + 1} A) (pullback f g))
          ((supportKernelEvaluationIso A (Etale.supportedProductImmersion f g i j)).hom ≫
            supportComparisonUnit A (Etale.supportedProductImmersion f g i j)))).app (M ⊗ N) ≫
      (comparisonUpperStar (ModuleCat.{u + 1} A) (pullback f g)).mapDerivedCategory.map
        (Etale.supportedCoefficientTensorDerived A f g i j M N) ≫
      (supportDerivedComparisonTensorIso (ModuleCat.{u + 1} A) (pullback f g)
        ((Etale.supportedFirstCoefficients A f g i).mapDerivedCategory.obj M)
        ((Etale.supportedSecondCoefficients A f g j).mapDerivedCategory.obj N)).hom =
    supportedCoefficientTensorDerived A f g i j M N ≫
      Etale.bifunctorMap (derivedTensor (ModuleCat.{u + 1} A) (pullback f g))
        ((projectedDerivedCoefficientComparison A i (pullback.fst f g)).app M)
        ((projectedDerivedCoefficientComparison A j (pullback.snd f g)).app N) := by
  let H := comparisonUpperStar (ModuleCat.{u + 1} A) (pullback f g)
  let p := Etale.supportedProductImmersion f g i j
  let da₀ := Etale.supportCoefficientMate (Etale.supportedCoefficientDerivedAdjunction A p)
    (supportedCoefficientDerivedAdjunction A p) H.mapDerivedCategory
    (Functor.rightDerivedPullback H ((supportKernelEvaluationIso A p).hom ≫
      supportComparisonUnit A p))
  let : (Etale.supportedSecondCoefficients A f g j).PreservesFlat :=
    Etale.secondCoefficient_flat A f g j
  let : ((Etale.supportedSecondCoefficients A f g j) ⋙ H).PreservesFlat :=
    ⟨fun h ↦ Functor.PreservesFlat.flat_obj
      (F := H) (Functor.PreservesFlat.flat_obj h)⟩
  let : ((Etale.supportedSecondCoefficients A f g j) ⋙ H).IsLeftAdjoint :=
    inferInstanceAs ((Etale.supportedCoefficients A j ⋙
      Etale.upperStar (ModuleCat.{u + 1} A) (pullback.snd f g)) ⋙ H).IsLeftAdjoint
  let : (Etale.supportedCoefficients A p).IsLeftAdjoint :=
    (Etale.supportedCoefficientAdjunction A p).isLeftAdjoint
  let : (supportedCoefficients A p).IsLeftAdjoint :=
    (supportedCoefficientAdjunction A p).isLeftAdjoint
  have ha₀ : mapNatNormalization (Etale.supportedCoefficients A p) H
      (supportedCoefficients A p) (coefficientComparison A p).inv da₀ := by
    dsimp only [da₀]
    rw [derivedComparisonMate_eq]
    exact exactMapNormalized _ _ _ _
  have he := schemeTensorSquareResult (ModuleCat.{u + 1} A) (pullback f g)
    (Etale.supportedCoefficients A p)
    (Etale.supportedFirstCoefficients A f g i) (Etale.supportedSecondCoefficients A f g j)
    (supportedCoefficients A p)
    (supportedFirstCoefficients A f g i) (supportedSecondCoefficients A f g j)
    (Etale.supportedCoefficientTensorNatTrans A f g i j) (coefficientTensorNatTrans A f g i j)
    (coefficientComparison A p).inv
    (projectedCoefficientComparison A i (pullback.fst f g))
    (projectedCoefficientComparison A j (pullback.snd f g)) da₀
    (projectedDerivedCoefficientComparison A i (pullback.fst f g))
    (projectedDerivedCoefficientComparison A j (pullback.snd f g))
    (Etale.coefficientTensorNatTrans A f g i j)
    (supportedCoefficientTensorComplex A f g i j)
    (by funext P Q; exact coefficientTensorComplex_eq A f g i j P Q)
    (exists_unique_supportedCoefficientTensorDerived A f g i j).choose
    (exists_unique_supportedCoefficientTensorDerived A f g i j).choose_spec.1
    (Etale.coefficientTensorNatTrans_fac A f g i j) ha₀
    (projectedDerivedCoefficientComparison_normalized A i (pullback.fst f g))
    (projectedDerivedCoefficientComparison_normalized A j (pullback.snd f g))
    (coefficientComparison_tensor A f g i j) M N
  have ht := Etale.coefficientTensorComponent_app A f g i j M N
  unfold schemeTensorComponent at ht
  have hp := proCoefficientDerivedNat_app A f g i j M N
  dsimp only [proCoefficientDerivedNat] at hp
  erw [ht, hp] at he
  simpa only [da₀, H, p] using he

private noncomputable def etCoefficientProjectionIso
    (A : Type (u + 1)) [CommRing A]
    {C X P : Scheme.{u}} (i : C ⟶ X) (p : P ⟶ X) [IsClosedImmersion i] :
    (Etale.supportedCoefficients A i ⋙ Etale.upperStar (ModuleCat.{u + 1} A) p).mapDerivedCategory ≅
      (Etale.supportedCoefficients A i).mapDerivedCategory ⋙
        (Etale.upperStar (ModuleCat.{u + 1} A) p).leftDerivedFunctor :=
  Functor.mapDerivedCategoryCompIso (Etale.supportedCoefficients A i)
      (Etale.upperStar (ModuleCat.{u + 1} A) p) ≪≫
    Functor.isoWhiskerLeft (Etale.supportedCoefficients A i).mapDerivedCategory
      (Etale.leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) p).symm

private noncomputable abbrev derivedCoefficientComparisonMate
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {C X : Scheme.{u}} (i : C ⟶ X) [IsClosedImmersion i] [IsLocallyNoetherian X] :=
  Etale.supportCoefficientMate (Etale.supportedCoefficientDerivedAdjunction A i)
    (supportedCoefficientDerivedAdjunction A i)
    (comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory
    (Functor.rightDerivedPullback (comparisonUpperStar (ModuleCat.{u + 1} A) X)
      ((supportKernelEvaluationIso A i).hom ≫ supportComparisonUnit A i))

private lemma projectedDerivedCoefficientComparison_left
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {C X P : Scheme.{u}} (i : C ⟶ X) [IsClosedImmersion i]
    [IsLocallyNoetherian X] (p : P ⟶ X) (M : DerivedCategory (ModuleCat.{u + 1} A)) :
    (projectedDerivedCoefficientComparison A i p).app M =
      (proCoefficientProjectionIso A i p).hom.app M ≫
        (upperStar (ModuleCat.{u + 1} A) p).leftDerivedFunctor.map
          ((derivedCoefficientComparisonMate A i).app M) ≫
        (comparisonLeftPullbackIso A p).inv.app
          ((Etale.supportedCoefficients A i).mapDerivedCategory.obj M) ≫
        (comparisonUpperStar (ModuleCat.{u + 1} A) P).mapDerivedCategory.map
          ((etCoefficientProjectionIso A i p).inv.app M) := by
  simp only [proCoefficientProjectionIso, etCoefficientProjectionIso,
    comparisonLeftPullbackIso, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
    NatTrans.comp_app, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerLeft_inv,
    Functor.isoWhiskerRight_inv, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    CategoryTheory.Functor.map_comp, Category.assoc]
  have hn := (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) p).inv.naturality
    ((derivedCoefficientComparisonMate A i).app M)
  rw [← reassoc_of% hn]
  rw [Iso.inv_hom_id_app_assoc]
  rw [← Functor.map_comp_assoc, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id,
    Category.id_comp]
  simp only [projectedDerivedCoefficientComparison, squareCoefficient,
    supportDerivedPullbackIso, supportDerivedCoefficientPullbackIso,
    Functor.mapDerivedCategorySquareIso, Functor.mapDerivedCategoryNatIso_symm,
    Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.assoc]

private lemma projectedEvaluation_comparison
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {C X P : Scheme.{u}} (i : C ⟶ X) [IsClosedImmersion i]
    [IsLocallyNoetherian X] (p : P ⟶ X)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (projectedDerivedCoefficientComparison A i p).app
        ((Etale.supportedSectionsDerived A i).obj K) ≫
      (comparisonUpperStar (ModuleCat.{u + 1} A) P).mapDerivedCategory.map
        ((etCoefficientProjectionIso A i p).hom.app
            ((Etale.supportedSectionsDerived A i).obj K) ≫
          (Etale.upperStar (ModuleCat.{u + 1} A) p).leftDerivedFunctor.map
            ((Etale.supportedCoefficientDerivedAdjunction A i).counit.app K)) ≫
      (comparisonLeftPullbackIso A p).hom.app K =
    (supportedCoefficients A i ⋙ upperStar (ModuleCat.{u + 1} A) p).mapDerivedCategory.map
      ((Functor.rightDerivedPullback (comparisonUpperStar (ModuleCat.{u + 1} A) X)
        ((supportKernelEvaluationIso A i).hom ≫ supportComparisonUnit A i)).app K) ≫
      (proCoefficientProjectionIso A i p).hom.app
        ((supportSections i A).rightDerivedFunctor.obj
          ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj K)) ≫
      (upperStar (ModuleCat.{u + 1} A) p).leftDerivedFunctor.map
        ((supportedCoefficientDerivedAdjunction A i).counit.app
          ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj K)) := by
  rw [projectedDerivedCoefficientComparison_left]
  exact Etale.evaluation_transport
    (Etale.supportedCoefficientDerivedAdjunction A i) (supportedCoefficientDerivedAdjunction A i)
    (comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory _
    (Etale.upperStar (ModuleCat.{u + 1} A) p).leftDerivedFunctor
    (upperStar (ModuleCat.{u + 1} A) p).leftDerivedFunctor
    (comparisonUpperStar (ModuleCat.{u + 1} A) P).mapDerivedCategory _ _
    (etCoefficientProjectionIso A i p) (proCoefficientProjectionIso A i p) K
    ((comparisonLeftPullbackIso A p).app K)
    ((comparisonLeftPullbackIso A p).app _)
    ((comparisonLeftPullbackIso A p).hom.naturality
      ((Etale.supportedCoefficientDerivedAdjunction A i).counit.app K))

private lemma comparisonTensor_natural
    (D : Type v₁) [Category.{u + 1} D] [Abelian D]
    [IsGrothendieckAbelian.{u + 1} D] [MonoidalCategory D] [MonoidalPreadditive D]
    [SymmetricCategory D] [MonoidalClosed D] [Abelian.HasFunctorialFlatResolution D]
    (T : Scheme.{u}) [(comparisonUpperStar D T).PreservesFlat]
    {K K' L L' : DerivedCategory (Sheaf T.smallEtaleTopology D)}
    (a : K ⟶ K') (b : L ⟶ L') :
    (comparisonUpperStar D T).mapDerivedCategory.map
        (Etale.bifunctorMap (Etale.derivedTensor D T) a b) ≫
      (supportDerivedComparisonTensorIso D T K' L').hom =
    (supportDerivedComparisonTensorIso D T K L).hom ≫
      Etale.bifunctorMap (derivedTensor D T)
        ((comparisonUpperStar D T).mapDerivedCategory.map a)
        ((comparisonUpperStar D T).mapDerivedCategory.map b) := by
  have h := Etale.bifunctorComparison_natural
    (Etale.derivedTensor D T)
    (derivedTensor D T)
    (comparisonUpperStar D T).mapDerivedCategory
    (exactTensor (comparisonUpperStar D T)) a b
  simpa only [exactTensor_comparison_app] using h

private lemma supportExteriorCoefficientIso_hom_eq
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (L : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (supportExteriorCoefficientIso A f g K L).hom =
      (supportDerivedComparisonTensorIso (ModuleCat.{u + 1} A) (pullback f g)
        ((Etale.upperStar (ModuleCat.{u + 1} A) (pullback.fst f g)).leftDerivedFunctor.obj K)
        ((Etale.upperStar (ModuleCat.{u + 1} A) (pullback.snd f g)).leftDerivedFunctor.obj L)).hom ≫
      Etale.bifunctorMap (derivedTensor (ModuleCat.{u + 1} A) (pullback f g))
        ((comparisonLeftPullbackIso A (pullback.fst f g)).hom.app K)
        ((comparisonLeftPullbackIso A (pullback.snd f g)).hom.app L) ≫
      eqToHom (supportedExternalProduct_eq A f g
        ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj K)
        ((comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory.obj L)) := by
  have hn := comparisonTensor_natural (ModuleCat.{u + 1} A) (pullback f g)
    ((Etale.leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A)
      (pullback.fst f g)).hom.app K)
    ((Etale.leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A)
      (pullback.snd f g)).hom.app L)
  simp only [supportExteriorCoefficientIso, Iso.trans_hom, Iso.symm_hom, Iso.app_hom,
    supportBifunctorIso, Functor.mapIso_hom, Functor.mapIso_trans,
    Category.assoc] at ⊢
  change _ ≫ _ ≫ _ ≫ _ ≫ _ = _
  simp only [Etale.bifunctorMap, CategoryTheory.Functor.map_comp, Category.assoc] at hn
  erw [reassoc_of% hn]
  simp only [comparisonLeftPullbackIso, Iso.trans_hom,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Iso.symm_hom, Etale.bifunctorMap, CategoryTheory.Functor.map_comp, Category.assoc]
  rw [NatTrans.naturality_assoc, NatTrans.naturality_assoc,
    NatTrans.naturality_assoc]
  rfl



private lemma proFirstEvaluation_eq
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {S X Y Z : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (i : Z ⟶ X)
    [IsClosedImmersion i] [IsLocallyNoetherian X]
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))) :
    supportedFirstEvaluation A f g i K =
      (proCoefficientProjectionIso A i (pullback.fst f g)).hom.app
        ((supportedSectionsDerived A i).obj K) ≫
      (upperStar (ModuleCat.{u + 1} A) (pullback.fst f g)).leftDerivedFunctor.map
        ((supportedCoefficientDerivedAdjunction A i).counit.app K) := by
  exact Etale.coefficientEvaluation_eq _ _ _ _ _ _ _ _ _

private lemma proSecondEvaluation_eq
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {S X Y W : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (j : W ⟶ Y)
    [IsClosedImmersion j] [IsLocallyNoetherian Y]
    (L : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} A))) :
    supportedSecondEvaluation A f g j L =
      (proCoefficientProjectionIso A j (pullback.snd f g)).hom.app
        ((supportedSectionsDerived A j).obj L) ≫
      (upperStar (ModuleCat.{u + 1} A) (pullback.snd f g)).leftDerivedFunctor.map
        ((supportedCoefficientDerivedAdjunction A j).counit.app L) := by
  exact Etale.coefficientEvaluation_eq _ _ _ _ _ _ _ _ _

private lemma proCoefficientTensorDerived_natural
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {S X Y Z W : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (i : Z ⟶ X) (j : W ⟶ Y) [IsClosedImmersion i] [IsClosedImmersion j]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsLocallyNoetherian (pullback f g)]
    {M M' N N' : DerivedCategory (ModuleCat.{u + 1} A)} (a : M ⟶ M') (b : N ⟶ N') :
    (supportedCoefficients A (Etale.supportedProductImmersion f g i j)).mapDerivedCategory.map
        (a ⊗ₘ b) ≫ supportedCoefficientTensorDerived A f g i j M' N' =
      supportedCoefficientTensorDerived A f g i j M N ≫
        Etale.bifunctorMap (derivedTensor (ModuleCat.{u + 1} A) (pullback f g))
          ((supportedFirstCoefficients A f g i).mapDerivedCategory.map a)
          ((supportedSecondCoefficients A f g j).mapDerivedCategory.map b) := by
  simpa only [supportedDerivedTensorMap, Etale.bifunctorMap] using
    comparison_natural A f g i j a b


private lemma comparison_exterior_unbounded
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {S X Y Z W : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (i : Z ⟶ X) (j : W ⟶ Y) [IsClosedImmersion i] [IsClosedImmersion j]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsLocallyNoetherian (pullback f g)]
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (L : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    Etale.supportedExteriorProduct A f g i j K L ≫
      (Functor.rightDerivedPullback (comparisonUpperStar (ModuleCat.{u + 1} A) (pullback f g))
        ((supportKernelEvaluationIso A (Etale.supportedProductImmersion f g i j)).hom ≫
          supportComparisonUnit A (Etale.supportedProductImmersion f g i j))).app
        (Etale.externalProduct (ModuleCat.{u + 1} A) f g K L) ≫
      (supportSections (Etale.supportedProductImmersion f g i j) A).rightDerivedFunctor.map
        (supportExteriorCoefficientIso A f g K L).hom =
    ((Functor.rightDerivedPullback (comparisonUpperStar (ModuleCat.{u + 1} A) X)
        ((supportKernelEvaluationIso A i).hom ≫ supportComparisonUnit A i)).app K ⊗ₘ
      (Functor.rightDerivedPullback (comparisonUpperStar (ModuleCat.{u + 1} A) Y)
        ((supportKernelEvaluationIso A j).hom ≫ supportComparisonUnit A j)).app L) ≫
      supportedExteriorProduct A f g i j
        ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj K)
        ((comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory.obj L) := by
  unfold Etale.supportedExteriorProduct supportedExteriorProduct
  rw [supportExteriorCoefficientIso_hom_eq]
  simp only [CategoryTheory.Functor.map_comp, ← Category.assoc]
  congr 1
  simp only [Category.assoc, ← CategoryTheory.Functor.map_comp]
  dsimp only [Etale.externalProduct]
  refine Etale.adjunct_pairing_transport
    (Etale.supportedCoefficientDerivedAdjunction A (Etale.supportedProductImmersion f g i j))
    (supportedCoefficientDerivedAdjunction A (Etale.supportedProductImmersion f g i j))
    (comparisonUpperStar (ModuleCat.{u + 1} A) (pullback f g)).mapDerivedCategory
    (Functor.rightDerivedPullback (comparisonUpperStar (ModuleCat.{u + 1} A) (pullback f g))
      ((supportKernelEvaluationIso A (Etale.supportedProductImmersion f g i j)).hom ≫
        supportComparisonUnit A (Etale.supportedProductImmersion f g i j)))
    (Etale.derivedTensor (ModuleCat.{u + 1} A) (pullback f g))
    (derivedTensor (ModuleCat.{u + 1} A) (pullback f g))
    ((Functor.rightDerivedPullback (comparisonUpperStar (ModuleCat.{u + 1} A) X)
      ((supportKernelEvaluationIso A i).hom ≫ supportComparisonUnit A i)).app K)
    ((Functor.rightDerivedPullback (comparisonUpperStar (ModuleCat.{u + 1} A) Y)
      ((supportKernelEvaluationIso A j).hom ≫ supportComparisonUnit A j)).app L)
    _ (supportedCoefficientTensorDerived A f g i j _ _) _
    ((projectedDerivedCoefficientComparison A i (pullback.fst f g)).app _)
    ((projectedDerivedCoefficientComparison A j (pullback.snd f g)).app _)
    _ _ _ _
    ((supportedFirstCoefficients A f g i).mapDerivedCategory.map
      ((Functor.rightDerivedPullback (comparisonUpperStar (ModuleCat.{u + 1} A) X)
        ((supportKernelEvaluationIso A i).hom ≫ supportComparisonUnit A i)).app K))
    ((supportedSecondCoefficients A f g j).mapDerivedCategory.map
      ((Functor.rightDerivedPullback (comparisonUpperStar (ModuleCat.{u + 1} A) Y)
        ((supportKernelEvaluationIso A j).hom ≫ supportComparisonUnit A j)).app L))
    ((comparisonLeftPullbackIso A (pullback.fst f g)).hom.app K)
    ((comparisonLeftPullbackIso A (pullback.snd f g)).hom.app L)
    (supportDerivedComparisonTensorIso (ModuleCat.{u + 1} A) (pullback f g) _ _).hom
    (supportDerivedComparisonTensorIso (ModuleCat.{u + 1} A) (pullback f g) _ _).hom
    ?_ ?_ ?_ ?_ ?_
  · exact coefficientComparison_derived_tensor A f g i j _ _
  · exact comparisonTensor_natural (ModuleCat.{u + 1} A) (pullback f g) _ _
  · rw [Etale.firstEvaluation_eq, proFirstEvaluation_eq]
    exact projectedEvaluation_comparison A i (pullback.fst f g) K
  · rw [Etale.secondEvaluation_eq, proSecondEvaluation_eq]
    exact projectedEvaluation_comparison A j (pullback.snd f g) L
  · exact proCoefficientTensorDerived_natural A f g i j _ _

private lemma presentationCancel
    {C D B : Type*} [Category C] [Category D] [Category B]
    (E : C ⥤ B) (H : C ⥤ D) (R : D ⥤ B) (r : E ⟶ H ⋙ R)
    {X Y : C} (e : X ≅ Y) {M : B} (p : M ⟶ E.obj Y)
    {Z : D} (t : H.obj Y ⟶ Z) :
    p ≫ E.map e.inv ≫ r.app X ≫ R.map (H.map e.hom ≫ t) =
      p ≫ r.app Y ≫ R.map t := by
  have hn := r.naturality e.inv
  simp only [Functor.comp_map, Functor.comp_obj] at hn
  rw [reassoc_of% hn]
  have hc : H.map e.inv ≫ (H.map e.hom ≫ t) = t := by
    rw [← Category.assoc, ← H.map_comp, e.inv_hom_id, H.map_id, Category.id_comp]
  rw [← R.map_comp, hc]

end ExteriorComparisonProof
/-- Compatibility with both supported exterior products in the unbounded derived
category of ordinary modules; the boundedness hypothesis is imposed on the actual
exterior product, rather than implicitly assuming it follows from its inputs.
Source: Stacks Tags 0H9A and 07A4; blueprint proof paragraphs 2--8
(blueprint: lem-pur-support-site-comparison).
Proof: form the quotient of the free constant sheaf by the free sheaf of the
open complement. It represents supported sections by the kernel/cokernel Yoneda
bijection. Its geometric etale stalks are zero or A, hence it is flat; comparison
pullback gives the pro-etale quotient and its flatness without using pro-etale
stalk conservativity. Quotient multiplication identifies the tensor of the two
pulled-back quotients with the product-support quotient. All maps preserve quotient
generators. The exact constant-with-support functors are left adjoint to the actual
unbounded derived support functors. Comparison of supports is the transpose of
the pulled-back counit, since both transposes send a section to its adjunction-unit
image. The exterior product is the transpose of the tensor of the two pulled-back
counits through the generator-normalized product identification. Pullback and tensor
coherence identify that identification in both topologies. Transpose both sides of
the displayed equation under the product-support adjunction. The two comparison
counit identities and monoidal coherence make the transposes equal. Injectivity of
the Hom bijection proves the equation. K-flat localization identifies these maps
with the pairing derived using K-flat tensor and injective support resolutions. -/
theorem supportComparison_exterior [Finite A] (k : Type u) [Field k] [IsAlgClosed k]
    {X Y Z W : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    (i : Z ⟶ X) (j : W ⟶ Y) [IsClosedImmersion i] [IsClosedImmersion j]
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (L : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (F : DerivedCategory.Plus
      (Sheaf (pullback (X ↘ Spec (.of k)) (Y ↘ Spec (.of k))).smallEtaleTopology
        (ModuleCat.{u + 1} A)))
    (eF : F.obj ≅ Etale.externalProduct (ModuleCat.{u + 1} A)
      (X ↘ Spec (.of k)) (Y ↘ Spec (.of k)) K.obj L.obj) :
    Etale.supportedExteriorProduct A (X ↘ Spec (.of k)) (Y ↘ Spec (.of k)) i j K.obj L.obj ≫
      (globalEtaleSupportKernel A
        (Etale.supportedProductImmersion
          (X ↘ Spec (.of k)) (Y ↘ Spec (.of k)) i j)).rightDerivedFunctor.map
          eF.inv ≫
      supportComparisonUnbounded A
        (Etale.supportedProductImmersion (X ↘ Spec (.of k)) (Y ↘ Spec (.of k)) i j) F ≫
      (supportSections
        (Etale.supportedProductImmersion
          (X ↘ Spec (.of k)) (Y ↘ Spec (.of k)) i j) A).rightDerivedFunctor.map
        ((comparisonUpperStar (ModuleCat.{u + 1} A)
          (pullback (X ↘ Spec (.of k)) (Y ↘ Spec (.of k)))).mapDerivedCategory.map eF.hom ≫
          (supportExteriorCoefficientIso A (X ↘ Spec (.of k)) (Y ↘ Spec (.of k))
            K.obj L.obj).hom) =
    tensorHom (supportComparisonUnbounded A i K) (supportComparisonUnbounded A j L) ≫
      supportedExteriorProductOverField A k (X ↘ Spec (.of k)) (Y ↘ Spec (.of k)) i j
        ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj K.obj)
        ((comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory.obj L.obj) := by
  let : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  let : IsLocallyNoetherian Y :=
    LocallyOfFiniteType.isLocallyNoetherian (Y ↘ Spec (.of k))
  rw [comparisonUnbounded_eq_global, comparisonUnbounded_eq_global,
    comparisonUnbounded_eq_global]
  rw [presentationCancel]
  exact comparison_exterior_unbounded A (X ↘ Spec (.of k)) (Y ↘ Spec (.of k)) i j K.obj L.obj

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry


namespace ProEtale

section OpenConstantProof
universe v
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option backward.defeqAttrib.useBackward true

private noncomputable def constantMap (D : Type v) [Category.{u + 1} D] [Abelian D]
    [IsGrothendieckAbelian.{u + 1} D] {Z X : Scheme.{u}} (i : Z ⟶ X) (M : D) :=
  (upperStarLowerStarAdjunction D i).unit.app
    ((constantSheaf (Scheme.ProEt.topology X) D).obj M) ≫
    (lowerStar D i).map ((constantSheafCompUpperStarIso D i).hom.app M)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types true in
private lemma constantMap_unit
    (D : Type v) [Category.{u + 1} D] [Abelian D]
    [IsGrothendieckAbelian.{u + 1} D] {Z X : Scheme.{u}}
    (i : Z ⟶ X) (M : D) :
    (constantSheafΓAdj (Scheme.ProEt.topology X) D).unit.app M ≫
      (Sheaf.Γ (Scheme.ProEt.topology X) D).map (constantMap D i M) ≫
      (globalSectionsLowerStarIso D i).hom.app _ =
    (constantSheafΓAdj (Scheme.ProEt.topology Z) D).unit.app M := by
  exact constantUnit_global D i M

attribute [local irreducible] constantMap

private theorem constantAdjunct_comp
    {B X Y Z : Type*} [Category B] [Category X] [Category Y] [Category Z]
    {LX : B ⥤ X} {LY : B ⥤ Y} {LZ : B ⥤ Z}
    {RX : X ⥤ B} {RY : Y ⥤ B} {RZ : Z ⥤ B}
    (ax : LX ⊣ RX) (ay : LY ⊣ RY) (az : LZ ⊣ RZ)
    (F : Z ⥤ Y) (G : Y ⥤ X) (H : Z ⥤ X) (p : F ⋙ G ≅ H)
    (ef : F ⋙ RY ≅ RZ) (eg : G ⋙ RX ≅ RY) (eh : H ⋙ RX ≅ RZ)
    (M : B) (f : LY.obj M ⟶ F.obj (LZ.obj M))
    (g : LX.obj M ⟶ G.obj (LY.obj M)) (h : LX.obj M ⟶ H.obj (LZ.obj M))
    (hf : ay.unit.app M ≫ RY.map f ≫ ef.hom.app _ = az.unit.app M)
    (hg : ax.unit.app M ≫ RX.map g ≫ eg.hom.app _ = ay.unit.app M)
    (hh : ax.unit.app M ≫ RX.map h ≫ eh.hom.app _ = az.unit.app M)
    (hp : RX.map (p.hom.app (LZ.obj M)) ≫ eh.hom.app _ =
      eg.hom.app _ ≫ ef.hom.app _) : g ≫ G.map f ≫ p.hom.app _ = h := by
  apply (ax.homEquiv _ _).injective
  apply (Iso.cancel_iso_hom_right _ _ (eh.app (LZ.obj M))).mp
  simp only [Adjunction.homEquiv_apply, Functor.map_comp, Iso.app_hom, Category.assoc]
  rw [hp]
  have hn := eg.hom.naturality f
  dsimp only [Functor.comp_map] at hn
  rw [reassoc_of% hn, reassoc_of% hg, hf, hh]

private lemma constantMap_comp
    (D : Type v) [Category.{u + 1} D] [Abelian D]
    [IsGrothendieckAbelian.{u + 1} D] {Z Y X : Scheme.{u}}
    (g : Z ⟶ Y) (h : Y ⟶ X) (M : D) :
    constantMap D h M ≫ (lowerStar D h).map (constantMap D g M) ≫
      (lowerStarComp D g h).hom.app _ = constantMap D (g ≫ h) M := by
  exact constantAdjunct_comp
    (constantSheafΓAdj (Scheme.ProEt.topology X) D)
    (constantSheafΓAdj (Scheme.ProEt.topology Y) D)
    (constantSheafΓAdj (Scheme.ProEt.topology Z) D)
    (lowerStar D g) (lowerStar D h) (lowerStar D (g ≫ h)) (lowerStarComp D g h)
    (globalSectionsLowerStarIso D g) (globalSectionsLowerStarIso D h)
    (globalSectionsLowerStarIso D (g ≫ h)) M
    (constantMap D g M) (constantMap D h M) (constantMap D (g ≫ h) M)
    (constantMap_unit D g M) (constantMap_unit D h M)
    (constantMap_unit D (g ≫ h) M) (globalSectionsLowerStarIso_comp D g h _)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types true in
private lemma constantMap_congr
    (D : Type v) [Category.{u + 1} D] [Abelian D]
    [IsGrothendieckAbelian.{u + 1} D] {Y X : Scheme.{u}}
    {g h : Y ⟶ X} (w : g = h) (M : D) :
    constantMap D g M ≫ (lowerStarCongr D w).hom.app _ = constantMap D h M := by
  apply ((constantSheafΓAdj (Scheme.ProEt.topology X) D).homEquiv _ _).injective
  let e := (globalSectionsLowerStarIso D h).app
    ((constantSheaf (Scheme.ProEt.topology Y) D).obj M)
  apply (Iso.cancel_iso_hom_right _ _ e).mp
  dsimp only [e, Iso.app_hom]
  simp only [Adjunction.homEquiv_apply, Functor.map_comp, Category.assoc]
  rw [globalSectionsLowerStarIso_congr]
  erw [constantMap_unit, constantMap_unit]

private lemma iso_hom (D : Type v) [Category.{u + 1} D] [Abelian D]
    [IsGrothendieckAbelian.{u + 1} D]
    {C' C U T : Scheme.{u}} {w : C' ⟶ C} {i' : C' ⟶ U} {v : U ⟶ T} {i : C ⟶ T}
    (sq : CommSq i' w v i) :
    (squareLowerStarIso D sq).hom =
      (lowerStarComp D w i).hom ≫ (lowerStarCongr D sq.w.symm).hom ≫
        (lowerStarComp D i' v).inv := rfl
private lemma square_map
    (D : Type v) [Category.{u + 1} D] [Abelian D]
    [IsGrothendieckAbelian.{u + 1} D]
    {C' C U T : Scheme.{u}} {w : C' ⟶ C} {i' : C' ⟶ U} {v : U ⟶ T} {i : C ⟶ T}
    (sq : CommSq i' w v i) (M : Sheaf (Scheme.ProEt.topology C') D) :
    (squareLowerStarIso D sq).hom.app M =
      (lowerStarComp D w i).hom.app M ≫ (lowerStarCongr D sq.w.symm).hom.app M ≫
        (lowerStarComp D i' v).inv.app M :=
  congrArg (fun α ↦ α.app M) (iso_hom D sq)

private lemma constantMap_square
    (D : Type v) [Category.{u + 1} D] [Abelian D]
    [IsGrothendieckAbelian.{u + 1} D]
    {C' C U T : Scheme.{u}} {w : C' ⟶ C} {i' : C' ⟶ U} {v : U ⟶ T} {i : C ⟶ T}
    (sq : CommSq i' w v i) (M : D) :
    constantMap D i M ≫ (lowerStar D i).map (constantMap D w M) ≫
        (squareLowerStarIso D sq).hom.app _ =
      constantMap D v M ≫ (lowerStar D v).map (constantMap D i' M) := by
  rw [square_map]
  apply (Iso.cancel_iso_hom_right _ _ ((lowerStarComp D i' v).app
    ((constantSheaf (Scheme.ProEt.topology C') D).obj M))).mp
  simp only [Category.assoc, Iso.app_hom, Iso.inv_hom_id_app, Category.comp_id]
  rw [reassoc_of% constantMap_comp D w i M, constantMap_congr]
  exact (constantMap_comp D i' v M).symm


private theorem mate_square
    {B C U T : Type*} [Category B] [Category C] [Category U] [Category T]
    {Lw : C ⥤ B} {Rw : B ⥤ C} {Lv : T ⥤ U} {Rv : U ⥤ T}
    (aw : Lw ⊣ Rw) (av : Lv ⊣ Rv) (I : C ⥤ T) (J : B ⥤ U)
    (σ : Rw ⋙ I ⟶ J ⋙ Rv)
    {c : C} {b : B} {u : U} {t : T}
    (a : t ⟶ I.obj c) (cw : Lw.obj c ⟶ b) (cv : Lv.obj t ⟶ u) (q : u ⟶ J.obj b)
    (hs : a ≫ I.map (aw.unit.app c ≫ Rw.map cw) ≫ σ.app b =
      av.unit.app t ≫ Rv.map cv ≫ Rv.map q) :
    Lv.map a ≫ ((mateEquiv aw av).symm (TwoSquare.mk _ _ _ _ σ)).natTrans.app c ≫
        J.map cw = cv ≫ q := by
  apply (av.homEquiv _ _).injective
  simp only [Adjunction.homEquiv_apply, Functor.map_comp]
  have hv := av.unit.naturality a
  dsimp only [Functor.comp_map, Functor.id_map] at hv
  rw [← reassoc_of% hv]
  rw [← reassoc_of% unit_mateEquiv_symm aw av (TwoSquare.mk _ _ _ _ σ) c]
  have hn := σ.naturality cw
  dsimp only [Functor.comp_map] at hn
  rw [← hn, ← I.map_comp_assoc]
  exact hs

private lemma baseChangeMap_eq_mate
    (D : Type v) [Category.{u + 1} D] [Abelian D]
    [IsGrothendieckAbelian.{u + 1} D]
    {C' C U T : Scheme.{u}} {w : C' ⟶ C} {i' : C' ⟶ U} {v : U ⟶ T} {i : C ⟶ T}
    [WeaklyEtale w] [WeaklyEtale v] (sq : CommSq i' w v i) :
    baseChangeMap D sq =
      ((mateEquiv (upperStarLowerStarAdjunction D w)
        (upperStarLowerStarAdjunction D v)).symm
        (TwoSquare.mk _ _ _ _ (squareLowerStarIso D sq).hom)).natTrans := rfl

private theorem mate_square_normalized
    {B C U T : Type*} [Category B] [Category C] [Category U] [Category T]
    {Lw : C ⥤ B} {Rw : B ⥤ C} {Lv : T ⥤ U} {Rv : U ⥤ T}
    (aw : Lw ⊣ Rw) (av : Lv ⊣ Rv) (I : C ⥤ T) (J : B ⥤ U)
    (σ : Rw ⋙ I ⟶ J ⋙ Rv)
    (β : I ⋙ Lv ⟶ Lw ⋙ J)
    (hβ : β = ((mateEquiv aw av).symm (TwoSquare.mk _ _ _ _ σ)).natTrans)
    {c : C} {b : B} {u : U} {t : T}
    (a : t ⟶ I.obj c) (cw : Lw.obj c ⟶ b) (cv : Lv.obj t ⟶ u) (q : u ⟶ J.obj b)
    (qw : c ⟶ Rw.obj b) (qv : t ⟶ Rv.obj u)
    (hw : qw = aw.unit.app c ≫ Rw.map cw)
    (hv : qv = av.unit.app t ≫ Rv.map cv)
    (hs : a ≫ I.map qw ≫ σ.app b = qv ≫ Rv.map q) :
    Lv.map a ≫ β.app c ≫ J.map cw = cv ≫ q := by
  rw [hβ]
  apply mate_square aw av I J σ a cw cv q
  rw [hw, hv, Category.assoc] at hs
  exact hs

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types true in
private lemma constantMap_def
    (D : Type v) [Category.{u + 1} D] [Abelian D]
    [IsGrothendieckAbelian.{u + 1} D] {Z X : Scheme.{u}} (i : Z ⟶ X) (M : D) :
    constantMap D i M = (upperStarLowerStarAdjunction D i).unit.app
      ((constantSheaf (Scheme.ProEt.topology X) D).obj M) ≫
        (lowerStar D i).map ((constantSheafCompUpperStarIso D i).hom.app M) := by
  unfold constantMap
  rfl
private lemma constantMap_baseChange_aux
    (D : Type v) [Category.{u + 1} D] [Abelian D]
    [IsGrothendieckAbelian.{u + 1} D]
    {C' C U T : Scheme.{u}} {w : C' ⟶ C} {i' : C' ⟶ U} {v : U ⟶ T} {i : C ⟶ T}
    [WeaklyEtale w] [WeaklyEtale v] (sq : CommSq i' w v i) (M : D)
    (β : lowerStar D i ⋙ upperStar D v ⟶ upperStar D w ⋙ lowerStar D i')
    (hβ : β = ((mateEquiv (upperStarLowerStarAdjunction D w)
      (upperStarLowerStarAdjunction D v)).symm
        (TwoSquare.mk _ _ _ _ (squareLowerStarIso D sq).hom)).natTrans) :
    (upperStar D v).map (constantMap D i M) ≫
        β.app ((constantSheaf (Scheme.ProEt.topology C) D).obj M) ≫
        (lowerStar D i').map ((constantSheafCompUpperStarIso D w).hom.app M) =
      (constantSheafCompUpperStarIso D v).hom.app M ≫ constantMap D i' M := by
  exact mate_square_normalized (upperStarLowerStarAdjunction D w)
    (upperStarLowerStarAdjunction D v) (lowerStar D i) (lowerStar D i')
    (squareLowerStarIso D sq).hom β hβ
    (constantMap D i M) ((constantSheafCompUpperStarIso D w).hom.app M)
    ((constantSheafCompUpperStarIso D v).hom.app M) (constantMap D i' M)
    (constantMap D w M) (constantMap D v M)
    (constantMap_def D w M) (constantMap_def D v M) (constantMap_square D sq M)


private noncomputable def constantMapNat
    (D : Type v) [Category.{u + 1} D] [Abelian D]
    [IsGrothendieckAbelian.{u + 1} D] {Z X : Scheme.{u}} (i : Z ⟶ X) :
    constantSheaf (Scheme.ProEt.topology X) D ⟶
      constantSheaf (Scheme.ProEt.topology Z) D ⋙ lowerStar D i :=
  Functor.whiskerLeft (constantSheaf (Scheme.ProEt.topology X) D)
      (upperStarLowerStarAdjunction D i).unit ≫
    Functor.whiskerRight (constantSheafCompUpperStarIso D i).hom (lowerStar D i)

private lemma constantMapNat_app
    (D : Type v) [Category.{u + 1} D] [Abelian D]
    [IsGrothendieckAbelian.{u + 1} D] {Z X : Scheme.{u}} (i : Z ⟶ X) (M : D) :
    (constantMapNat D i).app M = constantMap D i M := by
  unfold constantMapNat constantMap
  rfl

private lemma constantMap_baseChange_nat
    (D : Type v) [Category.{u + 1} D] [Abelian D]
    [IsGrothendieckAbelian.{u + 1} D]
    {C' C U T : Scheme.{u}} {w : C' ⟶ C} {i' : C' ⟶ U} {v : U ⟶ T} {i : C ⟶ T}
    [WeaklyEtale w] [WeaklyEtale v] (sq : CommSq i' w v i) :
    Functor.whiskerRight (constantMapNat D i) (upperStar D v) ≫
      Functor.whiskerLeft (constantSheaf (Scheme.ProEt.topology C) D) (baseChangeMap D sq) ≫
      Functor.whiskerRight (constantSheafCompUpperStarIso D w).hom (lowerStar D i') =
    (constantSheafCompUpperStarIso D v).hom ≫ constantMapNat D i' := by
  have h (β : lowerStar D i ⋙ upperStar D v ⟶ upperStar D w ⋙ lowerStar D i')
      (hβ : β = ((mateEquiv (upperStarLowerStarAdjunction D w)
        (upperStarLowerStarAdjunction D v)).symm
          (TwoSquare.mk _ _ _ _ (squareLowerStarIso D sq).hom)).natTrans) :
      Functor.whiskerRight (constantMapNat D i) (upperStar D v) ≫
        Functor.whiskerLeft (constantSheaf (Scheme.ProEt.topology C) D) β ≫
        Functor.whiskerRight (constantSheafCompUpperStarIso D w).hom (lowerStar D i') =
      (constantSheafCompUpperStarIso D v).hom ≫ constantMapNat D i' := by
    apply NatTrans.ext
    funext M
    simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      constantMapNat_app]
    exact constantMap_baseChange_aux D sq M β hβ
  exact h (baseChangeMap D sq) (baseChangeMap_eq_mate D sq)

end OpenConstantProof

variable (A : Type (u + 1)) [CommRing A] [Finite A] {C T U : Scheme.{u}}
  [IsLocallyNoetherian T] [IsLocallyNoetherian U]
  (i : C ⟶ T) [IsClosedImmersion i] (v : U ⟶ T) [IsOpenImmersion v]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types true in
set_option backward.defeqAttrib.useBackward true in
set_option linter.unusedSectionVars false in
/-- Pullback of the support quotient, determined by its constant quotient map.
Source: blueprint proof paragraphs 1 and 3 (blueprint: lem-pur-support-site-comparison).
Proof: inverse image takes the free sheaf on an open to the free sheaf on its
inverse image. It preserves the cokernel defining supported constants, and the
inverse image of the complement is the complement of the pulled-back support.
This produces the normalized isomorphism. Its quotient map is epimorphic, so the
normalization determines it at every coefficient module, hence uniquely as a
natural isomorphism. In the pro-etale topology this is also the pullback of the
etale quotient construction through comparison. -/
theorem supportOpenConstantIso_existsUnique :
    ∃! e : supportedCoefficients A i ⋙ upperStar (ModuleCat.{u + 1} A) v ≅
      supportedCoefficients A (pullback.snd i v),
      ∀ M : ModuleCat.{u + 1} A,
        (upperStar (ModuleCat.{u + 1} A) v).map (supportedCoefficientQuotient A i M) ≫
          e.hom.app M =
        (constantSheafCompUpperStarIso (ModuleCat.{u + 1} A) v).hom.app M ≫
          supportedCoefficientQuotient A (pullback.snd i v) M := by
  let D := ModuleCat.{u + 1} A
  let sq := (IsPullback.of_hasPullback i v).flip
  have : IsIso (baseChangeMap D sq.toCommSq) :=
    isIso_baseChangeMap_of_isPullback D sq
  let e : supportedCoefficients A i ⋙ upperStar D v ≅
      supportedCoefficients A (pullback.snd i v) :=
    Functor.isoWhiskerLeft (constantSheaf (Scheme.ProEt.topology C) D)
      (asIso (baseChangeMap D sq.toCommSq)) ≪≫
    Functor.isoWhiskerRight (constantSheafCompUpperStarIso D (pullback.fst i v))
      (lowerStar D (pullback.snd i v))
  have eh : e.hom =
      Functor.whiskerLeft (constantSheaf (Scheme.ProEt.topology C) D)
        (baseChangeMap D sq.toCommSq) ≫
      Functor.whiskerRight (constantSheafCompUpperStarIso D (pullback.fst i v)).hom
        (lowerStar D (pullback.snd i v)) := rfl
  have hnat :
      Functor.whiskerRight (constantMapNat D i) (upperStar D v) ≫ e.hom =
        (constantSheafCompUpperStarIso D v).hom ≫
          constantMapNat D (pullback.snd i v) := by
    rw [eh]
    exact constantMap_baseChange_nat D sq.toCommSq
  have hn (M : ModuleCat.{u + 1} A) :
      (upperStar D v).map (supportedCoefficientQuotient A i M) ≫ e.hom.app M =
        (constantSheafCompUpperStarIso D v).hom.app M ≫
          supportedCoefficientQuotient A (pullback.snd i v) M := by
    have h := congrArg (fun α ↦ α.app M) hnat
    simpa only [NatTrans.comp_app, Functor.whiskerRight_app, constantMapNat_app,
      supportedCoefficientQuotient, Adjunction.homEquiv_apply, constantMap] using h
  refine ⟨e, hn, ?_⟩
  intro e' he'
  apply Iso.ext
  apply NatTrans.ext
  funext M
  have := coefficientQuotient_epi A i M
  have := Functor.map_epi (upperStar D v) (supportedCoefficientQuotient A i M)
  apply (cancel_epi ((upperStar D v).map (supportedCoefficientQuotient A i M))).mp
  exact (he' M).trans (hn M).symm
/-- The normalized open pullback of the supported constant functor.
Source: blueprint proof paragraph 1 (blueprint: lem-pur-support-site-comparison). -/
noncomputable def supportOpenConstantIso :
    supportedCoefficients A i ⋙ upperStar (ModuleCat.{u + 1} A) v ≅
      supportedCoefficients A (pullback.snd i v) :=
  Classical.choose (supportOpenConstantIso_existsUnique A i v)

/-- The exact derived open pullback of the quotient functor.
Source: blueprint proof paragraph 1 (blueprint: lem-pur-support-site-comparison). -/
noncomputable def supportOpenDerivedConstantIso :
    (supportedCoefficients A i).mapDerivedCategory ⋙
      (upperStar (ModuleCat.{u + 1} A) v).mapDerivedCategory ≅
        (supportedCoefficients A (pullback.snd i v)).mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso (supportedCoefficients A i)
    (upperStar (ModuleCat.{u + 1} A) v)).symm ≪≫
      Functor.mapDerivedCategoryNatIso (supportOpenConstantIso A i v)

/-- Restriction of derived supported sections to an open: transpose the pulled-back
support counit using the uniquely quotient-normalized base-change identification.
Source: blueprint proof paragraph 1 (blueprint: lem-pur-support-site-comparison). -/
noncomputable def supportOpenRestriction
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A))) :=
  (supportedCoefficientDerivedAdjunction A (pullback.snd i v)).homEquiv _ _
    ((supportOpenDerivedConstantIso A i v).inv.app
      ((supportSections i A).rightDerivedFunctor.obj K) ≫
      (upperStar (ModuleCat.{u + 1} A) v).mapDerivedCategory.map
        ((supportedCoefficientDerivedAdjunction A i).counit.app K))

end ProEtale

namespace ProEtale

/-- Open restriction with local Noetherianity supplied by finite type over the field.
Source: blueprint open-restriction clause (blueprint: lem-pur-support-site-comparison). -/
noncomputable def supportOpenRestrictionOverField
    (A : Type (u + 1)) [CommRing A] [Finite A] (k : Type u) [Field k]
    {C T U : Scheme.{u}} [T.Over (Spec (.of k))]
    [LocallyOfFiniteType (T ↘ Spec (.of k))]
    (i : C ⟶ T) [IsClosedImmersion i] (v : U ⟶ T) [IsOpenImmersion v]
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A))) :=
  letI : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian (T ↘ Spec (.of k))
  letI : IsLocallyNoetherian U := LocallyOfFiniteType.isLocallyNoetherian v
  supportOpenRestriction A i v K

section OpenCoefficientNormalization
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true
set_option backward.defeqAttrib.useBackward true
private lemma supportOpenConstantIso_quotient_inv
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {C T U : Scheme.{u}} (i : C ⟶ T) [IsClosedImmersion i]
    (v : U ⟶ T) [IsOpenImmersion v]
    [IsLocallyNoetherian T] [IsLocallyNoetherian U] (M : ModuleCat.{u + 1} A) :
    supportedCoefficientQuotient A (pullback.snd i v) M ≫
        (supportOpenConstantIso A i v).inv.app M =
      (constantSheafCompUpperStarIso (ModuleCat.{u + 1} A) v).inv.app M ≫
        (upperStar (ModuleCat.{u + 1} A) v).map (supportedCoefficientQuotient A i M) := by
  have h := (supportOpenConstantIso_existsUnique A i v).choose_spec.1 M
  apply (Iso.comp_inv_eq ((supportOpenConstantIso A i v).app M)).2
  erw [Category.assoc, h, Iso.inv_hom_id_app_assoc]

private noncomputable def ordinaryEtaleOpenMate
    (A : Type (u + 1)) [CommRing A]
    {C T : Scheme.{u}} (i : C ⟶ T) [IsClosedImmersion i] (U : T.Opens) :=
  Etale.supportCoefficientMate (Etale.supportedCoefficientAdjunction A i)
    (Etale.supportedCoefficientAdjunction A (Etale.supportOnOpen i U))
    (Etale.upperStar (ModuleCat.{u + 1} A) U.ι)
    (Etale.supportTransport A U.ι i (Etale.supportOnOpen i U)
      (Etale.supportOnOpen_complement i U))

private lemma coefficientComparison_open
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {C T : Scheme.{u}} (i : C ⟶ T) [IsClosedImmersion i]
    [IsLocallyNoetherian T] (U : T.Opens) [IsLocallyNoetherian U]
    (M : ModuleCat.{u + 1} A) :
    (supportOpenConstantIso A i U.ι).inv.app M ≫
        (upperStar (ModuleCat.{u + 1} A) U.ι).map ((coefficientComparison A i).inv.app M) =
      (coefficientComparison A (pullback.snd i U.ι)).inv.app M ≫
        (comparisonUpperStar (ModuleCat.{u + 1} A) U).map
          ((ordinaryEtaleOpenMate A i U).app M) ≫
        (supportSiteComparisonCoefficientPullbackIso (ModuleCat.{u + 1} A) U.ι).hom.app
          ((Etale.supportedCoefficients A i).obj M) := by
  let D := ModuleCat.{u + 1} A
  have := coefficientQuotient_epi A (pullback.snd i U.ι) M
  exact quotientMateSquare
    (Etale.upperStar D U.ι) (upperStar D U.ι)
    (comparisonUpperStar D T) (comparisonUpperStar D U)
    (supportSiteComparisonCoefficientPullbackIso D U.ι)
    (Etale.supportedCoefficientQuotient A i M)
    (Etale.supportedCoefficientQuotient A (Etale.supportOnOpen i U) M)
    (supportedCoefficientQuotient A i M)
    (supportedCoefficientQuotient A (pullback.snd i U.ι) M)
    ((Scheme.upperStarConstantSheafIso D U.ι).app M)
    ((constantSheafCompUpperStarIso D U.ι).app M)
    ((constantComparison A T).inv.app M) ((constantComparison A U).inv.app M)
    ((coefficientComparison A i).inv.app M)
    ((coefficientComparison A (pullback.snd i U.ι)).inv.app M)
    ((ordinaryEtaleOpenMate A i U).app M)
    ((supportOpenConstantIso A i U.ι).inv.app M)
    (coefficientComparison_quotient A i M)
    (coefficientComparison_quotient A (pullback.snd i U.ι) M)
    (Etale.supportedCoefficientOpenMate_quotient A U.ι i (Etale.supportOnOpen i U)
      (Etale.supportOnOpen_complement i U) M)
    (supportOpenConstantIso_quotient_inv A i U.ι M)
    (constantComparison_square_inv A U.ι M)
private noncomputable def ordinaryProEtaleOpenRestriction
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {C T U : Scheme.{u}} (i : C ⟶ T) [IsClosedImmersion i]
    (v : U ⟶ T) [IsOpenImmersion v]
    [IsLocallyNoetherian T] [IsLocallyNoetherian U] :=
  coefficientRightMate (supportedCoefficientAdjunction A i)
    (supportedCoefficientAdjunction A (pullback.snd i v))
    (upperStar (ModuleCat.{u + 1} A) v) (supportOpenConstantIso A i v).inv

private lemma supportOpenRestriction_eq_derived
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {C T U : Scheme.{u}} (i : C ⟶ T) [IsClosedImmersion i]
    (v : U ⟶ T) [IsOpenImmersion v]
    [IsLocallyNoetherian T] [IsLocallyNoetherian U]
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A))) :
    supportOpenRestriction A i v K =
      (Functor.rightDerivedPullback (upperStar (ModuleCat.{u + 1} A) v)
        (ordinaryProEtaleOpenRestriction A i v)).app K := by
  rw [ordinaryProEtaleOpenRestriction, ← derivedRightMate, coefficientRightMate_app]
  unfold supportOpenRestriction supportOpenDerivedConstantIso
  apply congrArg ((supportedCoefficientDerivedAdjunction A (pullback.snd i v)).homEquiv _ _)
  erw [exactMap_iso (supportOpenConstantIso A i v).symm,
    Functor.mapDerivedCategoryNatIso_symm]
  rfl

private lemma ordinaryComparison_open
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {C T : Scheme.{u}} (i : C ⟶ T) [IsClosedImmersion i]
    [IsLocallyNoetherian T] (U : T.Opens) [IsLocallyNoetherian U]
    (K : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    (((supportKernelEvaluationIso A i).hom ≫ supportComparisonUnit A i).app K) ≫
        (ordinaryProEtaleOpenRestriction A i U.ι).app
          ((comparisonUpperStar (ModuleCat.{u + 1} A) T).obj K) =
      (Etale.supportTransport A U.ι i (Etale.supportOnOpen i U)
        (Etale.supportOnOpen_complement i U)).app K ≫
      (((supportKernelEvaluationIso A (pullback.snd i U.ι)).hom ≫
        supportComparisonUnit A (pullback.snd i U.ι)).app
          ((Etale.upperStar (ModuleCat.{u + 1} A) U.ι).obj K)) ≫
      (supportSections (pullback.snd i U.ι) A).map
        ((supportSiteComparisonCoefficientPullbackIso (ModuleCat.{u + 1} A) U.ι).hom.app K) := by
  rw [ordinaryProEtaleOpenRestriction, coefficientRightMate_app]
  exact mateSquareDirect
    (Etale.supportedCoefficientAdjunction A i)
    (Etale.supportedCoefficientAdjunction A (Etale.supportOnOpen i U))
    (supportedCoefficientAdjunction A i)
    (supportedCoefficientAdjunction A (pullback.snd i U.ι))
    (Etale.upperStar (ModuleCat.{u + 1} A) U.ι)
    (upperStar (ModuleCat.{u + 1} A) U.ι)
    (comparisonUpperStar (ModuleCat.{u + 1} A) T)
    (comparisonUpperStar (ModuleCat.{u + 1} A) U)
    ((supportKernelEvaluationIso A i).hom ≫ supportComparisonUnit A i)
    ((supportKernelEvaluationIso A (pullback.snd i U.ι)).hom ≫
      supportComparisonUnit A (pullback.snd i U.ι))
    (Etale.supportTransport A U.ι i (Etale.supportOnOpen i U)
      (Etale.supportOnOpen_complement i U))
    (supportOpenConstantIso A i U.ι).inv
    (supportSiteComparisonCoefficientPullbackIso (ModuleCat.{u + 1} A) U.ι)
    (by
      intro M
      erw [comparisonMate_eq, comparisonMate_eq]
      exact coefficientComparison_open A i U M) K

end OpenCoefficientNormalization

/-- The comparison commutes with canonical restriction to every open, with the
specified comparison-pullback coefficient transport on the restricted object.
Source: blueprint proof paragraph 1 (blueprint: lem-pur-support-site-comparison).
Proof: restriction commutes with the support kernel because both maps restrict
the same sections. Open restriction preserves K-injectives: its extension-by-zero
left adjoint is exact in each topology. Thus on restricted K-injective direct
images the same kernel square computes the derived restriction square. The
comparison unit commutes with this square by adjunction, since both restricted
units are transposes of the identity. The pro-etale quotient-normalized transpose
is this same restriction map by the support adjunction. The etale arrow reuses
`Etale.derivedSupportOpenRestriction`,
normalized by ordinary kernel restriction and the derived-composition unit.
Therefore the two paths are equal, with exactly the canonical pullback coefficient
identification displayed on the last map. -/
theorem supportComparison_open (A : Type (u + 1)) [CommRing A] [Finite A]
    (k : Type u) [Field k] [IsAlgClosed k]
    {C T : Scheme.{u}} [T.Over (Spec (.of k))]
    [LocallyOfFiniteType (T ↘ Spec (.of k))] [QuasiCompact (T ↘ Spec (.of k))]
    [IsSeparated (T ↘ Spec (.of k))]
    (i : C ⟶ T) [IsClosedImmersion i] (U : T.Opens)
    (M : DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    supportComparisonUnbounded A i M ≫
      supportOpenRestrictionOverField A k i U.ι
        ((comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory.obj M.obj) =
    (Etale.derivedSupportOpenRestriction A i U).app M.obj ≫
      supportComparisonUnbounded A (pullback.snd i U.ι)
        ((Etale.upperStar (ModuleCat.{u + 1} A) U.ι).mapDerivedCategoryPlus.obj M) ≫
      (supportSections (pullback.snd i U.ι) A).rightDerivedFunctor.map
        ((supportDerivedPullbackIso A U.ι).hom.app M.obj) := by
  let : IsLocallyNoetherian T :=
    LocallyOfFiniteType.isLocallyNoetherian (T ↘ Spec (.of k))
  let : IsLocallyNoetherian U := LocallyOfFiniteType.isLocallyNoetherian U.ι
  rw [comparisonUnbounded_eq_global, comparisonUnbounded_eq_global]
  change _ ≫ supportOpenRestriction A i U.ι _ = _
  rw [supportOpenRestriction_eq_derived]
  have h := derivedPullbackSquare
    (Etale.upperStar (ModuleCat.{u + 1} A) U.ι)
    (comparisonUpperStar (ModuleCat.{u + 1} A) U)
    (comparisonUpperStar (ModuleCat.{u + 1} A) T)
    (upperStar (ModuleCat.{u + 1} A) U.ι)
    (globalEtaleSupportKernel A i)
    (globalEtaleSupportKernel A (Etale.supportOnOpen i U))
    (supportSections i A) (supportSections (pullback.snd i U.ι) A)
    (Etale.supportTransport A U.ι i (Etale.supportOnOpen i U)
      (Etale.supportOnOpen_complement i U))
    ((supportKernelEvaluationIso A (pullback.snd i U.ι)).hom ≫
      supportComparisonUnit A (pullback.snd i U.ι))
    ((supportKernelEvaluationIso A i).hom ≫ supportComparisonUnit A i)
    (ordinaryProEtaleOpenRestriction A i U.ι)
    (supportSiteComparisonCoefficientPullbackIso (ModuleCat.{u + 1} A) U.ι)
    (fun K ↦ (ordinaryComparison_open A i U K).symm) M.obj
  rw [Etale.support_pullback_eq, ← Etale.openRestriction_eq_transport] at h
  exact h

end ProEtale
end AlgebraicGeometry
