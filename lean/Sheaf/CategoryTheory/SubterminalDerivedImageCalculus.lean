/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q115
-/
module

public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.CategoryTheory.Subterminal
public import Mathlib.CategoryTheory.Sites.Subcanonical
public import WeilConjectures.Mathlib.Algebra.Category.Ring.Limits
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
import Sheaf.CategoryTheory.SiteRelocalizationKInjective
import Sheaf.CategoryTheory.SiteRestrictionKInjective
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import Sheaf.CategoryTheory.DerivedCategory.ExactRestrictionComposition
import Sheaf.CategoryTheory.RingedToposOrdinaryCrossRestriction

/-! # Derived direct images for subterminal slices

Source: Stacks Project, Tags 03CE, 08DG, 08FI and 09T5
(blueprint: lem-sp-subterminal-derived-image-calculus).

The auxiliary records package chosen derived functors with their localization comparisons.
Every functor on module sheaves is the existing Mathlib functor, including its scalar map.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u r w a b va vb wa wb

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.SubterminalImageCalculus

/-- Abelian sheafification on a small site in any coefficient universe containing it.
Source: Stacks 03CV (blueprint: lem-sp-subterminal-derived-image-calculus). -/
instance smallSheafify {C : Type a} [Category.{va} C] [EssentiallySmall.{r} C]
    (J : GrothendieckTopology C) : HasSheafify J AddCommGrpCat.{r} :=
  hasSheafifyEssentiallySmallSite J AddCommGrpCat.{r}

/-- The sheafification criterion transported from a small model.
Source: Stacks 03CV (blueprint: lem-sp-subterminal-derived-image-calculus). -/
instance smallLocalCriterion {C : Type a} [Category.{va} C] [EssentiallySmall.{r} C]
    (J : GrothendieckTopology C) : J.WEqualsLocallyBijective AddCommGrpCat.{r} :=
  letI : ∀ X : Cᵒᵖ,
      HasLimitsOfShape
        (StructuredArrow X (equivSmallModel.{r} C).inverse.op) AddCommGrpCat.{r} :=
    fun _ ↦ HasLimitsOfShape.of_small.{r, r} AddCommGrpCat.{r} _
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall J
    (A := AddCommGrpCat.{r})

/-- Pushforward acts additively componentwise. Source: Stacks 03CE, module specialization
(blueprint: lem-sp-subterminal-derived-image-calculus). -/
instance pushforwardAdditive
    {C : Type a} [Category.{va} C] {D : Type b} [Category.{vb} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {F : C ⥤ D} [F.IsContinuous J K]
    {S : Sheaf J RingCat.{r}} {R : Sheaf K RingCat.{r}}
    (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{r} J K).obj R) :
    (SheafOfModules.pushforward.{w} φ).Additive where
  map_add := rfl

/-- Restriction is the additive pushforward along the forgetful functor.
Source: Stacks 03CE (blueprint: lem-sp-subterminal-derived-image-calculus). -/
instance overAdditive {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{r}) (Z : C) :
    (SheafOfModules.overFunctor.{w} R Z).Additive := pushforwardAdditive (𝟙 _)

/-- Relocalization is additive on sectionwise maps.
Source: Stacks 03DH (blueprint: lem-sp-subterminal-derived-image-calculus). -/
instance overMapAdditive {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{r}) {X Y : C} (f : X ⟶ Y) :
    (SheafOfModules.overMap.{w} R f).Additive :=
  pushforwardAdditive (Sheaf.pushforwardOverMapIso R f).inv

/-- Slice direct image is additive on sectionwise maps.
Source: Stacks 03CE (blueprint: lem-sp-subterminal-derived-image-calculus). -/
instance overPullbackAdditive {C : Type u} [SmallCategory C] [HasPullbacks C]
    {J : GrothendieckTopology C} (R : Sheaf J RingCat.{r}) {X Y : C} (f : X ⟶ Y) :
    (SheafOfModules.overPullback.{w} R f).Additive :=
  pushforwardAdditive (Sheaf.toPushforwardOverPullback R f)

/-- A chosen derived restriction/direct-image adjunction, normalized on complexes.
Source: Stacks 08FI, 070I, 070K and 09T5
(blueprint: lem-sp-subterminal-derived-image-calculus).
The two preservation fields and two resolution fields are assertions, not assumptions
on the site. The comparison `qG` computes direct image on K-injective complexes.
The last field fixes the derived adjunction to the ordinary chain-map transpose. -/
structure DerivedPair
    {A : Type a} [Category.{va} A] [Abelian A]
    {B : Type b} [Category.{vb} B] [Abelian B]
    [HasDerivedCategory.{wa} A] [HasDerivedCategory.{wb} B]
    (F : A ⥤ B) (G : B ⥤ A) [F.Additive] [G.Additive]
    (ordinary : F ⊣ G) where
  left : DerivedCategory A ⥤ DerivedCategory B
  right : DerivedCategory B ⥤ DerivedCategory A
  adj : left ⊣ right
  qF : DerivedCategory.Q ⋙ left ≅ F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q
  qG : G.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ right
  qG_iso : ∀ (I : CochainComplex B ℤ), I.IsKInjective → IsIso (qG.app I)
  restrict_injective : ∀ (I : CochainComplex A ℤ), I.IsKInjective →
    CochainComplex.IsKInjective ((F.mapHomologicalComplex (.up ℤ)).obj I)
  direct_injective : ∀ (I : CochainComplex B ℤ), I.IsKInjective →
    CochainComplex.IsKInjective ((G.mapHomologicalComplex (.up ℤ)).obj I)
  resolutions_source : ∀ (M : CochainComplex A ℤ),
    ∃ (I : CochainComplex A ℤ) (i : M ⟶ I), QuasiIso i ∧ I.IsKInjective
  resolutions_target : ∀ (M : CochainComplex B ℤ),
    ∃ (I : CochainComplex B ℤ) (i : M ⟶ I), QuasiIso i ∧ I.IsKInjective
  transpose : ∀ (M : CochainComplex A ℤ) (I : CochainComplex B ℤ)
    (f : (F.mapHomologicalComplex (.up ℤ)).obj M ⟶ I), I.IsKInjective →
    adj.homEquiv (DerivedCategory.Q.obj M) (DerivedCategory.Q.obj I)
        (qF.hom.app M ≫ DerivedCategory.Q.map f) =
      DerivedCategory.Q.map ((ordinary.mapHomologicalComplex (.up ℤ)).homEquiv M I f) ≫
        qG.app I

/-- The actual sectionwise right adjoint, evaluating at `Z × C → Z` (the product order
used by Mathlib's `Over.star`). The scalar map is restriction along the other projection.
Source: Stacks 03CE (blueprint: lem-sp-subterminal-derived-image-calculus). -/
abbrev direct {C : Type u} [SmallCategory C] [HasFiniteLimits C]
    {J : GrothendieckTopology C} (R : Sheaf J RingCat.{max u r}) (Z : C) :=
  SheafOfModules.pushforward.{max u r} (SheafOfModules.pushforwardOver (R := R) Z)

/-- The overlap map is the transpose of the restricted counit.
Source: Stacks 08DG (blueprint: lem-sp-subterminal-derived-image-calculus). -/
def overlap {A : Type a} [Category.{va} A]
    {B : Type b} [Category.{vb} B] {D : Type w} [Category.{r} D]
    {f : A ⥤ B} {g : B ⥤ A} {h : A ⥤ D} {k : D ⥤ A} {t : B ⥤ D}
    (adj : f ⊣ g) (adjW : h ⊣ k) (comp : h ≅ f ⋙ t) (X : B) :
    g.obj X ⟶ k.obj (t.obj X) :=
  adjW.homEquiv _ _ (comp.hom.app (g.obj X) ≫ t.map (adj.counit.app X))

/-- The forgetful change from commutative ring sheaves to ring sheaves.
Source: Stacks 03CE (blueprint: lem-sp-subterminal-derived-image-calculus). -/
abbrev ring {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{max u r}) : Sheaf J RingCat.{max u r} :=
  (sheafCompose J (forget₂ CommRingCat RingCat)).obj R

/-- The recorded module category, with coefficient and site universes both retained.
Source: Stacks 03CE (blueprint: lem-sp-subterminal-derived-image-calculus). -/
abbrev modules {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{max u r}) := ringedSiteModules.{max u r} (ring R)

/-- The recorded module category on the localized ringed site.
Source: Stacks 03CE (blueprint: lem-sp-subterminal-derived-image-calculus). -/
abbrev sliceModules {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{max u r}) (Z : C) :=
  ringedSiteModules.{max u r} ((ring.{u, r} R).over Z)

/-- The sectionwise identity for iterated restriction, on complexes.
Source: Stacks 03DH (blueprint: lem-sp-subterminal-derived-image-calculus). -/
def restrictionComp {C : Type u} [SmallCategory C] [HasFiniteLimits C]
    {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{max u r})
    {X Y : C} (f : X ⟶ Y) :
    (SheafOfModules.overFunctor.{max u r} (ring R) X).mapHomologicalComplex (.up ℤ) ≅
      (SheafOfModules.overFunctor.{max u r} (ring R) Y).mapHomologicalComplex (.up ℤ) ⋙
        (SheafOfModules.overMap.{max u r} (ring R) f).mapHomologicalComplex (.up ℤ) :=
  NatIso.mapHomologicalComplex
    (SheafOfModules.overFunctorMap.{max u r} (ring R) f).symm (.up ℤ)

universe d vd wd

/-- Compatibility of iterated derived restriction with the termwise product comparison.
Source: Stacks 03DH and 08DG (blueprint: lem-sp-subterminal-derived-image-calculus). -/
def CompositionNormalization
    {A : Type a} [Category.{va} A] [Abelian A]
    {B : Type b} [Category.{vb} B] [Abelian B]
    {D : Type d} [Category.{vd} D] [Abelian D]
    [HasDerivedCategory.{wa} A] [HasDerivedCategory.{wb} B] [HasDerivedCategory.{wd} D]
    {F : A ⥤ B} {G : B ⥤ D} {H : A ⥤ D} [F.Additive] [G.Additive] [H.Additive]
    {f : DerivedCategory A ⥤ DerivedCategory B}
    {g : DerivedCategory B ⥤ DerivedCategory D}
    {h : DerivedCategory A ⥤ DerivedCategory D}
    (qF : DerivedCategory.Q ⋙ f ≅ F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (qG : DerivedCategory.Q ⋙ g ≅ G.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (qH : DerivedCategory.Q ⋙ h ≅ H.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (c : h ≅ f ⋙ g)
    (t : H.mapHomologicalComplex (.up ℤ) ≅
      F.mapHomologicalComplex (.up ℤ) ⋙ G.mapHomologicalComplex (.up ℤ)) : Prop :=
  ∀ M : CochainComplex A ℤ,
    c.hom.app (DerivedCategory.Q.obj M) ≫ g.map (qF.hom.app M) ≫
      qG.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj M) =
        qH.hom.app M ≫ DerivedCategory.Q.map (t.hom.app M)

universe q0 qU qV qW v0 vU vV vW

/-- The natural comparison isomorphisms and their canonical mate equations.
Source: Stacks 08DG and 03CE (blueprint: lem-sp-subterminal-derived-image-calculus).
This auxiliary record lists exactly the comparison and overlap assertions of the node.
The six final laws are the two unit identities, two cross identities and two W identities. -/
structure Comparisons
    {D0 : Type q0} [Category.{v0} D0] {DU : Type qU} [Category.{vU} DU]
    {DV : Type qV} [Category.{vV} DV] {DW : Type qW} [Category.{vW} DW]
    {rU : D0 ⥤ DU} {rV : D0 ⥤ DV} {rW : D0 ⥤ DW}
    {kU : DU ⥤ DW} {kV : DV ⥤ DW}
    {RU : DU ⥤ D0} {RV : DV ⥤ D0} {RW : DW ⥤ D0}
    {KU : DW ⥤ DU} {KV : DW ⥤ DV}
    (adjU : rU ⊣ RU) (adjV : rV ⊣ RV) (adjW : rW ⊣ RW)
    (adjKU : kU ⊣ KU) (adjKV : kV ⊣ KV)
    (cU : rW ≅ rU ⋙ kU) (cV : rW ≅ rV ⋙ kV) where
  eU : RU ⋙ rU ≅ 𝟭 _
  eV : RV ⋙ rV ≅ 𝟭 _
  eW : RW ⋙ rW ≅ 𝟭 _
  eUV : RV ⋙ rU ≅ kV ⋙ KU
  eVU : RU ⋙ rV ≅ kU ⋙ KV
  eUW : RW ⋙ rU ≅ KU
  eVW : RW ⋙ rV ≅ KV
  dU : KU ⋙ RU ≅ RW
  dV : KV ⋙ RV ≅ RW
  selfU : eU.hom = adjU.counit
  selfV : eV.hom = adjV.counit
  selfW : eW.hom = adjW.counit
  crossUV : ∀ B, eUV.hom.app B = adjKU.unit.app (rU.obj (RV.obj B)) ≫
      KU.map (cU.inv.app (RV.obj B) ≫
        cV.hom.app (RV.obj B) ≫ kV.map (adjV.counit.app B))
  crossVU : ∀ B, eVU.hom.app B = adjKV.unit.app (rV.obj (RU.obj B)) ≫
      KV.map (cV.inv.app (RU.obj B) ≫
        cU.hom.app (RU.obj B) ≫ kU.map (adjU.counit.app B))
  toUW : ∀ D, eUW.hom.app D = adjKU.unit.app (rU.obj (RW.obj D)) ≫
      KU.map (cU.inv.app (RW.obj D) ≫ adjW.counit.app D)
  compositeU : ∀ D, dU.hom.app D = adjW.homEquiv _ _
      (cU.hom.app (RU.obj (KU.obj D)) ≫
        kU.map (adjU.counit.app (KU.obj D)) ≫ adjKU.counit.app D)
  toVW : ∀ D, eVW.hom.app D = adjKV.unit.app (rV.obj (RW.obj D)) ≫
      KV.map (cV.inv.app (RW.obj D) ≫ adjW.counit.app D)
  compositeV : ∀ D, dV.hom.app D = adjW.homEquiv _ _
      (cV.hom.app (RV.obj (KV.obj D)) ≫
        kV.map (adjV.counit.app (KV.obj D)) ≫ adjKV.counit.app D)
  overlapUnitU : ∀ A, rU.map (overlap adjU adjW cU A) ≫
      eUW.hom.app (kU.obj A) = eU.hom.app A ≫ adjKU.unit.app A
  overlapCrossU : ∀ B, rU.map (overlap adjV adjW cV B) ≫
      eUW.hom.app (kV.obj B) = eUV.hom.app B
  overlapWU : ∀ A, rW.map (overlap adjU adjW cU A) ≫
      eW.hom.app (kU.obj A) = cU.hom.app (RU.obj A) ≫ kU.map (eU.hom.app A)
  overlapUnitV : ∀ A, rV.map (overlap adjV adjW cV A) ≫
      eVW.hom.app (kV.obj A) = eV.hom.app A ≫ adjKV.unit.app A
  overlapCrossV : ∀ B, rV.map (overlap adjU adjW cU B) ≫
      eVW.hom.app (kU.obj B) = eVU.hom.app B
  overlapWV : ∀ A, rW.map (overlap adjV adjW cV A) ≫
      eW.hom.app (kV.obj A) = cV.hom.app (RV.obj A) ≫ kV.map (eV.hom.app A)

universe e ve we t vt
open CategoryTheory.Abelian Opposite
attribute [local instance 20000] smallSheafify smallLocalCriterion
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

section SitePairs
private def makeDerivedPair
    {A : Type a} [Category.{va} A] [Abelian A]
    {B : Type b} [Category.{vb} B] [Abelian B]
    [HasDerivedCategory.{wa} A] [HasDerivedCategory.{wb} B]
    [HasKInjectiveResolutions B]
    (F : A ⥤ B) (G : B ⥤ A) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [F.PreservesKInjectiveComplexes]
    (ordinary : F ⊣ G)
    (hA : ∀ M : CochainComplex A ℤ,
      ∃ (I : CochainComplex A ℤ) (i : M ⟶ I), QuasiIso i ∧ I.IsKInjective)
    (hB : ∀ M : CochainComplex B ℤ,
      ∃ (I : CochainComplex B ℤ) (i : M ⟶ I), QuasiIso i ∧ I.IsKInjective) :
    DerivedPair F G ordinary := by
  let : G.PreservesKInjectiveComplexes := ordinary.preservesKInjectiveComplexes
  refine
    { left := F.mapDerivedCategory
      right := G.rightDerivedFunctor
      adj := ordinary.mapDerivedCategoryRightDerivedAdjunction
      qF := F.mapDerivedCategoryFactors
      qG :=
        { app := fun I ↦ G.rightDerivedFunctorUnit.app
            ((HomotopyCategory.quotient B (.up ℤ)).obj I)
          naturality := fun _ _ f ↦ G.rightDerivedFunctorUnit.naturality
            ((HomotopyCategory.quotient B (.up ℤ)).map f) }
      qG_iso := fun I hI ↦ ?_
      restrict_injective := fun I hI ↦ inferInstance
      direct_injective := fun I hI ↦ inferInstance
      resolutions_source := hA
      resolutions_target := hB
      transpose := ?_ }
  · infer_instance
  · intro M I f hI
    let πA := HomotopyCategory.quotient A (.up ℤ)
    let πB := HomotopyCategory.quotient B (.up ℤ)
    let d := ordinary.mapDerivedCategoryRightDerivedAdjunction
    have hη := (ordinary.mapHomotopyCategory (.up ℤ)).derivedη_fac_app
      (HomotopyCategory.quasiIso A (.up ℤ)) F.mapDerivedCategoryFactorsh.hom
      G.rightDerivedFunctorUnit (πA.obj M)
    have he : F.mapDerivedCategoryFactorsh.hom.app (πA.obj M) =
        F.mapDerivedCategoryFactors.hom.app M := by
      simp only [πA, Functor.mapDerivedCategoryFactorsh_hom_app,
        DerivedCategory.quotientCompQhIso,
        HomologicalComplexUpToQuasiIso.quotientCompQhIso,
        Functor.mapHomotopyCategoryFactors, Quotient.lift.isLift_inv,
        Quotient.lift.isLift_hom, Functor.comp_obj, Functor.map_id, Category.comp_id]
      erw [Functor.map_id, Category.id_comp, Category.comp_id]
    rw [he, Adjunction.mapHomotopyCategory_unit_app_quotient] at hη
    change d.unit.app (DerivedCategory.Q.obj M) ≫
      G.rightDerivedFunctor.map (F.mapDerivedCategoryFactors.hom.app M) =
        DerivedCategory.Q.map ((ordinary.mapHomologicalComplex (.up ℤ)).unit.app M) ≫
          G.rightDerivedFunctorUnit.app (πB.obj
            ((F.mapHomologicalComplex (.up ℤ)).obj M)) at hη
    change d.homEquiv _ _ (_ ≫ DerivedCategory.Q.map f) = _
    rw [Adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc, hη,
      Category.assoc]
    have hn := G.rightDerivedFunctorUnit.naturality (πB.map f)
    change DerivedCategory.Q.map ((G.mapHomologicalComplex (.up ℤ)).map f) ≫
      G.rightDerivedFunctorUnit.app (πB.obj I) =
        G.rightDerivedFunctorUnit.app (πB.obj
          ((F.mapHomologicalComplex (.up ℤ)).obj M)) ≫
            G.rightDerivedFunctor.map (DerivedCategory.Q.map f) at hn
    rw [← hn, ← DerivedCategory.Q.map_comp_assoc]
    rfl


private theorem existsResolution
    {A : Type a} [Category.{va} A] [Abelian A] [HasKInjectiveResolutions A]
    (M : CochainComplex A ℤ) :
    ∃ (I : CochainComplex A ℤ) (i : M ⟶ I), QuasiIso i ∧ I.IsKInjective := by
  obtain ⟨I, hI, i, _, hi⟩ := HasKInjectiveResolutions.exists_isKInjective M
  exact ⟨I, i, hi, hI⟩

private def restrictionPair
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{max u r}) (Z : C) [HasFiniteLimits C]
    [HasSheafify J AddCommGrpCat.{max u r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u r}]
    [HasSheafify (J.over Z) AddCommGrpCat.{max u r}]
    [(J.over Z).WEqualsLocallyBijective AddCommGrpCat.{max u r}]
    [HasDerivedCategory.{wa} (modules.{u, r} R)]
    [HasDerivedCategory.{wb} (sliceModules.{u, r} R Z)] :
    DerivedPair (SheafOfModules.overFunctor.{max u r} (ring.{u, r} R) Z)
      (direct.{u, r} (ring.{u, r} R) Z) (SheafOfModules.overPushforwardOverAdj Z) := by
  have : IsGrothendieckAbelian.{max u r} (modules.{u, r} R) :=
    (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{u, u, r}
      J R).1
  have : IsGrothendieckAbelian.{max u r} (sliceModules.{u, r} R Z) :=
    (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{u, u, r}
      (J.over Z) (R.over Z)).1
  have := (SheafOfModules.overFunctor_exact_ofUniverses.{u, u, max u r} (ring.{u, r} R) Z).1
  have := (SheafOfModules.overFunctor_exact_ofUniverses.{u, u, max u r} (ring.{u, r} R) Z).2
  have := SheafOfModules.overFunctor_preservesKInjectiveComplexes_ofUniverses.{u, u, max u r}
    (ring.{u, r} R) Z
  exact makeDerivedPair (SheafOfModules.overFunctor.{max u r} (ring.{u, r} R) Z)
    (direct.{u, r} (ring.{u, r} R) Z) (SheafOfModules.overPushforwardOverAdj Z)
    existsResolution existsResolution

private def relocalizationPair
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{max u r}) {X Y : C} (f : X ⟶ Y) [HasFiniteLimits C]
    [HasSheafify (J.over Y) AddCommGrpCat.{max u r}]
    [(J.over Y).WEqualsLocallyBijective AddCommGrpCat.{max u r}]
    [HasSheafify (J.over X) AddCommGrpCat.{max u r}]
    [(J.over X).WEqualsLocallyBijective AddCommGrpCat.{max u r}]
    [HasDerivedCategory.{wa} (sliceModules.{u, r} R Y)]
    [HasDerivedCategory.{wb} (sliceModules.{u, r} R X)] :
    DerivedPair (SheafOfModules.overMap.{max u r} (ring.{u, r} R) f)
      (SheafOfModules.overPullback.{max u r} (ring.{u, r} R) f)
      (SheafOfModules.overMapPushforwardAdj (ring.{u, r} R) f) := by
  have : IsGrothendieckAbelian.{max u r} (sliceModules.{u, r} R Y) :=
    (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{u, u, r}
      (J.over Y) (R.over Y)).1
  have : IsGrothendieckAbelian.{max u r} (sliceModules.{u, r} R X) :=
    (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{u, u, r}
      (J.over X) (R.over X)).1
  have := (SheafOfModules.overMap_exact_ofUniverses.{u, u, max u r} (ring.{u, r} R) f).1
  have := (SheafOfModules.overMap_exact_ofUniverses.{u, u, max u r} (ring.{u, r} R) f).2
  have := SheafOfModules.overMap_preservesKInjectiveComplexes_ofUniverses.{u, u, max u r}
    (ring.{u, r} R) f
  exact makeDerivedPair (SheafOfModules.overMap.{max u r} (ring.{u, r} R) f)
    (SheafOfModules.overPullback.{max u r} (ring.{u, r} R) f)
    (SheafOfModules.overMapPushforwardAdj (ring.{u, r} R) f)
    existsResolution existsResolution


end SitePairs

section PairLaws
variable {A : Type a} [Category.{va} A] [Abelian A]
  {B : Type b} [Category.{vb} B] [Abelian B]
  [HasDerivedCategory.{wa} A] [HasDerivedCategory.{wb} B]
  {F : A ⥤ B} {G : B ⥤ A} [F.Additive] [G.Additive]
  {ordinary : F ⊣ G} (p : DerivedPair F G ordinary)

private theorem pair_counit (I : CochainComplex B ℤ) (hI : I.IsKInjective) :
    p.left.map (p.qG.app I) ≫ p.adj.counit.app (DerivedCategory.Q.obj I) =
      p.qF.hom.app ((G.mapHomologicalComplex (.up ℤ)).obj I) ≫
        DerivedCategory.Q.map ((ordinary.mapHomologicalComplex (.up ℤ)).counit.app I) := by
  have ht := p.transpose ((G.mapHomologicalComplex (.up ℤ)).obj I) I
    ((ordinary.mapHomologicalComplex (.up ℤ)).counit.app I) hI
  have hid : (ordinary.mapHomologicalComplex (.up ℤ)).homEquiv _ _
      ((ordinary.mapHomologicalComplex (.up ℤ)).counit.app I) = 𝟙 _ := by
    rw [Adjunction.homEquiv_unit, Adjunction.right_triangle_components]
  erw [hid, Functor.map_id, Category.id_comp] at ht
  have hh := congrArg (p.adj.homEquiv _ _).symm ht
  simpa only [Equiv.symm_apply_apply, Adjunction.homEquiv_counit] using hh.symm

private theorem pair_counit_iso
    [IsIso ordinary.counit] : IsIso p.adj.counit := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro X
  obtain ⟨I, i, hi, hI⟩ := p.resolutions_target (DerivedCategory.Q.objPreimage X)
  have := hi
  have hq := p.qG_iso I hI
  have hc : IsIso ((ordinary.mapHomologicalComplex (.up ℤ)).counit.app I) := by
    have : ∀ n, IsIso (((ordinary.mapHomologicalComplex (.up ℤ)).counit.app I).f n) :=
      fun n ↦ inferInstanceAs (IsIso (ordinary.counit.app (I.X n)))
    exact HomologicalComplex.Hom.isIso_of_components _
  have hd : IsIso (p.adj.counit.app (DerivedCategory.Q.obj I)) := by
    have he := pair_counit p I hI
    have : IsIso (p.left.map (p.qG.app I) ≫
        p.adj.counit.app (DerivedCategory.Q.obj I)) := by rw [he]; infer_instance
    exact IsIso.of_isIso_comp_left (p.left.map (p.qG.app I)) _
  let e : X ≅ DerivedCategory.Q.obj I :=
    (DerivedCategory.Q.objObjPreimageIso X).symm ≪≫ asIso (DerivedCategory.Q.map i)
  have hn := p.adj.counit.naturality e.hom
  have : IsIso ((p.right ⋙ p.left).map e.hom ≫
      p.adj.counit.app (DerivedCategory.Q.obj I)) := inferInstance
  rw [hn] at this
  exact IsIso.of_isIso_comp_right _ ((𝟭 _).map e.hom)


end PairLaws

section Underived

private theorem ordinary_counit_iso
    {C : Type u} [SmallCategory C] [HasFiniteLimits C]
    {J : GrothendieckTopology C} (R : Sheaf J RingCat.{max u r})
    (Z : C) (hZ : IsSubterminal Z) :
    IsIso ((SheafOfModules.overPushforwardOverAdj (R := R) Z :
      SheafOfModules.overFunctor.{max u r} R Z ⊣ direct R Z)).counit := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro M
  rw [← isIso_iff_of_reflects_iso _
    (SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf _)]
  rw [NatTrans.isIso_iff_isIso_app]
  intro X
  have : (Over.forget Z).Full := by
    constructor
    intro V V' f
    exact ⟨Over.homMk f (hZ _ _), rfl⟩
  have : IsIso (Over.forgetAdjStar Z).unit := inferInstance
  change IsIso (M.val.presheaf.map ((Over.forgetAdjStar Z).unit.app X.unop).op)
  infer_instance


end Underived

section Formal
section Formal
variable {A : Type a} [Category.{va} A]
  {B : Type b} [Category.{vb} B] {D : Type d} [Category.{vd} D]
  {f : A ⥤ B} {h : A ⥤ D} {k : D ⥤ A}
  {q : B ⥤ D} {Q : D ⥤ B}
  (adjW : h ⊣ k) (adjK : q ⊣ Q) (c : h ≅ f ⋙ q)

private def restrictionMate : k ⋙ f ⟶ Q where
  app X := adjK.homEquiv _ _ (c.inv.app (k.obj X) ≫ adjW.counit.app X)
  naturality := by
    intro X Y a
    change f.map (k.map a) ≫ adjK.homEquiv _ _ _ =
      adjK.homEquiv _ _ _ ≫ Q.map a
    rw [← adjK.homEquiv_naturality_left, ← adjK.homEquiv_naturality_right]
    congr 1
    change q.map (f.map (k.map a)) ≫ (c.inv.app (k.obj Y) ≫
      adjW.counit.app Y) = (c.inv.app (k.obj X) ≫ adjW.counit.app X) ≫ a
    have hc := c.inv.naturality (k.map a)
    dsimp only [Functor.comp_map] at hc
    rw [← Category.assoc, hc, Category.assoc]
    erw [adjW.counit.naturality]
    simp only [Functor.id_map, Category.assoc]

private theorem restrictionMate_formula {X : A} {Y : D} (m : X ⟶ k.obj Y) :
    f.map m ≫ (restrictionMate adjW adjK c).app Y =
      adjK.homEquiv _ _ (c.inv.app X ≫ h.map m ≫ adjW.counit.app Y) := by
  change f.map m ≫ adjK.homEquiv _ _ _ = _
  rw [← adjK.homEquiv_naturality_left]
  congr 1
  erw [← Category.assoc, c.inv.naturality]
  exact Category.assoc _ _ _

private theorem overlap_counit
    {g : B ⥤ A} (adj : f ⊣ g) (X : B) :
    h.map (overlap adj adjW c X) ≫ adjW.counit.app (q.obj X) =
      c.hom.app (g.obj X) ≫ q.map (adj.counit.app X) := by
  exact (adjW.homEquiv _ _).symm_apply_apply _

private theorem restrictionMate_overlap_unit
    {g : B ⥤ A} (adj : f ⊣ g) (X : B) :
    f.map (overlap adj adjW c X) ≫ (restrictionMate adjW adjK c).app (q.obj X) =
      adj.counit.app X ≫ adjK.unit.app X := by
  rw [restrictionMate_formula, overlap_counit]
  rw [← Category.assoc, Iso.inv_hom_id_app]
  erw [Category.id_comp]
  rw [Adjunction.homEquiv_unit]
  exact (adjK.unit.naturality (adj.counit.app X)).symm

private theorem restrictionMate_iso
    {g : B ⥤ A} (adj : f ⊣ g) [IsIso adj.counit] :
    IsIso (restrictionMate adjW adjK c) := by
  let d := conjugateIsoEquiv (adj.comp adjK) adjW c
  rw [NatTrans.isIso_iff_isIso_app]
  intro X
  have hd : h.map (d.hom.app X) ≫ adjW.counit.app X =
      c.hom.app (g.obj (Q.obj X)) ≫ q.map (adj.counit.app (Q.obj X)) ≫
        adjK.counit.app X := by
    simpa only [d, conjugateIsoEquiv_apply_hom, Adjunction.comp_counit_app,
      Category.assoc, Functor.comp_obj] using conjugateEquiv_counit (adj.comp adjK) adjW c.hom X
  have he : f.map (d.hom.app X) ≫ (restrictionMate adjW adjK c).app X =
      adj.counit.app (Q.obj X) := by
    rw [restrictionMate_formula, hd]
    dsimp only [Functor.comp_obj]
    rw [Iso.inv_hom_id_app_assoc]
    rw [adjK.homEquiv_naturality_left, Adjunction.homEquiv_unit]
    dsimp only [Functor.id_obj]
    rw [Adjunction.right_triangle_components, Category.comp_id]
  have : IsIso (f.map (d.hom.app X) ≫ (restrictionMate adjW adjK c).app X) := by
    rw [he]
    infer_instance
  exact IsIso.of_isIso_comp_left (f.map (d.hom.app X)) _

end Formal

private def overlapNat
    {A : Type a} [Category.{va} A] {B : Type b} [Category.{vb} B]
    {D : Type d} [Category.{vd} D]
    {f : A ⥤ B} {g : B ⥤ A} {h : A ⥤ D} {k : D ⥤ A} {t : B ⥤ D}
    (adj : f ⊣ g) (adjW : h ⊣ k) (c : h ≅ f ⋙ t) : g ⟶ t ⋙ k where
  app X := overlap adj adjW c X
  naturality := by
    intro X Y a
    dsimp [overlap]
    rw [← adjW.homEquiv_naturality_left, ← adjW.homEquiv_naturality_right]
    congr 1
    have hc := c.hom.naturality (g.map a)
    dsimp only [Functor.comp_map] at hc
    rw [← Category.assoc, hc, Category.assoc]
    simp only [Category.assoc, ← t.map_comp]
    erw [adj.counit.naturality]
    rfl

section BuildComparisons
variable
    {D0 : Type q0} [Category.{v0} D0] {DU : Type qU} [Category.{vU} DU]
    {DV : Type qV} [Category.{vV} DV] {DW : Type qW} [Category.{vW} DW]
    {rU : D0 ⥤ DU} {rV : D0 ⥤ DV} {rW : D0 ⥤ DW}
    {kU : DU ⥤ DW} {kV : DV ⥤ DW}
    {RU : DU ⥤ D0} {RV : DV ⥤ D0} {RW : DW ⥤ D0}
    {KU : DW ⥤ DU} {KV : DW ⥤ DV}
    (adjU : rU ⊣ RU) (adjV : rV ⊣ RV) (adjW : rW ⊣ RW)
    (adjKU : kU ⊣ KU) (adjKV : kV ⊣ KV)
    (cU : rW ≅ rU ⋙ kU) (cV : rW ≅ rV ⋙ kV)

private def crossMate : RV ⋙ rU ⟶ kV ⋙ KU :=
  Functor.whiskerRight (overlapNat adjV adjW cV) rU ≫
    Functor.whiskerLeft kV (restrictionMate adjW adjKU cU)

private theorem crossMate_app (B : DV) :
    (crossMate adjV adjW adjKU cU cV).app B =
      adjKU.unit.app (rU.obj (RV.obj B)) ≫
        KU.map (cU.inv.app (RV.obj B) ≫ cV.hom.app (RV.obj B) ≫
          kV.map (adjV.counit.app B)) := by
  change rU.map (overlap adjV adjW cV B) ≫
    (restrictionMate adjW adjKU cU).app (kV.obj B) = _
  rw [restrictionMate_formula, overlap_counit]
  rfl

private def buildComparisons
    [IsIso adjU.counit] [IsIso adjV.counit] [IsIso adjW.counit]
    [IsIso (restrictionMate adjW adjKU cU)]
    [IsIso (restrictionMate adjW adjKV cV)]
    [IsIso (crossMate adjV adjW adjKU cU cV)]
    [IsIso (crossMate adjU adjW adjKV cV cU)] :
    Comparisons adjU adjV adjW adjKU adjKV cU cV where
  eU := asIso adjU.counit
  eV := asIso adjV.counit
  eW := asIso adjW.counit
  eUV := asIso (crossMate adjV adjW adjKU cU cV)
  eVU := asIso (crossMate adjU adjW adjKV cV cU)
  eUW := asIso (restrictionMate adjW adjKU cU)
  eVW := asIso (restrictionMate adjW adjKV cV)
  dU := conjugateIsoEquiv (adjU.comp adjKU) adjW cU
  dV := conjugateIsoEquiv (adjV.comp adjKV) adjW cV
  selfU := rfl
  selfV := rfl
  selfW := rfl
  crossUV := crossMate_app adjV adjW adjKU cU cV
  crossVU := crossMate_app adjU adjW adjKV cV cU
  toUW := fun _ ↦ rfl
  toVW := fun _ ↦ rfl
  compositeU := by
    intro D
    simp only [conjugateIsoEquiv_apply_hom, conjugateEquiv_apply_app,
      Adjunction.comp_counit_app, Adjunction.homEquiv_unit, Functor.map_comp,
      Functor.comp_obj]
  compositeV := by
    intro D
    simp only [conjugateIsoEquiv_apply_hom, conjugateEquiv_apply_app,
      Adjunction.comp_counit_app, Adjunction.homEquiv_unit, Functor.map_comp,
      Functor.comp_obj]
  overlapUnitU := restrictionMate_overlap_unit adjW adjKU cU adjU
  overlapUnitV := restrictionMate_overlap_unit adjW adjKV cV adjV
  overlapCrossU := fun _ ↦ rfl
  overlapCrossV := fun _ ↦ rfl
  overlapWU := overlap_counit adjW cU adjU
  overlapWV := overlap_counit adjW cV adjV

end BuildComparisons

end Formal

section Composition
section
variable {A : Type a} [Category.{va} A] [Abelian A]
  {B : Type b} [Category.{vb} B] [Abelian B]
  {E : Type e} [Category.{ve} E] [Abelian E]
  [HasDerivedCategory.{wa} A] [HasDerivedCategory.{wb} B]
  [HasDerivedCategory.{we} E]
  (F : A ⥤ B) (G : B ⥤ E) (H : A ⥤ E)
  [F.Additive] [G.Additive] [H.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits H] [PreservesFiniteColimits H]

private def exactComposition (t : H ≅ F ⋙ G) :
    H.mapDerivedCategory ≅ F.mapDerivedCategory ⋙ G.mapDerivedCategory :=
  (Functor.exactDerivedRestrictionComposition F G H t.symm).symm

private theorem exactComposition_normalization (t : H ≅ F ⋙ G)
    (M : CochainComplex A ℤ) :
    (exactComposition F G H t).hom.app (DerivedCategory.Q.obj M) ≫
      G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app M) ≫
      G.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj M) =
    H.mapDerivedCategoryFactors.hom.app M ≫
      DerivedCategory.Q.map ((NatIso.mapHomologicalComplex t (.up ℤ)).hom.app M) := by
  apply (cancel_epi ((exactComposition F G H t).inv.app (DerivedCategory.Q.obj M))).mp
  rw [Iso.inv_hom_id_app_assoc]
  have hh := Functor.exactDerivedRestrictionComposition_hom_factors F G H t.symm M
  change _ = (Functor.exactDerivedRestrictionComposition F G H t.symm).hom.app _ ≫ _
  rw [← Category.assoc, hh]
  simp only [Category.assoc]
  have ht : (NatIso.mapHomologicalComplex t.symm (.up ℤ)).hom.app M ≫
      (NatIso.mapHomologicalComplex t (.up ℤ)).hom.app M = 𝟙 _ :=
    (NatIso.mapHomologicalComplex t (.up ℤ)).inv_hom_id_app M
  erw [← DerivedCategory.Q.map_comp, ht, DerivedCategory.Q.map_id, Category.comp_id]

end

private theorem restrictionComp_component
    {C : Type u} [SmallCategory C] [HasFiniteLimits C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{max u r}) {X Y : C} (f : X ⟶ Y)
    (M : CochainComplex (modules.{u, r} R) ℤ) :
    (restrictionComp.{u, r} R f).hom.app M =
      (NatIso.mapHomologicalComplex (SheafOfModules.overFunctorMap (ring.{u, r} R) f).symm
        (.up ℤ)).hom.app M := by
  rfl


end Composition

section LiftOverlap
section
variable {A : Type a} [Category.{va} A] [Abelian A]
  {B : Type b} [Category.{vb} B] [Abelian B]
  {D : Type d} [Category.{vd} D] [Abelian D]
  [HasDerivedCategory.{wa} A] [HasDerivedCategory.{wb} B]
  [HasDerivedCategory.{wd} D]
  {F : A ⥤ B} {G : B ⥤ A} [F.Additive] [G.Additive]
  {H : A ⥤ D} {K : D ⥤ A} [H.Additive] [K.Additive]
  {adjF : F ⊣ G} {adjH : H ⊣ K}
  (p : DerivedPair F G adjF) (s : DerivedPair H K adjH)
  (T : B ⥤ D) [T.Additive]
  (Td : DerivedCategory B ⥤ DerivedCategory D)
  (qT : DerivedCategory.Q ⋙ Td ≅ T.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
  (c : s.left ≅ p.left ⋙ Td)
  (t : H.mapHomologicalComplex (.up ℤ) ≅
    F.mapHomologicalComplex (.up ℤ) ⋙ T.mapHomologicalComplex (.up ℤ))
  (hc : CompositionNormalization p.qF qT s.qF c t)

private def ordinaryOverlap (I : CochainComplex B ℤ) :
    (G.mapHomologicalComplex (.up ℤ)).obj I ⟶
      (K.mapHomologicalComplex (.up ℤ)).obj
        ((T.mapHomologicalComplex (.up ℤ)).obj I) :=
  (adjH.mapHomologicalComplex (.up ℤ)).homEquiv _ _
    (t.hom.app ((G.mapHomologicalComplex (.up ℤ)).obj I) ≫
      (T.mapHomologicalComplex (.up ℤ)).map
        ((adjF.mapHomologicalComplex (.up ℤ)).counit.app I))

omit [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory D] in
private theorem ordinaryOverlap_f
    (t0 : H ≅ F ⋙ T)
    (ht : ∀ (M : CochainComplex A ℤ) (n : ℤ),
      (t.hom.app M).f n = t0.hom.app (M.X n))
    (I : CochainComplex B ℤ) (n : ℤ) :
    (ordinaryOverlap (adjF := adjF) (adjH := adjH) T t I).f n =
      adjH.homEquiv _ _
        (t0.hom.app (G.obj (I.X n)) ≫ T.map (adjF.counit.app (I.X n))) := by
  simp only [ordinaryOverlap, Adjunction.homEquiv_unit, HomologicalComplex.comp_f,
    Functor.mapHomologicalComplex_map_f, Adjunction.mapHomologicalComplex_unit_app_f,
    Adjunction.mapHomologicalComplex_counit_app_f, ht,
    Functor.mapHomologicalComplex_obj_X]

omit [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory D] in
private theorem ordinaryOverlap_isIso_after
    {E : Type e} [Category.{ve} E] [Preadditive E]
    (S : A ⥤ E) [S.Additive] (t0 : H ≅ F ⋙ T)
    (ht : ∀ (M : CochainComplex A ℤ) (n : ℤ),
      (t.hom.app M).f n = t0.hom.app (M.X n))
    (hOrd : ∀ M : B, IsIso (S.map (adjH.homEquiv _ _
      (t0.hom.app (G.obj M) ≫ T.map (adjF.counit.app M)))))
    (I : CochainComplex B ℤ) :
    IsIso ((S.mapHomologicalComplex (.up ℤ)).map
      (ordinaryOverlap (adjF := adjF) (adjH := adjH) T t I)) := by
  have : ∀ n : ℤ, IsIso (((S.mapHomologicalComplex (.up ℤ)).map
      (ordinaryOverlap (adjF := adjF) (adjH := adjH) T t I)).f n) := by
    intro n
    rw [Functor.mapHomologicalComplex_map_f, ordinaryOverlap_f T t t0 ht]
    exact hOrd (I.X n)
  exact HomologicalComplex.Hom.isIso_of_components _

include hc in
private theorem overlap_representative
    (hp : ∀ (I : CochainComplex B ℤ), I.IsKInjective →
      p.left.map (p.qG.app I) ≫ p.adj.counit.app (DerivedCategory.Q.obj I) =
        p.qF.hom.app ((G.mapHomologicalComplex (.up ℤ)).obj I) ≫
          DerivedCategory.Q.map ((adjF.mapHomologicalComplex (.up ℤ)).counit.app I))
    (I : CochainComplex B ℤ) (hI : I.IsKInjective)
    (hTI : CochainComplex.IsKInjective ((T.mapHomologicalComplex (.up ℤ)).obj I)) :
    p.qG.app I ≫ overlap p.adj s.adj c (DerivedCategory.Q.obj I) ≫
        s.right.map (qT.hom.app I) =
      DerivedCategory.Q.map (ordinaryOverlap (adjF := adjF) (adjH := adjH) T t I) ≫
        s.qG.app ((T.mapHomologicalComplex (.up ℤ)).obj I) := by
  dsimp only [overlap]
  erw [← Category.assoc, ← s.adj.homEquiv_naturality_left,
    ← s.adj.homEquiv_naturality_right]
  have hn := c.hom.naturality (p.qG.app I)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hn
  erw [← Category.assoc, hn]
  simp only [Category.assoc]
  erw [← Td.map_comp_assoc, hp I hI, Td.map_comp]
  simp only [Category.assoc]
  have hq := qT.hom.naturality ((adjF.mapHomologicalComplex (.up ℤ)).counit.app I)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hq
  erw [hq]
  have hc' := congrArg
    (fun f ↦ f ≫ DerivedCategory.Q.map
      ((T.mapHomologicalComplex (.up ℤ)).map
        ((adjF.mapHomologicalComplex (.up ℤ)).counit.app I)))
    (hc ((G.mapHomologicalComplex (.up ℤ)).obj I))
  simp only [Category.assoc] at hc'
  erw [hc', ← DerivedCategory.Q.map_comp]
  exact s.transpose _ _ _ hTI

include hc in
private theorem overlap_iso_after
    {E : Type e} [Category.{ve} E] [Abelian E] [HasDerivedCategory.{we} E]
    (S : A ⥤ E) [S.Additive]
    (Sd : DerivedCategory A ⥤ DerivedCategory E)
    (qS : DerivedCategory.Q ⋙ Sd ≅ S.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (hp : ∀ (I : CochainComplex B ℤ), I.IsKInjective →
      p.left.map (p.qG.app I) ≫ p.adj.counit.app (DerivedCategory.Q.obj I) =
        p.qF.hom.app ((G.mapHomologicalComplex (.up ℤ)).obj I) ≫
          DerivedCategory.Q.map ((adjF.mapHomologicalComplex (.up ℤ)).counit.app I))
    (hT : ∀ (I : CochainComplex B ℤ), I.IsKInjective →
      CochainComplex.IsKInjective ((T.mapHomologicalComplex (.up ℤ)).obj I))
    (hOrd : ∀ I : CochainComplex B ℤ,
      IsIso ((S.mapHomologicalComplex (.up ℤ)).map
        (ordinaryOverlap (adjF := adjF) (adjH := adjH) T t I)))
    (X : DerivedCategory B) : IsIso (Sd.map (overlap p.adj s.adj c X)) := by
  have hrep (I : CochainComplex B ℤ) (hI : I.IsKInjective) :
      IsIso (Sd.map (overlap p.adj s.adj c (DerivedCategory.Q.obj I))) := by
    have := p.qG_iso I hI
    have := s.qG_iso _ (hT I hI)
    have hm : IsIso (Sd.map (DerivedCategory.Q.map
        (ordinaryOverlap (adjF := adjF) (adjH := adjH) T t I))) := by
      have := hOrd I
      have hn := qS.hom.naturality
        (ordinaryOverlap (adjF := adjF) (adjH := adjH) T t I)
      dsimp only [Functor.comp_map] at hn
      have : IsIso (Sd.map (DerivedCategory.Q.map
          (ordinaryOverlap (adjF := adjF) (adjH := adjH) T t I)) ≫
          qS.hom.app _) := by
        erw [hn]
        infer_instance
      exact IsIso.of_isIso_comp_right _ (qS.hom.app _)
    have hcomp : IsIso (Sd.map (p.qG.app I) ≫
        Sd.map (overlap p.adj s.adj c (DerivedCategory.Q.obj I)) ≫
        Sd.map (s.right.map (qT.hom.app I))) := by
      rw [← Sd.map_comp, ← Sd.map_comp,
        overlap_representative p s T Td qT c t hc hp I hI (hT I hI), Sd.map_comp]
      infer_instance
    have : IsIso (Sd.map (overlap p.adj s.adj c (DerivedCategory.Q.obj I)) ≫
        Sd.map (s.right.map (qT.hom.app I))) :=
      IsIso.of_isIso_comp_left (Sd.map (p.qG.app I)) _
    exact IsIso.of_isIso_comp_right _ (Sd.map (s.right.map (qT.hom.app I)))
  obtain ⟨I, i, hi, hI⟩ := p.resolutions_target (DerivedCategory.Q.objPreimage X)
  have := hi
  let e : X ≅ DerivedCategory.Q.obj I :=
    (DerivedCategory.Q.objObjPreimageIso X).symm ≪≫ asIso (DerivedCategory.Q.map i)
  have := hrep I hI
  have hn := (overlapNat p.adj s.adj c).naturality e.hom
  have he := congrArg Sd.map hn
  dsimp only [Functor.comp_map, overlapNat] at he
  rw [Sd.map_comp, Sd.map_comp] at he
  have : IsIso (Sd.map (p.right.map e.hom) ≫
      Sd.map (overlap p.adj s.adj c (DerivedCategory.Q.obj I))) := inferInstance
  rw [he] at this
  exact IsIso.of_isIso_comp_right _ (Sd.map (s.right.map (Td.map e.hom)))

end

end LiftOverlap

section OrdinaryOverlap
set_option maxHeartbeats 400000 in
-- Normalize the termwise adjunction and restriction compositor together.
private theorem ordinary_overlap_iso
    {C : Type u} [SmallCategory C] [HasFiniteLimits C]
    {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{max u r})
    (U V W : C) (hU : IsSubterminal U) (hV : IsSubterminal V)
    [HasSheafify J AddCommGrpCat.{max u r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u r}]
    [HasSheafify (J.over U) AddCommGrpCat.{max u r}]
    [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{max u r}]
    [HasSheafify (J.over V) AddCommGrpCat.{max u r}]
    [(J.over V).WEqualsLocallyBijective AddCommGrpCat.{max u r}]
    [HasSheafify (J.over W) AddCommGrpCat.{max u r}]
    [(J.over W).WEqualsLocallyBijective AddCommGrpCat.{max u r}]
    (f : W ⟶ U) (g : W ⟶ V)
    (hW : IsPullback f g (terminal.from U) (terminal.from V))
    (I : CochainComplex (sliceModules.{u, r} R V) ℤ) :
    IsIso (((SheafOfModules.overFunctor.{max u r} (ring.{u, r} R) U).mapHomologicalComplex
      (.up ℤ)).map (ordinaryOverlap
        (F := SheafOfModules.overFunctor.{max u r} (ring.{u, r} R) V)
        (G := direct.{u, r} (ring.{u, r} R) V)
        (H := SheafOfModules.overFunctor.{max u r} (ring.{u, r} R) W)
        (K := direct.{u, r} (ring.{u, r} R) W)
        (adjF := SheafOfModules.overPushforwardOverAdj (R := ring.{u, r} R) V)
        (adjH := SheafOfModules.overPushforwardOverAdj (R := ring.{u, r} R) W)
        (SheafOfModules.overMap.{max u r} (ring.{u, r} R) g) (restrictionComp.{u, r} R g) I)) := by
  have := hU.mono_terminal_from
  have := hV.mono_terminal_from
  exact ordinaryOverlap_isIso_after
    (A := modules.{u, r} R) (B := sliceModules.{u, r} R V) (D := sliceModules.{u, r} R W)
    (E := sliceModules.{u, r} R U)
    (F := SheafOfModules.overFunctor.{max u r} (ring.{u, r} R) V)
    (G := direct.{u, r} (ring.{u, r} R) V)
    (H := SheafOfModules.overFunctor.{max u r} (ring.{u, r} R) W)
    (K := direct.{u, r} (ring.{u, r} R) W)
    (adjF := SheafOfModules.overPushforwardOverAdj (R := ring.{u, r} R) V)
    (adjH := SheafOfModules.overPushforwardOverAdj (R := ring.{u, r} R) W)
    (SheafOfModules.overMap.{max u r} (ring.{u, r} R) g) (restrictionComp.{u, r} R g)
    (SheafOfModules.overFunctor.{max u r} (ring.{u, r} R) U)
    (SheafOfModules.overFunctorMap.{max u r} (ring.{u, r} R) g).symm
    (fun M n ↦ by rw [restrictionComp_component]; rfl)
    (fun M ↦ ringedTopos_ordinaryCross_restriction.{u, u, max u r, max u r}
      (ring.{u, r} R) U V W f g hW M) I

end OrdinaryOverlap

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe w0 wU wV wW

set_option maxHeartbeats 500000 in
-- Simultaneous elaboration of five adjunctions and their localization comparisons.
/-- Subterminal derived direct-image calculus, with comparisons normalized on representatives.
Source: Stacks 03CE, 08DG, 08FI and 09T5
(blueprint: lem-sp-subterminal-derived-image-calculus).

Proof:
1. Apply lem-trf-slice-subtopos-site-presentation to the underlying sheaf of F.
Give F(Z × C → Z) its addition and the scalar action via R(C) → R(Z × C).
The transpose restricts M(C) to M(Z × C), then applies the given map.
Its inverse restricts along the graph. Naturality and the graph/projection
identities give inverse linear operations. This is the ordinary module adjunction
used below; the same construction in each slice gives both k adjunctions.
2. All four sites are small. Apply prop-pur-kinjective-resolutions-exist to their
restricted rings. Exact extension by zero is left adjoint to restriction by
lem-pur-site-restriction-module-adjunction-exact. Apply
lem-weil-pbc-right-adjoint-preserves-kinjective to that adjunction and then to
restriction/direct image. Thus both functors preserve K-injectives in all pairs.
3. Exact restriction descends termwise by lem-weil-pbc-exact-functor-derived-factorization.
Apply lem-weil-pbc-kinjective-total-derived to additive termwise direct image
followed by Q on homotopy categories. Its cone and shift matrices are unchanged,
so it is triangulated and is computed on K-injectives without another resolution.
4. Combine lem-weil-pbc-kinjective-hom-derived on both sides of the ordinary
adjunction lem-weil-pbc-termwise-adjunction-homotopy. This gives the derived
adjunction with exactly the chain-transpose equation in DerivedPair.
It fixes counits, and units on K-injective source complexes since restriction
preserves K-injectives. Homotopy classes represent all maps between these models.
5. If T → U, subterminality identifies the graph T → U × T with the inverse
projection. Also T ×_U (U × V) ≅ T × V and T × W ≅ T ×_U W. These product
identifications respect scalar restriction and restriction arrows. Interchange U,V.
6. At C the composite direct image evaluates on (C × U) ×_U W ≅ C × W.
This gives the two composition comparisons. Iterated restriction is sectionwise
the identity, exactly overFunctorMap and its termwise comparison.
7. Apply steps 5 and 6 degreewise to K-injective representatives. Step 2 ensures
all intervening complexes remain K-injective. By lem-weil-pbc-kinjective-hom-derived
these natural chain comparisons descend naturally. Their adjunction-mate equations
below identify precisely those product comparisons. The self comparisons are counits.
8. The overlap transpose is represented at C by restriction
I(C × U/U) → I(C × W/U). Its W-transpose is the U graph counit restricted to W.
Both complexes are K-injective, so lem-weil-pbc-kinjective-hom-derived identifies
this calculation with overlap; the same calculation applies to V.
9. At T → U the first overlap is the k_U unit and the other overlap is the
identity on the common product. Interchange U,V. At T → W both overlap maps
are identities under graph counits. These give the six final equations.
No covering hypothesis is used at any step. -/
theorem subterminal_derived_image_calculus
    {C : Type u} [SmallCategory C] [HasFiniteLimits C]
    (J : GrothendieckTopology C) [J.Subcanonical]
    (R : Sheaf J CommRingCat.{max u r}) (U V : C)
    (hU : IsSubterminal U) (hV : IsSubterminal V)
    [HasDerivedCategory.{w0} (modules.{u, r} R)]
    [HasDerivedCategory.{wU} (sliceModules.{u, r} R U)]
    [HasDerivedCategory.{wV} (sliceModules.{u, r} R V)]
    [HasDerivedCategory.{wW} (sliceModules.{u, r} R (U ⨯ V))] :
    ∃ (pU : DerivedPair (SheafOfModules.overFunctor.{max u r} (ring.{u, r} R) U)
        (direct.{u, r} (ring.{u, r} R) U)
        (SheafOfModules.overPushforwardOverAdj (R := ring.{u, r} R) U))
      (pV : DerivedPair (SheafOfModules.overFunctor.{max u r} (ring.{u, r} R) V)
        (direct.{u, r} (ring.{u, r} R) V)
        (SheafOfModules.overPushforwardOverAdj (R := ring.{u, r} R) V))
      (pW : DerivedPair (SheafOfModules.overFunctor.{max u r} (ring.{u, r} R) (U ⨯ V))
        (direct.{u, r} (ring.{u, r} R) (U ⨯ V))
        (SheafOfModules.overPushforwardOverAdj (R := ring.{u, r} R) (U ⨯ V)))
      (pKU : DerivedPair
        (SheafOfModules.overMap.{max u r} (ring.{u, r} R) (Limits.prod.fst : U ⨯ V ⟶ U))
        (SheafOfModules.overPullback.{max u r} (ring.{u, r} R) (Limits.prod.fst : U ⨯ V ⟶ U))
        (SheafOfModules.overMapPushforwardAdj (ring.{u, r} R) (Limits.prod.fst : U ⨯ V ⟶ U)))
      (pKV : DerivedPair
        (SheafOfModules.overMap.{max u r} (ring.{u, r} R) (Limits.prod.snd : U ⨯ V ⟶ V))
        (SheafOfModules.overPullback.{max u r} (ring.{u, r} R) (Limits.prod.snd : U ⨯ V ⟶ V))
        (SheafOfModules.overMapPushforwardAdj (ring.{u, r} R) (Limits.prod.snd : U ⨯ V ⟶ V)))
      (cU : pW.left ≅ pU.left ⋙ pKU.left)
      (cV : pW.left ≅ pV.left ⋙ pKV.left),
      CompositionNormalization (A := modules.{u, r} R) (B := sliceModules.{u, r} R U)
        (D := sliceModules.{u, r} R (U ⨯ V)) pU.qF pKU.qF pW.qF cU
        (restrictionComp.{u, r} R (Limits.prod.fst : U ⨯ V ⟶ U)) ∧
      CompositionNormalization (A := modules.{u, r} R) (B := sliceModules.{u, r} R V)
        (D := sliceModules.{u, r} R (U ⨯ V)) pV.qF pKV.qF pW.qF cV
        (restrictionComp.{u, r} R (Limits.prod.snd : U ⨯ V ⟶ V)) ∧
      Nonempty (Comparisons pU.adj pV.adj pW.adj pKU.adj pKV.adj cU cV) := by
  let : HasSheafify J AddCommGrpCat.{max u r} :=
    smallSheafify.{max u r, u, u} J
  let : J.WEqualsLocallyBijective AddCommGrpCat.{max u r} :=
    smallLocalCriterion.{max u r, u, u} J
  let : ∀ Z : C, HasSheafify (J.over Z) AddCommGrpCat.{max u r} :=
    fun Z ↦ smallSheafify.{max u r, u, u} (J.over Z)
  let : ∀ Z : C, (J.over Z).WEqualsLocallyBijective AddCommGrpCat.{max u r} :=
    fun Z ↦ smallLocalCriterion.{max u r, u, u} (J.over Z)
  let pU := restrictionPair R U
  let pV := restrictionPair R V
  let pW := restrictionPair R (U ⨯ V)
  let pKU := relocalizationPair R (prod.fst : U ⨯ V ⟶ U)
  let pKV := relocalizationPair R (prod.snd : U ⨯ V ⟶ V)
  have hUlim := (SheafOfModules.overFunctor_exact_ofUniverses.{u, u, max u r}
    (ring.{u, r} R) U).1
  have hUcol := (SheafOfModules.overFunctor_exact_ofUniverses.{u, u, max u r}
    (ring.{u, r} R) U).2
  have hVlim := (SheafOfModules.overFunctor_exact_ofUniverses.{u, u, max u r}
    (ring.{u, r} R) V).1
  have hVcol := (SheafOfModules.overFunctor_exact_ofUniverses.{u, u, max u r}
    (ring.{u, r} R) V).2
  have hWlim := (SheafOfModules.overFunctor_exact_ofUniverses.{u, u, max u r}
    (ring.{u, r} R) (U ⨯ V)).1
  have hWcol := (SheafOfModules.overFunctor_exact_ofUniverses.{u, u, max u r}
    (ring.{u, r} R) (U ⨯ V)).2
  have hKUlim := (SheafOfModules.overMap_exact_ofUniverses.{u, u, max u r}
    (ring.{u, r} R) (prod.fst : U ⨯ V ⟶ U)).1
  have hKUcol := (SheafOfModules.overMap_exact_ofUniverses.{u, u, max u r}
    (ring.{u, r} R) (prod.fst : U ⨯ V ⟶ U)).2
  have hKVlim := (SheafOfModules.overMap_exact_ofUniverses.{u, u, max u r}
    (ring.{u, r} R) (prod.snd : U ⨯ V ⟶ V)).1
  have hKVcol := (SheafOfModules.overMap_exact_ofUniverses.{u, u, max u r}
    (ring.{u, r} R) (prod.snd : U ⨯ V ⟶ V)).2
  let cU : pW.left ≅ pU.left ⋙ pKU.left := exactComposition _ _ _
    (SheafOfModules.overFunctorMap (ring.{u, r} R) (prod.fst : U ⨯ V ⟶ U)).symm
  let cV : pW.left ≅ pV.left ⋙ pKV.left := exactComposition _ _ _
    (SheafOfModules.overFunctorMap (ring.{u, r} R) (prod.snd : U ⨯ V ⟶ V)).symm
  have hcU : CompositionNormalization pU.qF pKU.qF pW.qF cU
      (restrictionComp.{u, r} R (prod.fst : U ⨯ V ⟶ U)) := by
    intro M
    exact exactComposition_normalization _ _ _ _ M
  have hcV : CompositionNormalization pV.qF pKV.qF pW.qF cV
      (restrictionComp.{u, r} R (prod.snd : U ⨯ V ⟶ V)) := by
    intro M
    exact exactComposition_normalization _ _ _ _ M
  have hW : IsSubterminal (U ⨯ V) := by
    intro X f g
    apply prod.hom_ext
    · exact hU _ _
    · exact hV _ _
  have := ordinary_counit_iso (ring.{u, r} R) U hU
  have := ordinary_counit_iso (ring.{u, r} R) V hV
  have := ordinary_counit_iso (ring.{u, r} R) (U ⨯ V) hW
  have := pair_counit_iso pU
  have := pair_counit_iso pV
  have := pair_counit_iso pW
  have := restrictionMate_iso pW.adj pKU.adj cU pU.adj
  have := restrictionMate_iso pW.adj pKV.adj cV pV.adj
  have huv (B : DerivedCategory (sliceModules.{u, r} R V)) :
      IsIso (pU.left.map (overlap pV.adj pW.adj cV B)) := by
    exact overlap_iso_after pV pW _ pKV.left pKV.qF cV _ hcV
      _ pU.left pU.qF (pair_counit pV) pKV.restrict_injective
      (ordinary_overlap_iso R U V (U ⨯ V) hU hV _ _
        (IsPullback.of_hasBinaryProduct' U V)) B
  have hvu (A : DerivedCategory (sliceModules.{u, r} R U)) :
      IsIso (pV.left.map (overlap pU.adj pW.adj cU A)) := by
    exact overlap_iso_after pU pW _ pKU.left pKU.qF cU _ hcU
      _ pV.left pV.qF (pair_counit pU) pKU.restrict_injective
      (ordinary_overlap_iso R V U (U ⨯ V) hV hU _ _
        (IsPullback.of_hasBinaryProduct' U V).flip) A
  have : IsIso (crossMate pV.adj pW.adj pKU.adj cU cV) := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro B
    change IsIso (pU.left.map (overlap pV.adj pW.adj cV B) ≫ _)
    have := huv B
    infer_instance
  have : IsIso (crossMate pU.adj pW.adj pKV.adj cV cU) := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro A
    change IsIso (pV.left.map (overlap pU.adj pW.adj cU A) ≫ _)
    have := hvu A
    infer_instance
  exact ⟨pU, pV, pW, pKU, pKV, cU, cV, hcU, hcV,
    ⟨buildComparisons pU.adj pV.adj pW.adj pKU.adj pKV.adj cU cV⟩⟩

end CategoryTheory.SubterminalImageCalculus
