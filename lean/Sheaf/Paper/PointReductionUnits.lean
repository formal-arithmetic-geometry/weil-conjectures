/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q50
-/
module

public import Sheaf.Paper.PointSectionsDerivedReduction
public import Sheaf.Paper.PointSectionsFiniteReduction
public import Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Category.ModuleCat.AB
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
public import Sheaf.Paper.AdicCoefficientDatum

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Sheaf.Algebra.Homology.KFlat
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Sheaf.Paper.PointProEtaleSectionsExact
public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
public import Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients

public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
import WeilConjectures.Algebra.Homology.ExtensionKFlatQuasiIso
/-! # Canonical coefficient-reduction units at a geometric point

Source: Stacks Project, sites-cohomology.tex Tag 07A6 and derived.tex Tags 0FND and 09T5
(blueprint: def-trf-point-reduction-units).

## Main definitions

* `pointUnitIntegralModuleUnit`, `pointUnitIntegralSheafUnit`: the integral quotient units.
* `pointUnitFiniteModuleUnit`, `pointUnitFiniteSheafUnit`: the finite quotient units.
* `pointUnitIntegralDerivedSectionsRestrictionIso` and
  `pointUnitFiniteDerivedSectionsRestrictionIso`: the exact restriction/sections identity.

The named existence theorems fix each unit on actual tensor representatives, so their
choices determine the units uniquely. The section comparisons are the identity on elements.
The integral index n denotes exponent n+1; finite indices denote exponents.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w r
set_option linter.style.haveILetI false

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
open scoped TensorProduct ChangeOfRings

namespace WeilConjectures

private theorem pointUnitCochainNormalization
    {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B]
    (L : A ⥤ B) (R : B ⥤ A) [L.Additive] [R.Additive]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    (a₀ : L ⊣ R) (LD : DerivedCategory A ⥤ DerivedCategory B)
    (ε : DerivedCategory.Qh ⋙ LD ⟶ L.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (a : LD ⊣ R.mapDerivedCategory) (P : CochainComplex A ℤ)
    (h : a.unit.app (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj P)) ≫
      R.mapDerivedCategory.map (ε.app ((HomotopyCategory.quotient _ _).obj P)) ≫
      R.mapDerivedCategoryFactorsh.hom.app
        ((L.mapHomotopyCategory (.up ℤ)).obj ((HomotopyCategory.quotient _ _).obj P)) =
      DerivedCategory.Qh.map ((a₀.mapHomotopyCategory (.up ℤ)).unit.app
        ((HomotopyCategory.quotient _ _).obj P))) :
    a.unit.app (DerivedCategory.Q.obj P) ≫ R.mapDerivedCategory.map
      (LD.map ((DerivedCategory.quotientCompQhIso A).inv.app P) ≫
        ε.app ((HomotopyCategory.quotient _ _).obj P) ≫
        DerivedCategory.Qh.map ((L.mapHomotopyCategoryFactors (.up ℤ)).hom.app P) ≫
        (DerivedCategory.quotientCompQhIso B).hom.app
          ((L.mapHomologicalComplex (.up ℤ)).obj P)) ≫
      R.mapDerivedCategoryFactors.hom.app ((L.mapHomologicalComplex (.up ℤ)).obj P) =
      DerivedCategory.Q.map ((a₀.mapHomologicalComplex (.up ℤ)).unit.app P) := by
  let K := (L.mapHomologicalComplex (.up ℤ)).obj P
  let q₀ := (DerivedCategory.quotientCompQhIso A).app P
  let q₁ := (DerivedCategory.quotientCompQhIso B).app K
  let q₂ := (DerivedCategory.quotientCompQhIso A).app
    ((R.mapHomologicalComplex (.up ℤ)).obj K)
  have hf := R.mapDerivedCategoryFactorsh_hom_app K
  have hq : DerivedCategory.Qh.map
      ((R.mapHomotopyCategoryFactors (.up ℤ)).inv.app K) = 𝟙 _ := by
    change DerivedCategory.Qh.map (𝟙 _) = 𝟙 _
    exact DerivedCategory.Qh.map_id _
  rw [hq] at hf
  erw [Category.comp_id] at hf
  have hf' : R.mapDerivedCategory.map q₁.hom ≫ R.mapDerivedCategoryFactors.hom.app K =
      R.mapDerivedCategoryFactorsh.hom.app
        ((L.mapHomotopyCategory (.up ℤ)).obj ((HomotopyCategory.quotient _ _).obj P)) ≫
          q₂.hom := by
    have hh := congrArg (fun z ↦ z ≫ q₂.hom) hf
    change R.mapDerivedCategoryFactorsh.hom.app
      ((L.mapHomotopyCategory (.up ℤ)).obj ((HomotopyCategory.quotient _ _).obj P)) ≫
        q₂.hom =
      (R.mapDerivedCategory.map q₁.hom ≫ R.mapDerivedCategoryFactors.hom.app K ≫
        q₂.inv) ≫ q₂.hom at hh
    simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using hh.symm
  have hL : DerivedCategory.Qh.map ((L.mapHomotopyCategoryFactors (.up ℤ)).hom.app P) =
      𝟙 _ := by
    change DerivedCategory.Qh.map (𝟙 _) = 𝟙 _
    exact DerivedCategory.Qh.map_id _
  have hε : LD.map q₀.inv ≫ ε.app ((HomotopyCategory.quotient _ _).obj P) ≫
      DerivedCategory.Qh.map ((L.mapHomotopyCategoryFactors (.up ℤ)).hom.app P) ≫ q₁.hom =
      LD.map q₀.inv ≫ ε.app ((HomotopyCategory.quotient _ _).obj P) ≫ q₁.hom := by
    rw [hL]
    erw [Category.id_comp]
  change a.unit.app (DerivedCategory.Q.obj P) ≫ R.mapDerivedCategory.map
    (LD.map q₀.inv ≫ ε.app ((HomotopyCategory.quotient _ _).obj P) ≫
      DerivedCategory.Qh.map ((L.mapHomotopyCategoryFactors (.up ℤ)).hom.app P) ≫ q₁.hom) ≫
        R.mapDerivedCategoryFactors.hom.app K = _
  rw [hε]
  change a.unit.app (DerivedCategory.Q.obj P) ≫ R.mapDerivedCategory.map
    (LD.map q₀.inv ≫ ε.app ((HomotopyCategory.quotient _ _).obj P) ≫ q₁.hom) ≫
      R.mapDerivedCategoryFactors.hom.app K = _
  apply (cancel_epi q₀.hom).1
  have hn := a.unit.naturality q₀.hom
  dsimp only [Functor.id_map, Functor.comp_map] at hn
  simp only [Functor.map_comp, Category.assoc]
  rw [← Category.assoc, hn]
  rw [Category.assoc, ← R.mapDerivedCategory.map_comp_assoc, ← LD.map_comp,
    Iso.hom_inv_id, LD.map_id, R.mapDerivedCategory.map_id, Category.id_comp]
  erw [hf', reassoc_of% h]
  rw [Adjunction.mapHomotopyCategory_unit_app_quotient]
  exact DerivedCategory.quotientCompQhIso_hom_naturality
    ((a₀.mapHomologicalComplex (.up ℤ)).unit.app P)

private def pointUnitMixedIso {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) [(ModuleCat.extendScalars.{u, u, u} f).Additive] :
    (((ModuleCat.mixedTensor f).flip.map₂CochainComplex).flip.obj
      ((HomologicalComplex.single _ (.up ℤ) 0).obj (ModuleCat.of S S))) ≅
        (ModuleCat.extendScalars.{u, u, u} f).mapHomologicalComplex (.up ℤ) :=
  CochainComplex.map₂HomologicalComplexFlipObjSingleIso
      (ModuleCat.mixedTensor f).flip (ModuleCat.of S S) ≪≫
    NatIso.mapHomologicalComplex
      (Functor.isoWhiskerLeft (ModuleCat.extendScalars.{u, u, u} f)
        (MonoidalCategory.leftUnitorNatIso (ModuleCat.{u} S)) ≪≫
          Functor.rightUnitor _) (.up ℤ)

private theorem pointUnitMixedIso_inv {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) [(ModuleCat.extendScalars.{u, u, u} f).Additive]
    (C : CochainComplex (ModuleCat.{u} R) ℤ) (a : ℤ) (x : C.X a) :
    ((pointUnitMixedIso f).inv.app C).f a ((1 : S) ⊗ₜ[_, f] x) =
      (HomologicalComplex.ιMapBifunctorOrZero C
        ((HomologicalComplex.single _ (.up ℤ) 0).obj (ModuleCat.of S S))
        (ModuleCat.mixedTensor f).flip (.up ℤ) a 0 a)
        ((1 : S) ⊗ₜ ((1 : S) ⊗ₜ[_, f] x)) := by
  simp only [pointUnitMixedIso, Iso.trans_inv, NatTrans.comp_app,
    HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply,
    CochainComplex.map₂HomologicalComplexFlipObjSingleIso_inv_app,
    CochainComplex.mapBifunctorSingle₂Iso_inv]
  change (HomologicalComplex.mapBifunctorFlipIso C
    ((HomologicalComplex.single _ (.up ℤ) 0).obj (ModuleCat.of S S))
    (ModuleCat.mixedTensor f).flip (.up ℤ)).hom.f a
      ((CochainComplex.mapBifunctorSingle₁Iso (ModuleCat.mixedTensor f)
        (ModuleCat.of S S) C).inv.f a
          ((1 : S) ⊗ₜ[S] ((1 : S) ⊗ₜ[_, f] x))) = _
  rw [CochainComplex.mapBifunctorSingle₁Iso_inv_f]
  have hsingle : (HomologicalComplex.singleObjXSelf (.up ℤ) 0
      (ModuleCat.of S S)).inv = 𝟙 (ModuleCat.of S S) := rfl
  erw [hsingle, CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp]
  rw [HomologicalComplex.ιMapBifunctorOrZero_eq _ _ _ _ a 0 a (by simp)]
  have hf := HomologicalComplex.ι_mapBifunctorFlipIso_hom C
    ((HomologicalComplex.single _ (.up ℤ) 0).obj (ModuleCat.of S S))
    (ModuleCat.mixedTensor f).flip (.up ℤ) a 0 a (by simp)
  have hs : ComplexShape.σ (.up ℤ) (.up ℤ) (.up ℤ) a 0 = 1 := by
    change (a * 0).negOnePow = 1
    simp
  rw [hs, one_smul] at hf
  exact congrArg (fun g ↦ g ((1 : S) ⊗ₜ[S] ((1 : S) ⊗ₜ[_, f] x))) hf

private theorem pointUnitModuleNormalization
    {R S : Type u} [CommRing R] [CommRing S]
    [HasDerivedCategory (ModuleCat.{u} R)] [HasDerivedCategory (ModuleCat.{u} S)]
    (f : R →+* S) [(ModuleCat.extendScalars.{u, u, u} f).Additive]
    (F : CochainComplex (ModuleCat.{u} R) ℤ ⥤ CochainComplex (ModuleCat.{u} S) ℤ)
    (e : F ≅ (ModuleCat.extendScalars.{u, u, u} f).mapHomologicalComplex (.up ℤ))
    (T : DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} S))
    (ε : DerivedCategory.Q ⋙ T ⟶ F ⋙ DerivedCategory.Q)
    (hT : T.IsLeftDerivedFunctor ε (HomologicalComplex.quasiIso _ (.up ℤ)))
    (hc : ∀ C, (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat C → IsIso (ε.app C)) :
    ∃ b : T ⊣ (ModuleCat.restrictScalars.{u, u, u} f).mapDerivedCategory,
      ∀ C : CochainComplex (ModuleCat.{u} R) ℤ,
        b.unit.app (DerivedCategory.Q.obj C) ≫
            (ModuleCat.restrictScalars.{u, u, u} f).mapDerivedCategory.map (ε.app C) ≫
            (ModuleCat.restrictScalars.{u, u, u} f).mapDerivedCategoryFactors.hom.app (F.obj C) =
          DerivedCategory.Q.map
            (((ModuleCat.extendRestrictScalarsAdj.{u, u, u} f).mapHomologicalComplex
                (.up ℤ)).unit.app C ≫
              ((ModuleCat.restrictScalars.{u, u, u} f).mapHomologicalComplex (.up ℤ)).map
                (e.inv.app C)) := by
  classical
  let E := ModuleCat.extendScalars.{u, u, u} f
  let U := ModuleCat.restrictScalars.{u, u, u} f
  letI : E.Additive := (ModuleCat.extendRestrictScalarsAdj.{u, u, u} f).left_adjoint_additive
  letI : HasExactColimitsOfShape ℤ (ModuleCat.{u} R) :=
    HasExactColimitsOfShape.of_domain_equivalence (ModuleCat.{u} R)
      (AsSmall.equiv (C := ℤ)).symm
  letI : E.PreservesKFlatQuasiIso := ModuleCat.extendScalars_preservesKFlatQuasiIso f
  let adj := ModuleCat.extendRestrictScalarsAdj.{u, u, u} f
  let b₀ : E.leftDerivedFunctor ⊣ U.mapDerivedCategory :=
    adj.derivedAdjunction.ofNatIsoRight U.rightDerivedFunctorIsoMapDerivedCategory
  let ε₀ : DerivedCategory.Q ⋙ E.leftDerivedFunctor ⟶
      E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
    Functor.whiskerRight (DerivedCategory.quotientCompQhIso (ModuleCat.{u} R)).inv
        E.leftDerivedFunctor ≫
      Functor.whiskerLeft (HomotopyCategory.quotient _ _) E.leftDerivedFunctorCounit ≫
      Functor.whiskerRight (E.mapHomotopyCategoryFactors (.up ℤ)).hom DerivedCategory.Qh ≫
      Functor.whiskerLeft (E.mapHomologicalComplex (.up ℤ))
        (DerivedCategory.quotientCompQhIso (ModuleCat.{u} S)).hom
  let β := ε₀ ≫ (Functor.isoWhiskerRight e DerivedCategory.Q).inv
  letI := hT
  let i := T.leftDerivedLift ε (HomologicalComplex.quasiIso _ (.up ℤ))
    E.leftDerivedFunctor β
  have hi (C : CochainComplex (ModuleCat.{u} R) ℤ) :
      i.app (DerivedCategory.Q.obj C) ≫ ε.app C = β.app C :=
    T.leftDerived_fac_app ε (HomologicalComplex.quasiIso _ (.up ℤ))
      E.leftDerivedFunctor β C
  have hε₀ (C : CochainComplex (ModuleCat.{u} R) ℤ)
      (hC : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat C) : IsIso (ε₀.app C) := by
    have := E.isIso_leftDerivedFunctorCounit_app_of_kFlat C hC
    dsimp only [ε₀, NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
    infer_instance
  haveI : IsIso i := by
    apply (NatTrans.isIso_iff_isIso_app i).2
    intro X
    let QR := DerivedCategory.Q (C := ModuleCat.{u} R)
    let W := HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ)
    letI : QR.EssSurj := Localization.essSurj QR W
    let C := QR.objPreimage X
    let Λ := (Classical.choice (inferInstance :
      Abelian.HasFunctorialFlatResolution (ModuleCat.{u} R))).reduced
    let P := Λ.resolutionFunctor.obj C
    let t := Λ.resolutionNatTrans.app C
    have ht : QuasiIso t := inferInstance
    have hP : W.kFlat P :=
      Λ.kFlat_resolutionFunctor_obj ObjectProperty.flat.essImage_ι_le C
    haveI : IsIso (QR.map t) := (DerivedCategory.isIso_Q_map_iff_quasiIso _ t).2 ht
    let q : QR.obj P ≅ X := asIso (QR.map t) ≪≫ QR.objObjPreimageIso X
    rw [← NatTrans.isIso_app_iff_of_iso i q]
    haveI := hc P hP
    haveI := hε₀ P hP
    haveI : IsIso (β.app P) := by
      dsimp only [β, NatTrans.comp_app]
      infer_instance
    haveI : IsIso (i.app (QR.obj P) ≫ ε.app P) := by rw [hi]; infer_instance
    exact IsIso.of_isIso_comp_right _ (ε.app P)
  let b : T ⊣ U.mapDerivedCategory := b₀.ofNatIsoLeft (asIso i)
  refine ⟨b, ?_⟩
  intro C
  have hstd : b₀.unit.app (DerivedCategory.Q.obj C) ≫ U.mapDerivedCategory.map (ε₀.app C) ≫
      U.mapDerivedCategoryFactors.hom.app ((E.mapHomologicalComplex (.up ℤ)).obj C) =
        DerivedCategory.Q.map ((adj.mapHomologicalComplex (.up ℤ)).unit.app C) := by
    apply pointUnitCochainNormalization E U adj E.leftDerivedFunctor
      E.leftDerivedFunctorCounit b₀ C
    have hfac := (adj.mapHomotopyCategory (.up ℤ)).derivedη_fac_app
      (HomotopyCategory.quasiIso (ModuleCat.{u} R) (.up ℤ))
      E.leftDerivedFunctorCounit U.rightDerivedFunctorUnit
      ((HomotopyCategory.quotient _ _).obj C)
    simp only [b₀, Adjunction.ofNatIsoRight_unit, NatTrans.comp_app,
      Functor.whiskerLeft_app, Category.assoc]
    erw [← U.rightDerivedFunctorIsoMapDerivedCategory.hom.naturality_assoc]
    erw [← Category.assoc, hfac]
    have hβ := NatTrans.congr_app U.rightDerivedFunctorIsoMapDerivedCategory_hom_fac
      ((E.mapHomotopyCategory (.up ℤ)).obj ((HomotopyCategory.quotient _ _).obj C))
    dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app] at hβ
    rw [Category.assoc]
    erw [reassoc_of% hβ]
    simp only [Iso.inv_hom_id_app]
    erw [Category.comp_id]
  simp only [b, Adjunction.ofNatIsoLeft_unit, NatTrans.comp_app,
    Functor.whiskerRight_app, asIso_hom, Category.assoc]
  rw [← U.mapDerivedCategory.map_comp_assoc, hi]
  change b₀.unit.app _ ≫ U.mapDerivedCategory.map
    (ε₀.app C ≫ DerivedCategory.Q.map (e.inv.app C)) ≫ _ = _
  rw [Functor.map_comp, Category.assoc, U.mapDerivedCategoryFactors_hom_naturality]
  rw [reassoc_of% hstd, ← Functor.map_comp]

private theorem pointUnitMixedModuleNormalization
    {R S : Type u} [CommRing R] [CommRing S]
    [HasDerivedCategory (ModuleCat.{u} R)] [HasDerivedCategory (ModuleCat.{u} S)]
    (f : R →+* S) [(ModuleCat.extendScalars.{u, u, u} f).Additive]
    (T : DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} S))
    (ε : DerivedCategory.Q ⋙ T ⟶
      (((ModuleCat.mixedTensor f).flip.map₂CochainComplex).flip.obj
        ((HomologicalComplex.single _ (.up ℤ) 0).obj (ModuleCat.of S S))) ⋙ DerivedCategory.Q)
    (hT : T.IsLeftDerivedFunctor ε (HomologicalComplex.quasiIso _ (.up ℤ)))
    (hc : ∀ C, (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat C → IsIso (ε.app C)) :
    ∃ b : T ⊣ (ModuleCat.restrictScalars.{u, u, u} f).mapDerivedCategory,
      ∀ C : CochainComplex (ModuleCat.{u} R) ℤ,
        (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat C →
        ∃ g : C ⟶ ((ModuleCat.restrictScalars.{u, u, u} f).mapHomologicalComplex
            (.up ℤ)).obj ((((ModuleCat.mixedTensor f).flip.map₂CochainComplex).flip.obj
              ((HomologicalComplex.single _ (.up ℤ) 0).obj (ModuleCat.of S S))).obj C),
          (∀ (a : ℤ) (x : C.X a), g.f a x =
            (HomologicalComplex.ιMapBifunctorOrZero C
              ((HomologicalComplex.single _ (.up ℤ) 0).obj (ModuleCat.of S S))
              (ModuleCat.mixedTensor f).flip (.up ℤ) a 0 a)
                ((1 : S) ⊗ₜ ((1 : S) ⊗ₜ[_, f] x))) ∧
          b.unit.app (DerivedCategory.Q.obj C) ≫
              (ModuleCat.restrictScalars.{u, u, u} f).mapDerivedCategory.map (ε.app C) ≫
              (ModuleCat.restrictScalars.{u, u, u} f).mapDerivedCategoryFactors.hom.app
                ((((ModuleCat.mixedTensor f).flip.map₂CochainComplex).flip.obj
                  ((HomologicalComplex.single _ (.up ℤ) 0).obj (ModuleCat.of S S))).obj C) =
            DerivedCategory.Q.map g := by
  let F := (((ModuleCat.mixedTensor f).flip.map₂CochainComplex).flip.obj
    ((HomologicalComplex.single _ (.up ℤ) 0).obj (ModuleCat.of S S)))
  obtain ⟨b, hb⟩ := pointUnitModuleNormalization f F (pointUnitMixedIso f) T ε hT hc
  refine ⟨b, fun C _ ↦ ⟨
    ((ModuleCat.extendRestrictScalarsAdj.{u, u, u} f).mapHomologicalComplex (.up ℤ)).unit.app C ≫
      ((ModuleCat.restrictScalars.{u, u, u} f).mapHomologicalComplex (.up ℤ)).map
        ((pointUnitMixedIso f).inv.app C), ?_, hb C⟩⟩
  intro a x
  change ((pointUnitMixedIso f).inv.app C).f a
    ((ModuleCat.extendRestrictScalarsAdj.{u, u, u} f).unit.app (C.X a) x) = _
  rw [ModuleCat.extendRestrictScalarsAdj_unit_app_apply]
  exact pointUnitMixedIso_inv f C a x

private theorem pointUnitSheafNormalization
    {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
    {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify J AddCommGrpCat.{r}]
    {O O' : Sheaf J CommRingCat.{r}}
    [HasDerivedCategory.{w}
      (SheafOfModules.{r} (SheafOfModules.derivedChangeRingIndependentCoefficients J O))]
    [HasDerivedCategory.{w}
      (SheafOfModules.{r} (SheafOfModules.derivedChangeRingIndependentCoefficients J O'))]
    (φ : O ⟶ O')
    [PreservesFiniteLimits (SheafOfModules.restrictScalars.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).map φ))]
    [PreservesFiniteColimits (SheafOfModules.restrictScalars.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).map φ))]
    (E₀ : SheafOfModules.{r} (SheafOfModules.derivedChangeRingIndependentCoefficients J O) ⥤
      SheafOfModules.{r} (SheafOfModules.derivedChangeRingIndependentCoefficients J O'))
    (ho : ∀ M, E₀.obj M = SheafOfModules.changeOfRings φ M)
    (hm : ∀ {M N} (f : M ⟶ N), E₀.map f = eqToHom (ho M) ≫
      SheafOfModules.changeOfRingsHom φ M f ≫ eqToHom (ho N).symm) [E₀.Additive]
    (LF : DerivedCategory (SheafOfModules.{r}
      (SheafOfModules.derivedChangeRingIndependentCoefficients J O)) ⥤
      DerivedCategory (SheafOfModules.{r}
        (SheafOfModules.derivedChangeRingIndependentCoefficients J O')))
    (ε : DerivedCategory.Qh ⋙ LF ⟶ E₀.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (hLF : LF.IsLeftDerivedFunctor ε
      (HomotopyCategory.quasiIso (SheafOfModules.{r}
        (SheafOfModules.derivedChangeRingIndependentCoefficients J O)) (.up ℤ))) :
    ∃ a₀ : E₀ ⊣ SheafOfModules.restrictScalars
        ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).map φ),
      (∀ (M : SheafOfModules.{r}
          (SheafOfModules.derivedChangeRingIndependentCoefficients J O))
        (U : Cᵒᵖ) (x : M.val.obj U),
        (eqToHom (ho M)).val.app U ((a₀.unit.app M).val.app U x) =
          (toSheafify J (SheafOfModules.changeOfRingsPresheaf φ M).presheaf).app U
            ((1 : O'.obj.obj U) ⊗ₜ[O.obj.obj U, (φ.hom.app U).hom] x)) ∧
      ∃ a : LF ⊣ (SheafOfModules.restrictScalars
          ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).map φ)).mapDerivedCategory,
        ∀ P : CochainComplex (SheafOfModules.{r}
          (SheafOfModules.derivedChangeRingIndependentCoefficients J O)) ℤ,
          CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := O) P →
          (∀ i : ℤ, SheafOfModules.IsFlatOnSite (R := O) (P.X i)) →
          a.unit.app (DerivedCategory.Q.obj P) ≫
            (SheafOfModules.restrictScalars
              ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).map φ)
              ).mapDerivedCategory.map
              (LF.map ((DerivedCategory.quotientCompQhIso _).inv.app P) ≫
                ε.app ((HomotopyCategory.quotient _ _).obj P) ≫
                DerivedCategory.Qh.map ((E₀.mapHomotopyCategoryFactors (.up ℤ)).hom.app P) ≫
                (DerivedCategory.quotientCompQhIso _).hom.app
                  ((E₀.mapHomologicalComplex (.up ℤ)).obj P)) ≫
            (SheafOfModules.restrictScalars
              ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).map φ)
              ).mapDerivedCategoryFactors.hom.app
                ((E₀.mapHomologicalComplex (.up ℤ)).obj P) =
            DerivedCategory.Q.map ((a₀.mapHomologicalComplex (.up ℤ)).unit.app P) := by
  obtain ⟨_, _, h⟩ := SheafOfModules.sheafRingDerivedCoefficientAdjunction φ
  obtain ⟨a₀, ha₀, hd⟩ := h E₀ ho hm
  refine ⟨a₀, ?_, ?_⟩
  · intro M U x
    have hh := ha₀ M (SheafOfModules.changeOfRings φ M) (𝟙 _) U x
    simpa only [Category.comp_id, Adjunction.homEquiv_unit, SheafOfModules.comp_val,
      PresheafOfModules.comp_app, SheafOfModules.restrictScalars_map_val,
      PresheafOfModules.restrictScalars_map_app, ModuleCat.comp_apply,
      ModuleCat.restrictScalars.map_apply, SheafOfModules.id_val,
      PresheafOfModules.id_app, ModuleCat.id_apply] using! hh
  · obtain ⟨a, ha⟩ := hd LF ε hLF
    refine ⟨a, ?_⟩
    intro P hP hfP
    obtain ⟨_, hp, _⟩ := ha P hP hfP
    exact pointUnitCochainNormalization E₀ _ a₀ LF ε a P hp

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Ordinary restriction along the integral quotient, in the existing coefficient lift.
Source: Stacks 07A6 (blueprint: def-trf-point-reduction-units). -/
abbrev pointUnitIntegralRestriction (n : ℕ) :=
  ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} (pointReductionQuotient l E n)

/-- The fixed derived restriction on integral section modules.
Source: Stacks 07A6 (blueprint: def-trf-point-reduction-units). -/
def pointUnitIntegralDerivedRestriction (n : ℕ) :=
  (pointUnitIntegralRestriction l E n).mapDerivedCategory.{u + 2, u + 2}

/-- The quotient coefficient complex used by the existing module tensor functor.
Source: Stacks 06Y6 (blueprint: def-trf-point-reduction-units). -/
abbrev pointUnitIntegralCoefficient (n : ℕ) :=
  (HomologicalComplex.single _ (.up ℤ) 0).obj
    (ModuleCat.of (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1)))
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))))

/-- The mixed total tensor computing the published integral quotient functor.
Source: Stacks 06Y6 (blueprint: def-trf-point-reduction-units). -/
def pointUnitIntegralComplexTensor (n : ℕ) :=
  (((ModuleCat.mixedTensor (pointReductionQuotient l E n)).flip
    ).map₂CochainComplex).flip.obj (pointUnitIntegralCoefficient l E n)

/-- The universal computation map, retaining the published derived tensor choice.
Source: Stacks 06Y6 (blueprint: def-trf-point-reduction-units). -/
def pointUnitIntegralModuleCounit (n : ℕ) :
    DerivedCategory.Q ⋙ pointReductionModuleTensor l E n ⟶
      pointUnitIntegralComplexTensor l E n ⋙ DerivedCategory.Q :=
  (DerivedCategory.exists_derivedTensor_second_factor_functor
    (pointReductionQuotient l E n)).2.choose_spec.choose (pointUnitIntegralCoefficient l E n)

/-- The element 1 tensor (1 tensor x) in the degree-a summand of the actual total tensor.
Source: Stacks 06Y6 (blueprint: def-trf-point-reduction-units). -/
def pointUnitIntegralTensorGenerator (n : ℕ)
    (C : CochainComplex (ModuleCat.{u + 1}
      (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E))) ℤ)
    (a : ℤ) (b c : ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1)))
    (x : C.X a) : ((pointUnitIntegralComplexTensor l E n).obj C).X a :=
  (HomologicalComplex.ιMapBifunctorOrZero C (pointUnitIntegralCoefficient l E n)
    (ModuleCat.mixedTensor (pointReductionQuotient l E n)).flip (.up ℤ) a 0 a)
      (b ⊗ₜ (c ⊗ₜ[_, pointReductionQuotient l E n] x))

section
attribute [local irreducible] pointReductionQuotient
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

/-- The scalar-extension adjunction on section modules has its actual tensor unit.
Source: Stacks 07A6, 0FND, 09T5 (blueprint: def-trf-point-reduction-units).
Proof: the mixed tensor with the regular coefficient module in degree zero is ordinary
extension of scalars. Derive its ordinary tensor/restriction adjunction, whose unit sends
x to 1 tensor x. Identify the left derived functor by its universal computation map and
exact restriction by its localization comparison. On every K-flat complex this gives
the displayed equation, which fixes the unit on all derived objects. -/
theorem pointUnitIntegralModuleAdjunction (n : ℕ) :
    ∃ b : pointReductionModuleTensor l E n ⊣ pointUnitIntegralDerivedRestriction l E n,
      ∀ C : CochainComplex (ModuleCat.{u + 1}
          (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E))) ℤ,
        (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat C →
        ∃ g : C ⟶ ((pointUnitIntegralRestriction l E n).mapHomologicalComplex (.up ℤ)).obj
            ((pointUnitIntegralComplexTensor l E n).obj C),
          (∀ (a : ℤ) (x : C.X a), g.f a x = pointUnitIntegralTensorGenerator l E n C a 1 1 x) ∧
          b.unit.app (DerivedCategory.Q.obj C) ≫
              (pointUnitIntegralDerivedRestriction l E n).map
                ((pointUnitIntegralModuleCounit l E n).app C) ≫
              (pointUnitIntegralRestriction l E n).mapDerivedCategoryFactors.hom.app
                ((pointUnitIntegralComplexTensor l E n).obj C) = DerivedCategory.Q.map g := by
  let f := pointReductionQuotient l E n
  letI : (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} f).Additive :=
    (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1} f).left_adjoint_additive
  let N := pointUnitIntegralCoefficient l E n
  dsimp only [pointUnitIntegralDerivedRestriction, pointUnitIntegralRestriction,
    pointUnitIntegralComplexTensor, pointUnitIntegralCoefficient,
    pointUnitIntegralTensorGenerator, pointReductionModuleTensor,
    pointUnitIntegralModuleCounit]
  convert! pointUnitMixedModuleNormalization f
    ((DerivedCategory.exists_derivedTensor_second_factor_functor f).2.choose.obj N)
    ((DerivedCategory.exists_derivedTensor_second_factor_functor f).2.choose_spec.choose N)
    ((DerivedCategory.exists_derivedTensor_second_factor_functor f
      ).2.choose_spec.choose_spec.1 N)
    (fun C hC ↦ (DerivedCategory.exists_derivedTensor_second_factor_functor f
      ).2.choose_spec.choose_spec.2.2.1 N C hC) using 3

end

/-- Sections and actual integral coefficient restriction agree by the identity on elements.
Source: Stacks 07A6 (blueprint: def-trf-point-reduction-units).
Proof: restriction changes only the scalar action. The constant-to-completion map followed
by the limit projection is the constant quotient map. Thus both actions agree; the identity
on each section module gives a natural linear isomorphism, uniquely fixed on elements. -/
theorem pointUnitIntegralSectionsRestriction (n : ℕ) :
    ∃! e : scalarReductionRestriction l E (Spec (.of D.k)) n ⋙ pointIntegralSections l E D.k ≅
        pointFiniteSections D.k (Padic.coefficientExtensionRing l E (n + 1)) ⋙
          pointUnitIntegralRestriction l E n,
      ∀ (M : scalarReductionTarget l E (Spec (.of D.k)) n)
        (x : (pointFiniteSections D.k (Padic.coefficientExtensionRing l E (n + 1))).obj M),
        e.hom.app M x = x := by
  classical
  let J := ProEt.topology (Spec (.of D.k))
  let U := op (Scheme.ProEt.mk (𝟙 (Spec (.of D.k))))
  have hn (r : ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E)) :
      ((completedIntegralCommRingProjectionUnrestricted l E (Spec (.of D.k)) n
        ).hom.app U).hom (pointIntegralSectionMap l E D.k r) =
        pointConstantSectionMap D.k (Padic.coefficientExtensionRing l E (n + 1))
          (pointReductionQuotient l E n r) := by
    have hh := limit.lift_π (integralConstantCoefficientCone l E (Spec (.of D.k))) (op n)
    have hh' := congrArg (fun f ↦ (f.hom.app U).hom
      (pointConstantSectionMap D.k (Padic.coefficientExtensionIntegers l E) r)) hh
    change ((completedIntegralCommRingProjectionUnrestricted l E (Spec (.of D.k)) n
        ).hom.app U).hom (pointIntegralSectionMap l E D.k r) = _ at hh'
    rw [hh']
    have ht := NatTrans.congr_app (toSheafify_naturality J
      ((Functor.const (Scheme.ProEt (Spec (.of D.k)))ᵒᵖ).map
        (CommRingCat.ofHom (pointReductionQuotient l E n)))) U
    exact (congrArg (fun f ↦ f r) ht).symm
  let e : scalarReductionRestriction l E (Spec (.of D.k)) n ⋙ pointIntegralSections l E D.k ≅
      pointFiniteSections D.k (Padic.coefficientExtensionRing l E (n + 1)) ⋙
        pointUnitIntegralRestriction l E n :=
    NatIso.ofComponents (fun M ↦ LinearEquiv.toModuleIso
      (m₁ := ((pointIntegralSections l E D.k).obj
        ((scalarReductionRestriction l E (Spec (.of D.k)) n).obj M)).isModule)
      (m₂ := ((pointUnitIntegralRestriction l E n).obj
        ((pointFiniteSections D.k (Padic.coefficientExtensionRing l E (n + 1))).obj M)
          ).isModule)
      { toFun := fun x ↦ x
        invFun := fun x ↦ x
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun r x ↦ by
          change @SMul.smul _ (M.val.obj U) _
            (((completedIntegralCommRingProjectionUnrestricted l E (Spec (.of D.k)) n
              ).hom.app U).hom (pointIntegralSectionMap l E D.k r)) x =
            @SMul.smul _ (M.val.obj U) _
              (pointConstantSectionMap D.k (Padic.coefficientExtensionRing l E (n + 1))
                (pointReductionQuotient l E n r)) x
          rw [hn] }) (fun _ ↦ by ext x; rfl)
  refine ⟨e, fun _ _ ↦ rfl, ?_⟩
  intro e' he'
  apply Iso.ext
  ext M x
  exact he' M x

/-- Canonical identity-on-sections comparison before deriving.
Source: Stacks 07A6 (blueprint: def-trf-point-reduction-units). -/
def pointUnitIntegralSectionsRestrictionIso (n : ℕ) :=
  (pointUnitIntegralSectionsRestriction D l E n).exists.choose

/-- The exact identity-on-sections comparison transported through localization.
Source: Stacks 07A6, 09T5 (blueprint: def-trf-point-reduction-units). -/
def pointUnitIntegralDerivedSectionsRestrictionIso (n : ℕ) :
    scalarReductionDerivedRestriction l E (Spec (.of D.k)) n ⋙
        (pointIntegralSections l E D.k).mapDerivedCategory ≅
      (pointFiniteSections D.k (Padic.coefficientExtensionRing l E (n + 1))).mapDerivedCategory ⋙
        pointUnitIntegralDerivedRestriction l E n := by
  letI : PreservesFiniteLimits (scalarReductionRestriction l E (Spec (.of D.k)) n) :=
    scalarReductionRestrictionLimits l E (Spec (.of D.k)) n
  letI : PreservesFiniteColimits (scalarReductionRestriction l E (Spec (.of D.k)) n) :=
    scalarReductionRestrictionColimits l E (Spec (.of D.k)) n
  letI : PreservesFiniteLimits (pointIntegralSections l E D.k) :=
    pointReductionIntegralLimits D l E
  letI : PreservesFiniteColimits (pointIntegralSections l E D.k) :=
    pointReductionIntegralColimits D l E
  letI : PreservesFiniteLimits
      (pointFiniteSections D.k (Padic.coefficientExtensionRing l E (n + 1))) :=
    pointFiniteReductionSectionsLimits D.k l E (n + 1)
  letI : PreservesFiniteColimits
      (pointFiniteSections D.k (Padic.coefficientExtensionRing l E (n + 1))) :=
    pointFiniteReductionSectionsColimits D.k l E (n + 1)
  letI : (pointUnitIntegralRestriction l E n).Additive := ⟨by intros; rfl⟩
  letI : (pointFiniteSections D.k
      (Padic.coefficientExtensionRing l E (n + 1))).Additive :=
    pointFiniteSectionsAdditive _ _
  letI : (pointFiniteSections D.k (Padic.coefficientExtensionRing l E (n + 1)) ⋙
      pointUnitIntegralRestriction l E n).Additive := inferInstance
  letI : PreservesFiniteLimits
      (pointFiniteSections D.k (Padic.coefficientExtensionRing l E (n + 1)) ⋙
        pointUnitIntegralRestriction l E n) := comp_preservesFiniteLimits _ _
  letI : PreservesFiniteColimits
      (pointFiniteSections D.k (Padic.coefficientExtensionRing l E (n + 1)) ⋙
        pointUnitIntegralRestriction l E n) := comp_preservesFiniteColimits _ _
  letI : PreservesFiniteLimits
      (scalarReductionRestriction l E (Spec (.of D.k)) n ⋙ pointIntegralSections l E D.k) :=
    comp_preservesFiniteLimits _ _
  letI : PreservesFiniteColimits
      (scalarReductionRestriction l E (Spec (.of D.k)) n ⋙ pointIntegralSections l E D.k) :=
    comp_preservesFiniteColimits _ _
  convert! ((Functor.mapDerivedCategoryCompIso
    (scalarReductionRestriction l E (Spec (.of D.k)) n)
    (pointIntegralSections l E D.k)).symm ≪≫
    Functor.mapDerivedCategoryNatIso (pointUnitIntegralSectionsRestrictionIso D l E n) ≪≫
    Functor.mapDerivedCategoryCompIso
      (pointFiniteSections D.k (Padic.coefficientExtensionRing l E (n + 1)))
      (pointUnitIntegralRestriction l E n)) using 3


/-- The finite coefficient quotient with its named ring-sheaf source and target.
The explicit type keeps restriction and tensor constructions on the same coefficient
categories without unfolding the constant-sheaf construction during instance inference.
Source: Stacks Tag 06YY (blueprint: def-trf-point-reduction-units). -/
def pointUnitFiniteCoefficientMap (n j : ℕ) (h : j ≤ n) :
    pointFiniteReductionRingSheaf D.k l E n ⟶ pointFiniteReductionRingSheaf D.k l E j :=
  pointFiniteReductionSheafMap D.k l E n j h

section
attribute [local irreducible] pointFiniteReductionSheafExistence
  pointFiniteReductionSheafModel
/-- The object equation of the existing finite scalar-extension witness.
Source: Stacks Tag 06YY (blueprint: def-trf-point-reduction-units). -/
theorem pointUnitFiniteExtensionObj (n j : ℕ) (h : j ≤ n)
    (M : pointFiniteReductionSheaves D.k l E n) :
    (pointFiniteReductionSheafExtension D.k l E n j h).obj M =
      SheafOfModules.changeOfRings (pointUnitFiniteCoefficientMap D l E n j h) M := by
  exact (pointFiniteReductionSheafModel D.k l E n j h).objEq M
end

/-- Actual sheaf restriction for a pair of finite quotients.
Source: Stacks 07A6 (blueprint: def-trf-point-reduction-units). -/
abbrev pointUnitFiniteRestriction (n j : ℕ) (h : j ≤ n) :=
  SheafOfModules.restrictScalars.{u + 1}
    ((sheafCompose (ProEt.topology (Spec (.of D.k)))
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
        (pointUnitFiniteCoefficientMap D l E n j h))

/-- Restriction keeps the same kernels.
Source: Stacks 03DA (blueprint: def-trf-point-reduction-units). -/
instance pointUnitFiniteRestrictionLimits (n j : ℕ) (h : j ≤ n) :
    PreservesFiniteLimits (pointUnitFiniteRestriction D l E n j h) :=
  (SheafOfModules.sheafRingDerivedCoefficientAdjunction
    (pointUnitFiniteCoefficientMap D l E n j h)).choose

/-- Restriction keeps the same cokernels.
Source: Stacks 03DA (blueprint: def-trf-point-reduction-units). -/
instance pointUnitFiniteRestrictionColimits (n j : ℕ) (h : j ≤ n) :
    PreservesFiniteColimits (pointUnitFiniteRestriction D l E n j h) :=
  (SheafOfModules.sheafRingDerivedCoefficientAdjunction
    (pointUnitFiniteCoefficientMap D l E n j h)).choose_spec.choose

/-- Derived restriction using the existing standard localization of module sheaves.
Source: Stacks 07A6 (blueprint: def-trf-point-reduction-units). -/
def pointUnitFiniteDerivedRestriction (n j : ℕ) (h : j ≤ n) :=
  (pointUnitFiniteRestriction D l E n j h).mapDerivedCategory.{u + 2, u + 2}

/-- Ordinary restriction of the actual finite quotient ring map.
Source: Stacks 07A6 (blueprint: def-trf-point-reduction-units). -/
abbrev pointUnitFiniteModuleRestriction (n j : ℕ) (h : j ≤ n) :=
  ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} (pointFiniteReductionRingMap l E n j h)

/-- Derived module restriction with the small Grothendieck localization already used
by finite point sections, rather than the larger integral-module localization.
Source: Stacks 07A6 (blueprint: def-trf-point-reduction-units). -/
def pointUnitFiniteDerivedModuleRestriction (n j : ℕ) (h : j ≤ n) :=
  @Functor.mapDerivedCategory
    (pointFiniteReductionModules l E j) inferInstance inferInstance
    (HasDerivedCategory.ofIsGrothendieckAbelian.{u + 1} (pointFiniteReductionModules l E j))
    (pointFiniteReductionModules l E n) inferInstance inferInstance
    (HasDerivedCategory.ofIsGrothendieckAbelian.{u + 1} (pointFiniteReductionModules l E n))
    (pointUnitFiniteModuleRestriction l E n j h) inferInstance inferInstance inferInstance

/-- Localization of finite ordinary-module complexes with the published small Hom universe.
Source: Stacks 05RU (blueprint: def-trf-point-reduction-units). -/
def pointUnitFiniteQ (n : ℕ) :=
  letI := HasDerivedCategory.ofIsGrothendieckAbelian.{u + 1}
    (pointFiniteReductionModules l E n)
  DerivedCategory.Q (C := pointFiniteReductionModules l E n)

/-- The fixed exact-restriction factorization in that same localization.
Source: Stacks 09T5 (blueprint: def-trf-point-reduction-units). -/
def pointUnitFiniteModuleFactors (n j : ℕ) (h : j ≤ n) :=
  @Functor.mapDerivedCategoryFactors
    (pointFiniteReductionModules l E j) inferInstance inferInstance
    (HasDerivedCategory.ofIsGrothendieckAbelian.{u + 1} (pointFiniteReductionModules l E j))
    (pointFiniteReductionModules l E n) inferInstance inferInstance
    (HasDerivedCategory.ofIsGrothendieckAbelian.{u + 1} (pointFiniteReductionModules l E n))
    (pointUnitFiniteModuleRestriction l E n j h) inferInstance inferInstance inferInstance

/-- The ordinary-module quotient adjunction, with its canonical tensor unit.
Source: Stacks 07A6, 09T5 (blueprint: def-trf-point-reduction-units).
Proof: derive ordinary tensor/restriction along the actual quotient map, then identify
its left adjoint using the universal mixed-tensor computation with the regular module
in degree zero. Exact restriction descends termwise. The ordinary unit is 1 tensor x;
its derived representative is the displayed map. The normalization fixes the unit on
every K-flat representative and hence on every derived object. -/
theorem pointUnitFiniteModuleAdjunction (n j : ℕ) (h : j ≤ n) :
    ∃ b : pointFiniteReductionModuleTensor l E n j h ⊣
        pointUnitFiniteDerivedModuleRestriction l E n j h,
      ∀ C : CochainComplex (pointFiniteReductionModules l E n) ℤ,
        (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat C →
        ∃ g : C ⟶ ((pointUnitFiniteModuleRestriction l E n j h
            ).mapHomologicalComplex (.up ℤ)).obj
              ((pointFiniteReductionComplexTensor l E n j h).obj C),
          (∀ (a : ℤ) (x : C.X a),
            g.f a x = pointFiniteReductionTensorGenerator l E n j h C a 1 1 x) ∧
          b.unit.app ((pointUnitFiniteQ l E n).obj C) ≫
              (pointUnitFiniteDerivedModuleRestriction l E n j h).map
                ((pointFiniteReductionModuleCounit l E n j h).app C) ≫
              (pointUnitFiniteModuleFactors l E n j h).hom.app
                ((pointFiniteReductionComplexTensor l E n j h).obj C) =
            (pointUnitFiniteQ l E n).map g := by
  let R := ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)
  let S := ULift.{u + 1, u} (Padic.coefficientExtensionRing l E j)
  let hdR := HasDerivedCategory.ofIsGrothendieckAbelian.{u + 1}
    (pointFiniteReductionModules l E n)
  let hdS := HasDerivedCategory.ofIsGrothendieckAbelian.{u + 1}
    (pointFiniteReductionModules l E j)
  letI := hdS
  letI := hdR
  let f := pointFiniteReductionRingMap l E n j h
  letI ha : (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} f).Additive :=
    (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1} f).left_adjoint_additive
  let N := pointFiniteReductionCoefficientComplex l E j
  let z := @DerivedCategory.exists_derivedTensor_second_factor_functor
    R S inferInstance inferInstance hdR hdS f
  dsimp only [pointUnitFiniteDerivedModuleRestriction, pointUnitFiniteQ,
    pointUnitFiniteModuleFactors, pointUnitFiniteModuleRestriction,
    pointFiniteReductionTensorGenerator, pointFiniteReductionComplexTensor,
    pointFiniteReductionCoefficientComplex, pointFiniteReductionModuleTensor,
    pointFiniteReductionModuleCounit]
  convert! @pointUnitMixedModuleNormalization R S inferInstance inferInstance hdR hdS
    f ha (z.2.choose.obj N) (z.2.choose_spec.choose N)
    (z.2.choose_spec.choose_spec.1 N)
    (fun C hC ↦ z.2.choose_spec.choose_spec.2.2.1 N C hC) using 3

section

attribute [local irreducible] pointFiniteReductionSheafExistence
  pointFiniteReductionSheafModel
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false


/-- Finite sheaf reduction uses the actual normalized tensor/restriction adjunction.
Source: Stacks 07A6, 0FND, 09T5 (blueprint: def-trf-point-reduction-units).
Proof: apply the normalized ring-sheaf coefficient adjunction to the fixed ordinary
extension functor and its universal derived pair. Its ordinary unit is sheafification
of 1 tensor x at every object of the site. On a flat-term K-flat complex its derived
unit is the localization of that ordinary unit followed by the inverse universal
computation map and the inverse exact-restriction factorization. This determines it
independently of representatives, with no flatness assumption on the quotient map. -/
theorem pointUnitFiniteSheafAdjunction (n j : ℕ) (h : j ≤ n) :
    ∃ a₀ : pointFiniteReductionSheafExtension D.k l E n j h ⊣
        pointUnitFiniteRestriction D l E n j h,
      (∀ (M : pointFiniteReductionSheaves D.k l E n)
        (U : (Scheme.ProEt (Spec (.of D.k)))ᵒᵖ) (x : M.val.obj U),
        (eqToHom (pointUnitFiniteExtensionObj D l E n j h M)).val.app U
            ((a₀.unit.app M).val.app U x) =
          (toSheafify (ProEt.topology (Spec (.of D.k)))
            (SheafOfModules.changeOfRingsPresheaf
              (pointUnitFiniteCoefficientMap D l E n j h) M).presheaf).app U
                ((1 : (pointFiniteReductionRingSheaf D.k l E j).obj.obj U)
                  ⊗ₜ[(pointFiniteReductionRingSheaf D.k l E n).obj.obj U,
                    ((pointUnitFiniteCoefficientMap D l E n j h).hom.app U).hom] x)) ∧
      ∃ a : pointFiniteReductionSheafTensor D.k l E n j h ⊣
          pointUnitFiniteDerivedRestriction D l E n j h,
        ∀ P : CochainComplex (pointFiniteReductionSheaves D.k l E n) ℤ,
          CochainComplex.IsKFlatIndependentCoefficients
            (J := ProEt.topology (Spec (.of D.k)))
            (R := pointFiniteReductionRingSheaf D.k l E n) P →
          (∀ i : ℤ, SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
            (R := pointFiniteReductionRingSheaf D.k l E n) (P.X i)) →
          a.unit.app (DerivedCategory.Q.obj P) ≫
              (pointUnitFiniteDerivedRestriction D l E n j h).map
                (pointFiniteReductionSheafCounit D.k l E n j h P) ≫
              (pointUnitFiniteRestriction D l E n j h).mapDerivedCategoryFactors.hom.app
                ((pointFiniteReductionSheafComplexTensor D.k l E n j h).obj P) =
            (DerivedCategory.Q (C := pointFiniteReductionSheaves D.k l E n)).map
              ((a₀.mapHomologicalComplex (.up ℤ)).unit.app P) := by
  classical
  dsimp only [pointUnitFiniteDerivedRestriction, pointUnitFiniteRestriction,
    pointFiniteReductionSheafComplexTensor, pointFiniteReductionSheafCounit,
    pointFiniteReductionSheafExtension, pointFiniteReductionSheafTensor,
    pointUnitFiniteCoefficientMap, pointFiniteReductionSheafEpsilon]
  let z := pointFiniteReductionSheafModel D.k l E n j h
  exact @pointUnitSheafNormalization
    (Scheme.ProEt (Spec (.of D.k))) inferInstance (pointFiniteReductionSiteSmall D.k)
    (ProEt.topology (Spec (.of D.k))) inferInstance
    (pointFiniteReductionLocalBijections D.k) (pointFiniteReductionGroupSheafify D.k)
    (pointFiniteReductionRingSheaf D.k l E n) (pointFiniteReductionRingSheaf D.k l E j)
    (HasDerivedCategory.standard (pointFiniteReductionSheaves D.k l E n))
    (HasDerivedCategory.standard (pointFiniteReductionSheaves D.k l E j))
    (pointFiniteReductionSheafMap D.k l E n j h)
    (pointUnitFiniteRestrictionLimits D l E n j h)
    (pointUnitFiniteRestrictionColimits D l E n j h)
    z.F z.objEq z.mapEq z.additive z.T z.ε z.universal

end

/-- The unique identity-on-sections comparison for a finite quotient.
Source: Stacks 07A6 (blueprint: def-trf-point-reduction-units).
Proof: the quotient map of constant sheaves commutes with their constant section maps.
Thus sections with restricted scalar action are the identical ordinary modules on
both sides. The identity is linear and natural, and its value on each element makes
the natural isomorphism unique. -/
theorem pointUnitFiniteSectionsRestriction (n j : ℕ) (h : j ≤ n) :
    ∃! e : pointUnitFiniteRestriction D l E n j h ⋙
        pointFiniteSections D.k (Padic.coefficientExtensionRing l E n) ≅
        pointFiniteSections D.k (Padic.coefficientExtensionRing l E j) ⋙
          pointUnitFiniteModuleRestriction l E n j h,
      ∀ (M : pointFiniteReductionSheaves D.k l E j)
        (x : (pointFiniteSections D.k (Padic.coefficientExtensionRing l E j)).obj M),
        e.hom.app M x = x := by
  classical
  let J := ProEt.topology (Spec (.of D.k))
  let U := op (Scheme.ProEt.mk (𝟙 (Spec (.of D.k))))
  have hn (r : ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)) :
      ((pointUnitFiniteCoefficientMap D l E n j h).hom.app U).hom
          (pointConstantSectionMap D.k (Padic.coefficientExtensionRing l E n) r) =
        pointConstantSectionMap D.k (Padic.coefficientExtensionRing l E j)
          (pointFiniteReductionRingMap l E n j h r) := by
    have hh := NatTrans.congr_app (toSheafify_naturality J
      ((Functor.const (Scheme.ProEt (Spec (.of D.k)))ᵒᵖ).map
        (CommRingCat.ofHom (pointFiniteReductionRingMap l E n j h)))) U
    exact (congrArg (fun f ↦ f r) hh).symm
  let e : pointUnitFiniteRestriction D l E n j h ⋙
      pointFiniteSections D.k (Padic.coefficientExtensionRing l E n) ≅
      pointFiniteSections D.k (Padic.coefficientExtensionRing l E j) ⋙
        pointUnitFiniteModuleRestriction l E n j h :=
    NatIso.ofComponents (fun M ↦ LinearEquiv.toModuleIso
      (m₁ := ((pointFiniteSections D.k (Padic.coefficientExtensionRing l E n)).obj
        ((pointUnitFiniteRestriction D l E n j h).obj M)).isModule)
      (m₂ := ( (pointUnitFiniteModuleRestriction l E n j h).obj
        ((pointFiniteSections D.k (Padic.coefficientExtensionRing l E j)).obj M)).isModule)
      { toFun := fun x ↦ x
        invFun := fun x ↦ x
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun r x ↦ by
          change @SMul.smul _ (M.val.obj U) _
            (((pointUnitFiniteCoefficientMap D l E n j h).hom.app U).hom
              (pointConstantSectionMap D.k (Padic.coefficientExtensionRing l E n) r)) x =
            @SMul.smul _ (M.val.obj U) _
              (pointConstantSectionMap D.k (Padic.coefficientExtensionRing l E j)
                (pointFiniteReductionRingMap l E n j h r)) x
          rw [hn] }) (fun _ ↦ by ext x; rfl)
  refine ⟨e, fun _ _ ↦ rfl, ?_⟩
  intro e' he'
  apply Iso.ext
  ext M x
  exact he' M x

/-- The unique ordinary finite restriction/sections identification.
Source: Stacks 07A6 (blueprint: def-trf-point-reduction-units). -/
def pointUnitFiniteSectionsRestrictionIso (n j : ℕ) (h : j ≤ n) :=
  (pointUnitFiniteSectionsRestriction D l E n j h).exists.choose

/-- The same identity-on-sections comparison, descended through the fixed localizations.
Source: Stacks 07A6, 09T5 (blueprint: def-trf-point-reduction-units). -/
def pointUnitFiniteDerivedSectionsRestrictionIso (n j : ℕ) (h : j ≤ n) :
    pointUnitFiniteDerivedRestriction D l E n j h ⋙
        pointFiniteReductionSections D.k l E n ≅
      pointFiniteReductionSections D.k l E j ⋙
        pointUnitFiniteDerivedModuleRestriction l E n j h := by
  letI : PreservesFiniteLimits (pointUnitFiniteRestriction D l E n j h) :=
    pointUnitFiniteRestrictionLimits D l E n j h
  letI : PreservesFiniteColimits (pointUnitFiniteRestriction D l E n j h) :=
    pointUnitFiniteRestrictionColimits D l E n j h
  letI : PreservesFiniteLimits
      (pointFiniteSections D.k (Padic.coefficientExtensionRing l E n)) :=
    pointFiniteReductionSectionsLimits D.k l E n
  letI : PreservesFiniteColimits
      (pointFiniteSections D.k (Padic.coefficientExtensionRing l E n)) :=
    pointFiniteReductionSectionsColimits D.k l E n
  letI : PreservesFiniteLimits
      (pointFiniteSections D.k (Padic.coefficientExtensionRing l E j)) :=
    pointFiniteReductionSectionsLimits D.k l E j
  letI : PreservesFiniteColimits
      (pointFiniteSections D.k (Padic.coefficientExtensionRing l E j)) :=
    pointFiniteReductionSectionsColimits D.k l E j
  letI := HasDerivedCategory.ofIsGrothendieckAbelian.{u + 1}
    (pointFiniteReductionModules l E j)
  letI := HasDerivedCategory.ofIsGrothendieckAbelian.{u + 1}
    (pointFiniteReductionModules l E n)
  letI : (pointUnitFiniteModuleRestriction l E n j h).Additive := ⟨by intros; rfl⟩
  letI : (pointFiniteSections D.k (Padic.coefficientExtensionRing l E n)).Additive :=
    pointFiniteSectionsAdditive _ _
  letI : (pointFiniteSections D.k (Padic.coefficientExtensionRing l E j)).Additive :=
    pointFiniteSectionsAdditive _ _
  letI : PreservesFiniteLimits
      (pointUnitFiniteRestriction D l E n j h ⋙
        pointFiniteSections D.k (Padic.coefficientExtensionRing l E n)) :=
    comp_preservesFiniteLimits _ _
  letI : PreservesFiniteColimits
      (pointUnitFiniteRestriction D l E n j h ⋙
        pointFiniteSections D.k (Padic.coefficientExtensionRing l E n)) :=
    comp_preservesFiniteColimits _ _
  letI : PreservesFiniteLimits
      (pointFiniteSections D.k (Padic.coefficientExtensionRing l E j) ⋙
        pointUnitFiniteModuleRestriction l E n j h) := comp_preservesFiniteLimits _ _
  letI : PreservesFiniteColimits
      (pointFiniteSections D.k (Padic.coefficientExtensionRing l E j) ⋙
        pointUnitFiniteModuleRestriction l E n j h) := comp_preservesFiniteColimits _ _
  convert! ((Functor.mapDerivedCategoryCompIso (pointUnitFiniteRestriction D l E n j h)
    (pointFiniteSections D.k (Padic.coefficientExtensionRing l E n))).symm ≪≫
    Functor.mapDerivedCategoryNatIso (pointUnitFiniteSectionsRestrictionIso D l E n j h) ≪≫
    Functor.mapDerivedCategoryCompIso
      (pointFiniteSections D.k (Padic.coefficientExtensionRing l E j))
      (pointUnitFiniteModuleRestriction l E n j h)) using 3


/-- The actual integral module scalar-extension unit, fixed on tensor representatives.
Source: Stacks 07A6, 09T5 (blueprint: def-trf-point-reduction-units). -/
def pointUnitIntegralModuleUnit (n : ℕ) :
    𝟭 _ ⟶ pointReductionModuleTensor l E n ⋙ pointUnitIntegralDerivedRestriction l E n :=
  (pointUnitIntegralModuleAdjunction l E n).choose.unit

/-- The actual integral sheaf scalar-extension unit from the published adjunction.
Source: Stacks 07A6, 09T5 (blueprint: def-trf-point-reduction-units). -/
def pointUnitIntegralSheafUnit (n : ℕ) :
    𝟭 _ ⟶ scalarReductionDerivedExtension l E (Spec (.of D.k)) n ⋙
      scalarReductionDerivedRestriction l E (Spec (.of D.k)) n :=
  (derivedScalarExtensionRestrictionAdjunction l E (Spec (.of D.k)) n).choose.unit

/-- The actual finite module scalar-extension unit, fixed on tensor representatives.
Source: Stacks 07A6, 09T5 (blueprint: def-trf-point-reduction-units). -/
def pointUnitFiniteModuleUnit (n j : ℕ) (h : j ≤ n) :
    𝟭 _ ⟶ pointFiniteReductionModuleTensor l E n j h ⋙
      pointUnitFiniteDerivedModuleRestriction l E n j h :=
  (pointUnitFiniteModuleAdjunction l E n j h).choose.unit

/-- The actual finite sheaf scalar-extension unit, with ordinary and derived normalization.
Source: Stacks 07A6, 09T5 (blueprint: def-trf-point-reduction-units). -/
def pointUnitFiniteSheafUnit (n j : ℕ) (h : j ≤ n) :
    𝟭 _ ⟶ pointFiniteReductionSheafTensor D.k l E n j h ⋙
      pointUnitFiniteDerivedRestriction D l E n j h :=
  (pointUnitFiniteSheafAdjunction D l E n j h).choose_spec.2.choose.unit

end WeilConjectures
