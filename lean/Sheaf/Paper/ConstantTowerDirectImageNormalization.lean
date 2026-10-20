/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q16
-/
module

public import Mathlib.CategoryTheory.Products.Basic
public import Sheaf.AlgebraicGeometry.StrictConstantTowerOperations
public import Sheaf.Paper.CompleteCoefficientDatum
public import Sheaf.Paper.CompletedRlimFunctor
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
import all Sheaf.AlgebraicGeometry.StrictConstantTowerOperations
import Sheaf.Paper.BoundedConstructibleTower
import all Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction
import Sheaf.AlgebraicGeometry.ProfiniteCoefficientInverseImage
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.FullyFaithful
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import Mathlib.Algebra.Homology.Functor
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Homology.HomotopyCategory.Triangulated
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Mathlib.CategoryTheory.Sites.Limits
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.CategoryTheory.NatTransFromResolvingClass
import Sheaf.AlgebraicGeometry.ProEtaleAlgebraicInverseImage
import Sheaf.AlgebraicGeometry.ProEtaleToposFunctorialityInverseImage
import Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients
import Sheaf.Paper.KFlatRingedToposPullback

/-!
# Constant strict towers and normalized direct image

Source: Stacks, Tags 08BJ, 070K, 0940, 0941, 0A07, 06YS, 07A4 and 0B56;
agent-supplied constant-tower normalization supporting fix-lem-exchanges, Step 5
(blueprint: lem-sf-cbc-constant-tower-direct-image-normalization).

The index n denotes positive exponent n+1. Quotients need not be finite sets.
All tower derived categories localize strict diagrams before evaluation.

## Main definitions

* `chi`: the canonical diagonal/direct-image natural isomorphism.
* `deltaLimit`: the inverse of the diagonal/derived-limit adjunction unit.
* `reduction` and `augmentation`: quotient-tower tensor and its canonical unit map.
* `projection`: the normalized whole-tower counit mate.

## Main statements

* `constantTowerDirectImageNormalization`: the four requested normalizations.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.ProEtale.StrictTower.ConstantNormalization

attribute [local irreducible] CochainComplex.IsKFlatIndependentCoefficients

section GenericNormalization
universe u₁ u₂ u₃ u₄ v₁ v₂ v₃ v₄ w₁ w₂ w₃ w₄
variable {C : Type u₁} [Category.{v₁} C] [Abelian C] [HasDerivedCategory.{w₁} C]
  {D : Type u₂} [Category.{v₂} D] [Abelian D] [HasDerivedCategory.{w₂} D]
  {T : Type u₃} [Category.{v₃} T] [Abelian T] [HasDerivedCategory.{w₃} T]
  {U : Type u₄} [Category.{v₄} U] [Abelian U] [HasDerivedCategory.{w₄} U]

/-- The literal ordinary-square normalization on every K-injective representative.
The formula includes the exact-localization and derived-resolution comparisons.
Source: Stacks 070K (blueprint: lem-sf-cbc-constant-tower-direct-image-normalization). -/
def IsDirectImageNormalizedOnKInjectives
    (F : C ⥤ D) [F.Additive] (P : C ⥤ T) [P.Additive]
    [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    (Q : D ⥤ U) [Q.Additive] [PreservesFiniteLimits Q] [PreservesFiniteColimits Q]
    (H : T ⥤ U) [H.Additive]
    [Abelian.HasKInjectiveResolutions C] [Abelian.HasKInjectiveResolutions T]
    [P.PreservesKInjectiveComplexes]
    (e : F ⋙ Q ≅ P ⋙ H)
    (χ : F.rightDerivedFunctor ⋙ Q.mapDerivedCategory ≅
      P.mapDerivedCategory ⋙ H.rightDerivedFunctor) : Prop :=
  ∀ (J : CochainComplex C ℤ) [J.IsKInjective],
    χ.hom.app (DerivedCategory.Q.obj J) ≫
        H.rightDerivedFunctor.map (P.mapDerivedCategoryFactors.hom.app J) ≫
        (H.rightDerivedFunctorObjQIso ((P.mapHomologicalComplex (.up ℤ)).obj J)).hom =
      Q.mapDerivedCategory.map (F.rightDerivedFunctorObjQIso J).hom ≫
        Q.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj J) ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex e (.up ℤ)).hom.app J)

/-- The canonical pullback/reduction square at a homotopy representative. The two
counits and exact-localization factors specify the whole-tower tensor comparison.
Source: Stacks 06YY, 07A4
(blueprint: lem-sf-cbc-constant-tower-direct-image-normalization). -/
def IsReductionPullAt
    (P : C ⥤ T) [P.Additive] (Q : D ⥤ U) [Q.Additive]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (H : T ⥤ U) [H.Additive] [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (RP : DerivedCategory C ⥤ DerivedCategory T)
    (RQ : DerivedCategory D ⥤ DerivedCategory U)
    (cP : DerivedCategory.Qh ⋙ RP ⟶ P.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (cQ : DerivedCategory.Qh ⋙ RQ ⟶ Q.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (e : P ⋙ H ≅ F ⋙ Q)
    (τ : RP ⋙ H.mapDerivedCategory ≅ F.mapDerivedCategory ⋙ RQ)
    (K : HomotopyCategory C (.up ℤ)) : Prop :=
  τ.hom.app (DerivedCategory.Qh.obj K) ≫
      RQ.map (F.mapDerivedCategoryFactorsh.hom.app K) ≫
      cQ.app ((F.mapHomotopyCategory (.up ℤ)).obj K) =
    H.mapDerivedCategory.map (cP.app K) ≫
      H.mapDerivedCategoryFactorsh.hom.app ((P.mapHomotopyCategory (.up ℤ)).obj K) ≫
      DerivedCategory.Qh.map
        ((Functor.mapHomotopyCategoryCompIso e (.up ℤ)).hom.app K ≫
          (Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ Q)) (.up ℤ)).inv.app K)

end GenericNormalization

section KFlatResolutionAPI
universe a b r
private theorem exists_kflat_resolution
    {C : Type a} [Category.{b} C] [EssentiallySmall.{r} C]
    {J : GrothendieckTopology C} {R : Sheaf J CommRingCat.{r}}
    (E : CochainComplex (SheafOfModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ℤ) :
    ∃ (P : CochainComplex (SheafOfModules.{r}
        ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ℤ) (s : P ⟶ E),
      CochainComplex.IsKFlatIndependentCoefficients (R := R) P ∧ QuasiIso s := by
  obtain ⟨P, s, hP, _, hs, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients (R := R) E
  exact ⟨P, s, hP, hs⟩
end KFlatResolutionAPI

section GenericComparison
universe u₀ v₀ w₀
variable {C D T U : Type u₀} [Category.{v₀} C] [Category.{v₀} D]
  [Category.{v₀} T] [Category.{v₀} U] [Abelian C] [Abelian D] [Abelian T] [Abelian U]
  [HasDerivedCategory.{w₀} C] [HasDerivedCategory.{w₀} D]
  [HasDerivedCategory.{w₀} T] [HasDerivedCategory.{w₀} U]
  [Abelian.HasKInjectiveResolutions C] [Abelian.HasKInjectiveResolutions T]
private theorem quotient_hom_id {B : Type u₀} [Category.{v₀} B] [Abelian B]
    [HasDerivedCategory.{w₀} B] (J : CochainComplex B ℤ) :
    (DerivedCategory.quotientCompQhIso B).hom.app J = 𝟙 _ := rfl
private theorem quotient_inv_id {B : Type u₀} [Category.{v₀} B] [Abelian B]
    [HasDerivedCategory.{w₀} B] (J : CochainComplex B ℤ) :
    (DerivedCategory.quotientCompQhIso B).inv.app J = 𝟙 _ := rfl
private theorem homotopy_inv_id {B E : Type u₀} [Category.{v₀} B] [Category.{v₀} E]
    [Abelian B] [Abelian E] (F : B ⥤ E) [F.Additive] (J : CochainComplex B ℤ) :
    (F.mapHomotopyCategoryFactors (.up ℤ)).inv.app J = 𝟙 _ := rfl
variable (F : C ⥤ D) (P : C ⥤ T) (Q : D ⥤ U) (H : T ⥤ U)
  [F.Additive] [P.Additive] [Q.Additive] [H.Additive]
  [PreservesFiniteLimits P] [PreservesFiniteColimits P]
  [PreservesFiniteLimits Q] [PreservesFiniteColimits Q]
  [P.PreservesKInjectiveComplexes] (e : F ⋙ Q ≅ P ⋙ H)
private def derivedSquare : F.rightDerivedFunctor ⋙ Q.mapDerivedCategory ≅
    P.mapDerivedCategory ⋙ H.rightDerivedFunctor :=
  (Functor.rightDerivedFunctorCompMapDerivedCategoryIso F Q).symm ≪≫
    Functor.rightDerivedFunctorNatIso e ≪≫ Functor.rightDerivedFunctorCompIso P H ≪≫
      Functor.isoWhiskerRight P.rightDerivedFunctorIsoMapDerivedCategory H.rightDerivedFunctor
set_option backward.isDefEq.respectTransparency false in
private theorem derivedSquare_factorsh (K : HomotopyCategory C (.up ℤ)) :
    Q.mapDerivedCategory.map (F.rightDerivedFunctorUnit.app K) ≫
      (derivedSquare F P Q H e).hom.app (DerivedCategory.Qh.obj K) ≫
      H.rightDerivedFunctor.map (P.mapDerivedCategoryFactorsh.hom.app K) =
    Q.mapDerivedCategoryFactorsh.hom.app ((F.mapHomotopyCategory (.up ℤ)).obj K) ≫
      DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory e.hom (.up ℤ)).app K) ≫
      H.rightDerivedFunctorUnit.app ((P.mapHomotopyCategory (.up ℤ)).obj K) := by
  have h₁ : (Functor.rightDerivedFunctorCompMapDerivedCategoryUnit F Q).app K ≫
      (Functor.rightDerivedFunctorCompMapDerivedCategoryIso F Q).inv.app
        (DerivedCategory.Qh.obj K) = (F ⋙ Q).rightDerivedFunctorUnit.app K := by
    simp [Functor.rightDerivedFunctorCompMapDerivedCategoryIso]
  have h₂ : (F ⋙ Q).rightDerivedFunctorUnit.app K ≫
      (Functor.rightDerivedFunctorNatIso e).hom.app (DerivedCategory.Qh.obj K) =
      DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory e.hom (.up ℤ)).app K) ≫
        (P ⋙ H).rightDerivedFunctorUnit.app K := by
    simp [Functor.rightDerivedFunctorNatIso, Functor.rightDerivedFunctorNatTrans]
  have h₃ : (P ⋙ H).rightDerivedFunctorUnit.app K ≫
      (Functor.rightDerivedFunctorCompIso P H).hom.app (DerivedCategory.Qh.obj K) =
      (Functor.rightDerivedFunctorCompUnit P H).app K := by
    simp [Functor.rightDerivedFunctorCompIso]
  have hc : (Functor.rightDerivedFunctorCompMapDerivedCategoryUnit F Q).app K ≫
      (derivedSquare F P Q H e).hom.app (DerivedCategory.Qh.obj K) =
      DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory e.hom (.up ℤ)).app K) ≫
        (Functor.rightDerivedFunctorCompUnit P H).app K ≫
          H.rightDerivedFunctor.map
            (P.rightDerivedFunctorIsoMapDerivedCategory.hom.app (DerivedCategory.Qh.obj K)) := by
    simp only [derivedSquare, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
      Functor.isoWhiskerRight_hom, Functor.whiskerRight_app]
    rw [reassoc_of% h₁, reassoc_of% h₂, reassoc_of% h₃]
  dsimp only [Functor.rightDerivedFunctorCompMapDerivedCategoryUnit,
    Functor.rightDerivedFunctorCompUnit, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.comp_obj] at hc
  have hq₁ : (Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ Q)) (.up ℤ)).inv.app K =
      𝟙 _ := rfl
  have hq₂ : (Functor.mapHomotopyCategoryCompIso (Iso.refl (P ⋙ H)) (.up ℤ)).inv.app K =
      𝟙 _ := rfl
  rw [hq₁, hq₂] at hc
  erw [DerivedCategory.Qh.map_id, DerivedCategory.Qh.map_id] at hc
  simp only [Category.id_comp, Category.comp_id, Category.assoc] at hc
  have hp := NatTrans.congr_app P.rightDerivedFunctorIsoMapDerivedCategory_hom_fac K
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app] at hp
  rw [← H.rightDerivedFunctor.map_comp, hp] at hc
  apply (cancel_epi (Q.mapDerivedCategoryFactorsh.inv.app
    ((F.mapHomotopyCategory (.up ℤ)).obj K))).1
  simp only [Iso.inv_hom_id_app_assoc]
  erw [reassoc_of% hc]
  rw [← H.rightDerivedFunctor.map_comp, Iso.inv_hom_id_app]
  erw [H.rightDerivedFunctor.map_id]
  simp only [Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
private theorem derivedSquare_normalized :
    IsDirectImageNormalizedOnKInjectives F P Q H e (derivedSquare F P Q H e) := by
  intro J hJ
  let K := (HomotopyCategory.quotient C (.up ℤ)).obj J
  have hc := derivedSquare_factorsh F P Q H e K
  have hH : IsIso (H.rightDerivedFunctorUnit.app
      ((P.mapHomotopyCategory (.up ℤ)).obj K)) := by
    change IsIso (H.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient T (.up ℤ)).obj
      ((P.mapHomologicalComplex (.up ℤ)).obj J)))
    infer_instance
  have hf : (F.rightDerivedFunctorObjQIso J).hom =
      inv (F.rightDerivedFunctorUnit.app K) := by
    dsimp only [Functor.rightDerivedFunctorObjQIso, Iso.trans_hom, Iso.symm_hom,
      Functor.mapIso_hom, Iso.app_hom, Iso.app_inv, NatTrans.comp_app, asIso_inv]
    simp only [quotient_hom_id, quotient_inv_id]
    erw [F.rightDerivedFunctor.map_id, Category.id_comp, Category.comp_id]
  have hh : (H.rightDerivedFunctorObjQIso ((P.mapHomologicalComplex (.up ℤ)).obj J)).hom =
      inv (H.rightDerivedFunctorUnit.app ((P.mapHomotopyCategory (.up ℤ)).obj K)) := by
    dsimp only [Functor.rightDerivedFunctorObjQIso, Iso.trans_hom, Iso.symm_hom,
      Functor.mapIso_hom, Iso.app_hom, Iso.app_inv, NatTrans.comp_app, asIso_inv]
    simp only [quotient_hom_id, quotient_inv_id]
    erw [H.rightDerivedFunctor.map_id, Category.id_comp, Category.comp_id]
    rfl
  rw [hf, hh]
  have hpf : P.mapDerivedCategoryFactors.hom.app J = P.mapDerivedCategoryFactorsh.hom.app K :=
    by
      have ht := P.mapDerivedCategoryFactorsh_hom_app J
      simp only [quotient_hom_id, quotient_inv_id, homotopy_inv_id] at ht
      erw [P.mapDerivedCategory.map_id, DerivedCategory.Qh.map_id] at ht
      erw [Category.id_comp, Category.comp_id, Category.comp_id] at ht
      exact ht.symm
  have hqf : Q.mapDerivedCategoryFactors.hom.app
      ((F.mapHomologicalComplex (.up ℤ)).obj J) =
      Q.mapDerivedCategoryFactorsh.hom.app ((F.mapHomotopyCategory (.up ℤ)).obj K) :=
    by
      have ht := Q.mapDerivedCategoryFactorsh_hom_app
        ((F.mapHomologicalComplex (.up ℤ)).obj J)
      simp only [quotient_hom_id, quotient_inv_id, homotopy_inv_id] at ht
      erw [Q.mapDerivedCategory.map_id, DerivedCategory.Qh.map_id] at ht
      erw [Category.id_comp, Category.comp_id, Category.comp_id] at ht
      exact ht.symm
  rw [hpf, hqf]
  apply (cancel_epi (Q.mapDerivedCategory.map (F.rightDerivedFunctorUnit.app K))).1
  erw [reassoc_of% hc]
  erw [IsIso.hom_inv_id, Category.comp_id]
  rw [← Q.mapDerivedCategory.map_comp_assoc, IsIso.hom_inv_id,
    Q.mapDerivedCategory.map_id, Category.id_comp]
  rfl

variable {V : D ⥤ C} {W : U ⥤ T} [V.Additive] [W.Additive]
  [PreservesFiniteLimits V] [PreservesFiniteColimits V]
  [PreservesFiniteLimits W] [PreservesFiniteColimits W]
set_option backward.isDefEq.respectTransparency false in
private theorem derivedSquare_mate (a : V ⊣ F) (b : W ⊣ H)
    (s : Q ⋙ W ≅ V ⋙ P)
    (hs : (mateEquiv a b (TwoSquare.mk _ _ _ _ s.hom)).natTrans = e.hom) :
    (derivedSquare F P Q H e).hom =
      (mateEquiv a.mapDerivedCategoryRightDerivedAdjunction
        b.mapDerivedCategoryRightDerivedAdjunction
        (TwoSquare.mk _ _ _ _ ((Functor.mapDerivedCategoryCompIso Q W).symm ≪≫
          Functor.mapDerivedCategoryNatIso s ≪≫
            Functor.mapDerivedCategoryCompIso V P).hom)).natTrans := by
  apply Functor.rightDerived_ext (F.rightDerivedFunctor ⋙ Q.mapDerivedCategory)
    (Functor.rightDerivedFunctorCompMapDerivedCategoryUnit F Q)
    (HomotopyCategory.quasiIso C (.up ℤ))
  apply NatTrans.ext
  funext K
  have hc := derivedSquare_factorsh F P Q H e K
  have hm := AlgebraicGeometry.ProEtale.StrictTower.derived_mate_factorsh a b s K
  rw [hs] at hm
  have hid₁ : (Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ Q)) (.up ℤ)).hom.app K =
      𝟙 _ := rfl
  have hid₂ : (Functor.mapHomotopyCategoryCompIso (Iso.refl (P ⋙ H)) (.up ℤ)).inv.app K =
      𝟙 _ := rfl
  rw [hid₁, hid₂] at hm
  simp only [Category.comp_id] at hm
  erw [Category.id_comp] at hm
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.rightDerivedFunctorCompMapDerivedCategoryUnit, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app]
  have hid₃ : (Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ Q)) (.up ℤ)).inv.app K =
      𝟙 _ := rfl
  rw [hid₃]
  erw [DerivedCategory.Qh.map_id]
  simp only [Category.id_comp, Category.comp_id, Category.assoc]
  repeat erw [Category.id_comp]
  apply (cancel_mono (H.rightDerivedFunctor.map (P.mapDerivedCategoryFactorsh.hom.app K))).1
  simpa only [Category.assoc] using congrArg
    (fun k ↦ Q.mapDerivedCategoryFactorsh.inv.app
      ((F.mapHomotopyCategory (.up ℤ)).obj K) ≫ k) (hc.trans hm.symm)

end GenericComparison

section DerivedModelAPI
universe c d vc vd wc wd
/-- A universal left-derived model with its computation on a specified resolving class.
Source: Stacks 06YS, 06YY
(blueprint: lem-sf-cbc-constant-tower-direct-image-normalization). -/
structure DerivedReductionModelData
    {C : Type c} [Category.{vc} C] [Abelian C] [HasDerivedCategory.{wc} C]
    {D : Type d} [Category.{vd} D] [Abelian D] [HasDerivedCategory.{wd} D]
    (E : C ⥤ D) [E.Additive] (S : CochainComplex C ℤ → Prop) where
  functor : DerivedCategory C ⥤ DerivedCategory D
  counit : DerivedCategory.Qh ⋙ functor ⟶
    E.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh
  universal : functor.IsLeftDerivedFunctor counit (HomotopyCategory.quasiIso C (.up ℤ))
  computes : ∀ P, S P →
    IsIso (counit.app ((HomotopyCategory.quotient C (.up ℤ)).obj P))

private theorem derivedModel_exists
    {C : Type c} [Category.{vc} C] [Abelian C] [HasDerivedCategory.{wc} C]
    {D : Type d} [Category.{vd} D] [Abelian D] [HasDerivedCategory.{wd} D]
    (E : C ⥤ D) [E.Additive] (S : CochainComplex C ℤ → Prop)
    (hres : ∀ K, ∃ (P : CochainComplex C ℤ) (s : P ⟶ K), S P ∧ QuasiIso s)
    (hinv : ∀ {P Q : CochainComplex C ℤ} (a : P ⟶ Q),
      S P → S Q → QuasiIso a → QuasiIso ((E.mapHomologicalComplex (.up ℤ)).map a)) :
    Nonempty (DerivedReductionModelData E S) := by
  let H := HomotopyCategory.quotient C (.up ℤ)
  let F := E.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh
  let T : Set (HomotopyCategory C (.up ℤ)) := {K | ∃ P, S P ∧ H.obj P = K}
  have hres' (K : HomotopyCategory C (.up ℤ)) :
      ∃ (K' : HomotopyCategory C (.up ℤ)) (s : K' ⟶ K),
        K' ∈ T ∧ HomotopyCategory.quasiIso C (.up ℤ) s := by
    obtain ⟨K, rfl⟩ := K.quotient_obj_surjective
    obtain ⟨P, s, hP, hs⟩ := hres K
    exact ⟨H.obj P, H.map s, ⟨P, hP, rfl⟩,
      (HomotopyCategory.quotient_map_mem_quasiIso_iff s).2 hs⟩
  have hinv' (K K' : HomotopyCategory C (.up ℤ)) (s : K ⟶ K')
      (hK : K ∈ T) (hK' : K' ∈ T) (hs : HomotopyCategory.quasiIso C (.up ℤ) s) :
      IsIso (F.map s) := by
    obtain ⟨P, hP, rfl⟩ := hK
    obtain ⟨Q, hQ, rfl⟩ := hK'
    obtain ⟨a, rfl⟩ := H.map_surjective s
    have ha := (HomotopyCategory.quotient_map_mem_quasiIso_iff a).1 hs
    have hEa := hinv a hP hQ ha
    dsimp only [F, Functor.comp_map, Functor.mapHomotopyCategory_map]
    apply Localization.inverts DerivedCategory.Qh (HomotopyCategory.quasiIso D (.up ℤ))
    exact (HomotopyCategory.quotient_map_mem_quasiIso_iff _).2 hEa
  let : F.CommShift ℤ := by dsimp [F]; infer_instance
  have : F.IsTriangulated := by dsimp [F]; infer_instance
  obtain ⟨_, LF, ε, hLF, _, hε⟩ :=
    Functor.leftDerived_from_resolvingClass C (DerivedCategory D) F T hres' hinv'
  exact ⟨⟨LF, ε, hLF, fun P hP ↦ hε (H.obj P) ⟨P, hP, rfl⟩⟩⟩
end DerivedModelAPI

namespace DerivedComparisonProof
private theorem ext_resolving
    {C E : Type*} [Category C] [Category E]
    (W : MorphismProperty C) (S : C → Prop)
    (hres : ∀ K, ∃ (P : C) (s : P ⟶ K), S P ∧ W s)
    (A B : C ⥤ E) (hA : W.IsInvertedBy A) (a b : A ⟶ B)
    (h : ∀ P, S P → a.app P = b.app P) : a = b := by
  ext K
  obtain ⟨P, s, hP, hs⟩ := hres K
  have : IsIso (A.map s) := hA _ hs
  apply (cancel_epi (A.map s)).1
  rw [a.naturality, b.naturality, h P hP]

private theorem comparison_existsUnique
    {C D E : Type*} [Category C] [Category D] [Category E]
    (Q : C ⥤ D) (W : MorphismProperty C) [Q.IsLocalization W]
    [W.HasRightCalculusOfFractions]
    (S : C → Prop)
    (hres : ∀ K, ∃ (P : C) (s : P ⟶ K), S P ∧ W s)
    (A B : D ⥤ E) (T : C ⥤ E)
    (b : Q ⋙ A ⟶ T) (c : Q ⋙ B ⟶ T)
    (hb : ∀ P, S P → IsIso (b.app P))
    (hc : ∀ P, S P → IsIso (c.app P)) :
    ∃ t : A ≅ B,
      (∀ K, t.hom.app (Q.obj K) ≫ c.app K = b.app K) ∧
      ∀ t' : A ≅ B, (∀ P, S P → t'.hom.app (Q.obj P) ≫ c.app P = b.app P) →
        t' = t := by
  have hA : W.IsInvertedBy (Q ⋙ A) := by
    intro X Y s hs
    have : IsIso (Q.map s) := Localization.inverts Q W s hs
    exact Functor.map_isIso A (Q.map s)
  let a (P : C) (hP : S P) : (Q ⋙ A).obj P ⟶ (Q ⋙ B).obj P :=
    letI := hc P hP
    b.app P ≫ inv (c.app P)
  have ha (P R : C) (hP : S P) (hR : S R) (s : P ⟶ R) :
      (Q ⋙ A).map s ≫ a R hR = a P hP ≫ (Q ⋙ B).map s := by
    let := hc P hP
    let := hc R hR
    apply (cancel_mono (c.app R)).1
    dsimp only [a]
    simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    rw [c.naturality]
    simp only [IsIso.inv_hom_id_assoc]
    exact b.naturality s
  obtain ⟨α, hα⟩ := exists_natTrans_from_resolvingClass W S hres
    (Q ⋙ A) (Q ⋙ B) hA a ha
  have hfac : α ≫ c = b := by
    apply ext_resolving W S hres (Q ⋙ A) T hA
    intro P hP
    let := hc P hP
    change α.app P ≫ c.app P = b.app P
    rw [hα P hP]
    dsimp only [a]
    simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  have (K : C) : IsIso (α.app K) := by
    obtain ⟨P, s, hP, hs⟩ := hres K
    let := hb P hP
    let := hc P hP
    have hPiso : IsIso (α.app P) := by
      rw [hα P hP]
      dsimp only [a]
      infer_instance
    have : IsIso (Q.map s) := Localization.inverts Q W s hs
    have : IsIso ((Q ⋙ A).map s) := Functor.map_isIso A (Q.map s)
    have : IsIso ((Q ⋙ B).map s) := Functor.map_isIso B (Q.map s)
    have : IsIso ((Q ⋙ A).map s ≫ α.app K) := by
      rw [α.naturality]
      infer_instance
    exact IsIso.of_isIso_comp_left ((Q ⋙ A).map s) (α.app K)
  have : IsIso α := NatIso.isIso_of_isIso_app α
  let FF := Localization.fullyFaithfulWhiskeringLeft Q W E
  let t := FF.preimageIso (asIso α)
  have ht (K : C) : t.hom.app (Q.obj K) = α.app K :=
    congr_app (FF.map_preimage α) K
  refine ⟨t, ?_, ?_⟩
  · intro K
    rw [ht]
    exact congr_app hfac K
  · intro t' ht'
    apply Iso.ext
    apply FF.map_injective
    apply ext_resolving W S hres (Q ⋙ A) (Q ⋙ B) hA
    intro P hP
    let := hc P hP
    apply (cancel_mono (c.app P)).1
    change t'.hom.app (Q.obj P) ≫ c.app P = t.hom.app (Q.obj P) ≫ c.app P
    rw [ht, ht' P hP]
    exact (congr_app hfac P).symm
section DerivedSquare
universe ds dv dw
variable {C D T U : Type ds} [Category.{dv} C] [Category.{dv} D]
  [Category.{dv} T] [Category.{dv} U] [Abelian C] [Abelian D] [Abelian T] [Abelian U]
  [HasDerivedCategory.{dw} C] [HasDerivedCategory.{dw} D]
  [HasDerivedCategory.{dw} T] [HasDerivedCategory.{dw} U]
  (F : C ⥤ D) (H : T ⥤ U) (P : C ⥤ T) (Q : D ⥤ U)
  [F.Additive] [H.Additive] [P.Additive] [Q.Additive]
  [Limits.PreservesFiniteLimits F] [Limits.PreservesFiniteColimits F]
  [Limits.PreservesFiniteLimits H] [Limits.PreservesFiniteColimits H]
  (RP : DerivedCategory C ⥤ DerivedCategory T)
  (RQ : DerivedCategory D ⥤ DerivedCategory U)
  (cP : DerivedCategory.Qh ⋙ RP ⟶ P.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
  (cQ : DerivedCategory.Qh ⋙ RQ ⟶ Q.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
  (e : P ⋙ H ≅ F ⋙ Q)

open AlgebraicGeometry.ProEtale.StrictTower.ConstantNormalization

private structure SquareComparisonData
    (S : HomotopyCategory C (.up ℤ) → Prop) where
  iso : RP ⋙ H.mapDerivedCategory ≅ F.mapDerivedCategory ⋙ RQ
  normalized : ∀ K, IsReductionPullAt P Q F H RP RQ cP cQ e iso K
  unique : ∀ τ' : RP ⋙ H.mapDerivedCategory ≅ F.mapDerivedCategory ⋙ RQ,
    (∀ K, S K → IsReductionPullAt P Q F H RP RQ cP cQ e τ' K) → τ' = iso

private theorem derived_square_exists
    (S : HomotopyCategory C (.up ℤ) → Prop)
    (hres : ∀ K, ∃ (L : HomotopyCategory C (.up ℤ)) (s : L ⟶ K),
      S L ∧ HomotopyCategory.quasiIso C (.up ℤ) s)
    (hP : ∀ K, S K → IsIso (cP.app K))
    (hQ : ∀ K, S K → IsIso (cQ.app ((F.mapHomotopyCategory (.up ℤ)).obj K))) :
    Nonempty (SquareComparisonData F H P Q RP RQ cP cQ e S) := by
  let Ph := P.mapHomotopyCategory (.up ℤ)
  let Qh := Q.mapHomotopyCategory (.up ℤ)
  let Fh := F.mapHomotopyCategory (.up ℤ)
  let Hh := H.mapHomotopyCategory (.up ℤ)
  let eH : Ph ⋙ Hh ≅ Fh ⋙ Qh :=
    Functor.mapHomotopyCategoryCompIso e (.up ℤ) ≪≫
      (Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ Q)) (.up ℤ)).symm
  let b : DerivedCategory.Qh ⋙ (RP ⋙ H.mapDerivedCategory) ⟶
      Fh ⋙ (Qh ⋙ DerivedCategory.Qh) :=
    (Functor.associator _ _ _).inv ≫ Functor.whiskerRight cP H.mapDerivedCategory ≫
      (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft Ph H.mapDerivedCategoryFactorsh.hom ≫
      (Functor.associator _ _ _).inv ≫ Functor.whiskerRight eH.hom DerivedCategory.Qh ≫
      (Functor.associator _ _ _).hom
  let c : DerivedCategory.Qh ⋙ (F.mapDerivedCategory ⋙ RQ) ⟶
      Fh ⋙ (Qh ⋙ DerivedCategory.Qh) :=
    (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight F.mapDerivedCategoryFactorsh.hom RQ ≫
      (Functor.associator _ _ _).hom ≫ Functor.whiskerLeft Fh cQ
  have hb (K : HomotopyCategory C (.up ℤ)) (hK : S K) : IsIso (b.app K) := by
    let := hP K hK
    dsimp only [b, NatTrans.comp_app, Functor.associator_inv_app,
      Functor.associator_hom_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
    infer_instance
  have hc (K : HomotopyCategory C (.up ℤ)) (hK : S K) : IsIso (c.app K) := by
    let := hQ K hK
    dsimp only [c, NatTrans.comp_app, Functor.associator_inv_app,
      Functor.associator_hom_app, Functor.whiskerRight_app, Functor.whiskerLeft_app, Fh]
    infer_instance
  have hnorm (τ : RP ⋙ H.mapDerivedCategory ≅ F.mapDerivedCategory ⋙ RQ)
      (K : HomotopyCategory C (.up ℤ)) :
      (τ.hom.app (DerivedCategory.Qh.obj K) ≫ c.app K = b.app K) ↔
        IsReductionPullAt P Q F H RP RQ cP cQ e τ K := by
    simp only [b, c, NatTrans.comp_app, Functor.associator_inv_app,
      Functor.associator_hom_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Category.id_comp, Category.comp_id]
    rfl
  obtain ⟨τ, hτ, huniq⟩ := comparison_existsUnique DerivedCategory.Qh
    (HomotopyCategory.quasiIso C (.up ℤ)) S hres
    (RP ⋙ H.mapDerivedCategory) (F.mapDerivedCategory ⋙ RQ) _ b c hb hc
  exact ⟨⟨τ, fun K ↦ (hnorm τ K).1 (hτ K),
    fun τ' hτ' ↦ huniq τ' (fun K hK ↦ (hnorm τ' K).2 (hτ' K hK))⟩⟩
private structure ComplexSquareComparisonData
    (S : CochainComplex C ℤ → Prop) where
  iso : RP ⋙ H.mapDerivedCategory ≅ F.mapDerivedCategory ⋙ RQ
  normalized : ∀ K, IsReductionPullAt P Q F H RP RQ cP cQ e iso K
  unique : ∀ τ' : RP ⋙ H.mapDerivedCategory ≅ F.mapDerivedCategory ⋙ RQ,
    (∀ K, S K → IsReductionPullAt P Q F H RP RQ cP cQ e τ'
      ((HomotopyCategory.quotient C (.up ℤ)).obj K)) → τ' = iso

private theorem derived_square_exists_complexes
    (S : CochainComplex C ℤ → Prop)
    (hres : ∀ K, ∃ (L : CochainComplex C ℤ) (s : L ⟶ K), S L ∧ QuasiIso s)
    (hP : ∀ K, S K → IsIso (cP.app ((HomotopyCategory.quotient C (.up ℤ)).obj K)))
    (hQ : ∀ K, S K → IsIso (cQ.app ((HomotopyCategory.quotient D (.up ℤ)).obj
      ((F.mapHomologicalComplex (.up ℤ)).obj K)))) :
    Nonempty (ComplexSquareComparisonData F H P Q RP RQ cP cQ e S) := by
  let q := HomotopyCategory.quotient C (.up ℤ)
  let T : HomotopyCategory C (.up ℤ) → Prop := fun K ↦ ∃ L, S L ∧ q.obj L = K
  have hres' (K : HomotopyCategory C (.up ℤ)) :
      ∃ (L : HomotopyCategory C (.up ℤ)) (s : L ⟶ K),
        T L ∧ HomotopyCategory.quasiIso C (.up ℤ) s := by
    obtain ⟨K, rfl⟩ := K.quotient_obj_surjective
    obtain ⟨L, s, hL, hs⟩ := hres K
    exact ⟨q.obj L, q.map s, ⟨L, hL, rfl⟩,
      (HomotopyCategory.quotient_map_mem_quasiIso_iff s).2 hs⟩
  have hP' (K) (hK : T K) : IsIso (cP.app K) := by
    obtain ⟨L, hL, rfl⟩ := hK
    exact hP L hL
  have hQ' (K) (hK : T K) :
      IsIso (cQ.app ((F.mapHomotopyCategory (.up ℤ)).obj K)) := by
    obtain ⟨L, hL, rfl⟩ := hK
    exact hQ L hL
  obtain ⟨d⟩ := derived_square_exists F H P Q RP RQ cP cQ e T hres' hP' hQ'
  refine ⟨⟨d.iso, d.normalized, ?_⟩⟩
  intro τ' hτ'
  apply d.unique τ'
  rintro K ⟨L, hL, rfl⟩
  exact hτ' L hL

private theorem model_square_exists_complexes
    (SP : CochainComplex C ℤ → Prop) (SQ : CochainComplex D ℤ → Prop)
    (mP : DerivedReductionModelData P SP) (mQ : DerivedReductionModelData Q SQ)
    (e : P ⋙ H ≅ F ⋙ Q)
    (hres : ∀ K, ∃ (L : CochainComplex C ℤ) (s : L ⟶ K),
      (SP L ∧ SQ ((F.mapHomologicalComplex (.up ℤ)).obj L)) ∧ QuasiIso s) :
    Nonempty (ComplexSquareComparisonData F H P Q mP.functor mQ.functor
      mP.counit mQ.counit e
      (fun L ↦ SP L ∧ SQ ((F.mapHomologicalComplex (.up ℤ)).obj L))) :=
  derived_square_exists_complexes F H P Q mP.functor mQ.functor mP.counit mQ.counit e
    (fun L ↦ SP L ∧ SQ ((F.mapHomologicalComplex (.up ℤ)).obj L)) hres
    (fun L hL ↦ mP.computes L hL.1) (fun _ hL ↦ mQ.computes _ hL.2)

end DerivedSquare
end DerivedComparisonProof

section CoefficientConstructions
variable (A : Type (u + 1)) [CommRing A]

/-- Exact diagonal, using the existing strict tower category.
Source: Stacks 0941 (blueprint: lem-sf-cbc-constant-tower-direct-image-normalization). -/
abbrev delta (X : Scheme.{u}) :=
  (Functor.const ℕᵒᵖ : Modules A X ⥤ Towers A X).mapDerivedCategory

/-- Ordinary direct image in the same identified constant coefficients.
Source: Stacks 07A5 (blueprint: lem-sf-cbc-constant-tower-direct-image-normalization). -/
abbrev push {X Y : Scheme.{u}} (f : X ⟶ Y) := (moduleDirectImage A f).rightDerivedFunctor

/-- Ordinary exact inverse image.
Source: Stacks 03EK (blueprint: lem-sf-cbc-constant-tower-direct-image-normalization). -/
abbrev pull {X Y : Scheme.{u}} (f : X ⟶ Y) := (modulePullback A f).mapDerivedCategory

/-- The existing unbounded derived inverse limit on the original small site.
Source: Stacks 0941 (blueprint: lem-sf-cbc-constant-tower-direct-image-normalization). -/
abbrev L (X : Scheme.{u}) := completedRlim X (coefficients A X)

/-- The canonical ordinary constant/inverse-image square, with identity components.
Source: Stacks 00YV (blueprint: lem-sf-cbc-constant-tower-direct-image-normalization). -/
def deltaPull {X Y : Scheme.{u}} (f : X ⟶ Y) :
    delta A Y ⋙ G A f ≅ pull A f ⋙ delta A X :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso (Functor.compConstIso ℕᵒᵖ (modulePullback A f)).symm ≪≫
      Functor.mapDerivedCategoryCompIso _ _

/-- Derived diagonal/limit adjunction, with its ordinary diagonal unit.
Source: Stacks 0941 (blueprint: lem-sf-cbc-constant-tower-direct-image-normalization). -/
def deltaAdj (X : Scheme.{u}) : delta A X ⊣ L A X :=
  (constLimAdj : (Functor.const ℕᵒᵖ : Modules A X ⥤ Towers A X) ⊣
    completedTowerLimit X (coefficients A X)).mapDerivedCategoryRightDerivedAdjunction

/-- The common-direct-image comparison is the conjugate of the identity-component square.
This retains the canonical comparison of Tag 0A07, including its unit normalization.
Source: Stacks 0A07 (blueprint: lem-sf-cbc-constant-tower-direct-image-normalization). -/
def limitPush {X Y : Scheme.{u}} (f : X ⟶ Y) :
    L A X ⋙ push A f ≅ R A f ⋙ L A Y :=
  conjugateIsoEquiv
    ((proEtaleRingDerivedAdjunction f (coefficients A Y) (coefficients A X)
      (constantRingIso A f)).comp (deltaAdj A X))
    ((deltaAdj A Y).comp (adj A f)) (deltaPull A f)

/-- The exact diagonal preserves K-injectives because it is right adjoint to exact
terminal-index evaluation. Source: Stacks 08BJ
(blueprint: lem-sf-cbc-constant-tower-direct-image-normalization).
Proof: a map from a tower to a constant tower is uniquely determined at index zero;
all other components are its composites with the transitions to zero. This gives
an adjunction from exact evaluation to the diagonal. Transport a map from an acyclic
complex through that adjunction and use K-injectivity to null-homotope it. -/
@[instance] theorem delta_preservesKInjective (X : Scheme.{u}) :
    (Functor.const ℕᵒᵖ : Modules A X ⥤ Towers A X).PreservesKInjectiveComplexes := by
  let adj₀ : (evaluation ℕᵒᵖ (Modules A X)).obj (op 0) ⊣ Functor.const ℕᵒᵖ :=
    { unit :=
        { app := fun M ↦
            { app := fun n ↦ M.map (homOfLE (Nat.zero_le n.unop)).op
              naturality := by
                intro i j f
                change M.map f ≫ M.map _ = M.map _ ≫ 𝟙 _
                rw [Category.comp_id, ← M.map_comp]
                congr 1 }
          naturality := by
            intro M N f
            apply NatTrans.ext
            funext n
            exact (f.naturality _).symm }
      counit := 𝟙 _
      left_triangle_components := by intro M; simp
      right_triangle_components := by intro M; ext n; simp }
  exact adj₀.preservesKInjectiveComplexes

/-- The canonical derived direct-image/diagonal isomorphism. Both composition
comparisons retain their universal derived units; the middle comparison has identity
components on ordinary modules.
Source: Stacks 08BJ, 070K
(blueprint: lem-sf-cbc-constant-tower-direct-image-normalization). -/
def chi {X Y : Scheme.{u}} (f : X ⟶ Y) :
    push A f ⋙ delta A Y ≅ delta A X ⋙ R A f :=
  (Functor.rightDerivedFunctorCompMapDerivedCategoryIso (moduleDirectImage A f)
    (Functor.const ℕᵒᵖ)).symm ≪≫
  Functor.rightDerivedFunctorNatIso (Functor.compConstIso ℕᵒᵖ (moduleDirectImage A f)) ≪≫
  Functor.rightDerivedFunctorCompIso (Functor.const ℕᵒᵖ) (towerDirectImage A f) ≪≫
  Functor.isoWhiskerRight
    (Functor.rightDerivedFunctorIsoMapDerivedCategory (Functor.const ℕᵒᵖ)) (R A f)

/-- Evaluation of a diagonal is canonically the identity.
Source: Stacks 0941 (blueprint: lem-sf-cbc-constant-tower-direct-image-normalization). -/
def deltaEval (X : Scheme.{u}) (n : ℕ) : delta A X ⋙ ev A X n ≅ 𝟭 _ :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso
      (Functor.constCompEvaluationObj (D := Modules A X) (op n)) ≪≫
      Functor.mapDerivedCategoryIdIso _

/-- The constant-tower unit is invertible for every unbounded complex.
Source: Stacks 0941 (blueprint: lem-sf-cbc-constant-tower-direct-image-normalization).
Proof: take a K-injective representative J. The diagonal of J is K-injective by
terminal-index evaluation. Its ordinary inverse limit is J, with identity cone.
The derived adjunction unit is the ordinary unit on this representative, hence is
invertible. Naturality and resolving quasi-isomorphisms give every derived object. -/
theorem deltaUnit_isIso (X : Scheme.{u}) : IsIso (deltaAdj A X).unit := by
  have hff : (Functor.const ℕᵒᵖ : Modules A X ⥤ Towers A X).rightDerivedFunctor.Full :=
    inferInstance
  have hfa : (Functor.const ℕᵒᵖ : Modules A X ⥤ Towers A X).rightDerivedFunctor.Faithful :=
    inferInstance
  have : (delta A X).Full := Functor.Full.of_iso
    (Functor.rightDerivedFunctorIsoMapDerivedCategory
      (Functor.const ℕᵒᵖ : Modules A X ⥤ Towers A X))
  have : (delta A X).Faithful := Functor.Faithful.of_iso
    (Functor.rightDerivedFunctorIsoMapDerivedCategory
      (Functor.const ℕᵒᵖ : Modules A X ⥤ Towers A X))
  exact (deltaAdj A X).unit_isIso_of_L_fully_faithful

/-- The specified identification Rlim(delta M) = M, inverse to the canonical unit.
Source: Stacks 0941 (blueprint: lem-sf-cbc-constant-tower-direct-image-normalization). -/
def deltaLimit (X : Scheme.{u}) : delta A X ⋙ L A X ≅ 𝟭 _ :=
  (@asIso _ _ _ _ (deltaAdj A X).unit (deltaUnit_isIso A X)).symm

attribute [local irreducible] completedAdicChangeData

private theorem scalarChange_obj (X : Scheme.{u})
    {R S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    (φ : R ⟶ S) (M : reductionModules X R) :
    (reductionChange X φ).obj M = SheafOfModules.changeOfRings.{u, u + 1, u + 1} φ M :=
  (reductionChangeExistence X φ).choose_spec.choose M

private theorem scalarChange_quasiIso (X : Scheme.{u})
    {R S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}} (φ : R ⟶ S)
    {P Q : CochainComplex (reductionModules X R) ℤ} (a : P ⟶ Q)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (R := R) P)
    (hQ : CochainComplex.IsKFlatIndependentCoefficients (R := R) Q)
    (ha : QuasiIso a) :
    QuasiIso (((reductionChange X φ).mapHomologicalComplex (.up ℤ)).map a) := by
  let H := HomotopyCategory.quotient (reductionModules X R) (.up ℤ)
  let ε := reductionDerivedCounit X φ
  have hεP : IsIso (ε.app (H.obj P)) :=
    pbcExtensionCounit_isIso φ P hP
  have hεQ : IsIso (ε.app (H.obj Q)) :=
    pbcExtensionCounit_isIso φ Q hQ
  have : IsIso (DerivedCategory.Qh.map (H.map a)) :=
    (DerivedCategory.isIso_Qh_map_iff _).2
      ((HomotopyCategory.quotient_map_mem_quasiIso_iff a).2 ha)
  have := hεP
  have := hεQ
  have hn := ε.naturality (H.map a)
  have hmap : IsIso (((reductionChange X φ).mapHomotopyCategory (.up ℤ) ⋙
      DerivedCategory.Qh).map (H.map a)) := by
    have hcomp : IsIso (ε.app (H.obj P) ≫
        ((reductionChange X φ).mapHomotopyCategory (.up ℤ) ⋙
          DerivedCategory.Qh).map (H.map a)) := by
      rw [← hn]
      change IsIso ((reductionDerivedChange X φ).map
        (DerivedCategory.Qh.map (H.map a)) ≫ ε.app (H.obj Q))
      infer_instance
    exact @IsIso.of_isIso_comp_left _ _ _ _ _ _ _ hεP hcomp
  apply (HomotopyCategory.quotient_map_mem_quasiIso_iff _).1
  apply (DerivedCategory.isIso_Qh_map_iff _).1
  exact hmap




private theorem scalarRestriction_quasiIso (X : Scheme.{u})
    {R S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}} (φ : R ⟶ S)
    {P Q : CochainComplex (reductionModules X S) ℤ} (a : P ⟶ Q) [QuasiIso a] :
    QuasiIso (((reductionRestrict X φ).mapHomologicalComplex (.up ℤ)).map a) := by
  have : PreservesFiniteLimits (reductionRestrict X φ) :=
    proEtaleRingRestrictScalars_preservesFiniteLimits φ
  have : PreservesFiniteColimits (reductionRestrict X φ) :=
    proEtaleRingRestrictScalars_preservesFiniteColimits φ
  infer_instance

open scoped ChangeOfRings in
private theorem tensorSection_formula (X : Scheme.{u})
    {R S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}} (φ : R ⟶ S)
    (M : reductionModules X R) (U : X.ProEtᵒᵖ) (s : S.obj.obj U) (x : M.val.obj U) :
    reductionTensorSection X φ M U s x =
      (eqToHom (scalarChange_obj X φ M).symm).val.app U
        (((PresheafOfModules.sheafificationAdjunction.{u + 1}
          (𝟙 (reductionModuleRing X S).obj)).unit.app
            (SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} φ M)).app U
              (s ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] x)) := rfl

attribute [local irreducible] completedAdicChange

variable {A} (I : Ideal A)

/-- The genuine quotient map of constant coefficient sheaves at positive exponent n+1.
Source: Stacks 099M (blueprint: lem-sf-cbc-constant-tower-direct-image-normalization). -/
def quotient (X : Scheme.{u}) (n : ℕ) :
    coefficients A X ⟶ coefficients (A ⧸ I ^ (n + 1)) X :=
  (constantSheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}).map
    (CommRingCat.ofHom (Ideal.Quotient.mk _))

/-- The quotient transition of constant sheaves, including its coefficient action.
Source: Stacks 099M (blueprint: lem-sf-cbc-constant-tower-direct-image-normalization). -/
def quotientStep (X : Scheme.{u}) (n : ℕ) :
    coefficients (A ⧸ I ^ (n + 2)) X ⟶ coefficients (A ⧸ I ^ (n + 1)) X :=
  (constantSheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}).map
    (CommRingCat.ofHom (Ideal.Quotient.factorPow I (Nat.le_succ (n + 1))))

/-- Ordinary tensor with a quotient, restricted back to the original coefficients.
Source: Stacks 06YY (blueprint: lem-sf-cbc-constant-tower-direct-image-normalization). -/
def level (X : Scheme.{u}) (n : ℕ) : Modules A X ⥤ Modules A X :=
  reductionChange X (quotient I X n) ⋙ reductionRestrict X (quotient I X n)


open scoped ChangeOfRings in
set_option backward.isDefEq.respectTransparency false in
private theorem tensorSection_smul (X : Scheme.{u})
    {R S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    (φ : R ⟶ S) (M : reductionModules X R)
    (U : X.ProEtᵒᵖ) (s t : S.obj.obj U)
    (x : M.val.obj U) :
    s • reductionTensorSection X φ M U t x =
      reductionTensorSection X φ M U (s * t) x := by
  rw [tensorSection_formula, tensorSection_formula]
  let T := SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} φ M
  let b : T ⟶ ((reductionChange X φ).obj M).val :=
    (PresheafOfModules.sheafificationAdjunction.{u + 1}
      (𝟙 (reductionModuleRing X S).obj)).unit.app T ≫
      (eqToHom (scalarChange_obj X φ M).symm).val
  change s • b.app U (t ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] x) = _
  rw [← map_smul]
  rfl

private theorem scalarAdj_unit (X : Scheme.{u})
    {R S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}} (φ : R ⟶ S)
    (M : reductionModules X R) (U : X.ProEtᵒᵖ) (x : M.val.obj U) :
    ((pbcScalarAdjunction φ).unit.app M).val.app U x =
      reductionTensorSection X φ M U 1 x :=
  (pbcScalarAdjunction_exists φ).exists.choose_spec M U x

open scoped ChangeOfRings in
set_option backward.isDefEq.respectTransparency false in
private def scalarUnitMap (X : Scheme.{u})
    {R S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    (φ : R ⟶ S) (M : reductionModules X R) :
    M ⟶ (reductionRestrict X φ).obj ((reductionChange X φ).obj M) :=
  (pbcScalarAdjunction φ).unit.app M

private def levelUnitMap (X : Scheme.{u}) (n : ℕ) (M : Modules A X) :
    M ⟶ (level I X n).obj M := scalarUnitMap X (quotient I X n) M

private theorem levelUnitMap_apply (X : Scheme.{u}) (n : ℕ) (M : Modules A X)
    (U : X.ProEtᵒᵖ) (x : M.val.obj U) :
    (levelUnitMap I X n M).val.app U x =
      reductionTensorSection X (quotient I X n) M U 1 x := by
  exact scalarAdj_unit X (quotient I X n) M U x

attribute [local irreducible] scalarUnitMap

open scoped ChangeOfRings in
private theorem scalarTensorSection_map (X : Scheme.{u})
    {R S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    (φ : R ⟶ S) {M N : reductionModules X R} (a : M ⟶ N) (U : X.ProEtᵒᵖ)
    (s : S.obj.obj U) (x : M.val.obj U) :
    (((reductionChange X φ ⋙ reductionRestrict X φ)).map a).val.app U
        (reductionTensorSection X φ M U s x) =
      reductionTensorSection X φ N U s (a.val.app U x) := by
  let η := (pbcScalarAdjunction φ).unit
  have hc := congrArg (fun k ↦ k.val.app U x) (η.naturality a)
  change (η.app N).val.app U (a.val.app U x) =
    ((reductionChange X φ).map a).val.app U ((η.app M).val.app U x) at hc
  erw [scalarAdj_unit, scalarAdj_unit] at hc
  have hm := tensorSection_smul X φ M U s 1 x
  have hn := tensorSection_smul X φ N U s 1 (a.val.app U x)
  simp only [mul_one] at hm hn
  change ((reductionChange X φ).map a).val.app U
    (reductionTensorSection X φ M U s x) = _
  rw [← hm, ← hn, map_smul, hc]

private theorem tensorSection_map (X : Scheme.{u}) (n : ℕ)
    {M N : Modules A X} (a : M ⟶ N) (U : X.ProEtᵒᵖ)
    (s : (coefficients (A ⧸ I ^ (n + 1)) X).obj.obj U) (x : M.val.obj U) :
    ((level I X n).map a).val.app U
        (reductionTensorSection X (quotient I X n) M U s x) =
      reductionTensorSection X (quotient I X n) N U s (a.val.app U x) :=
  scalarTensorSection_map X (quotient I X n) a U s x

attribute [local semireducible] completedAdicChange in
open scoped ChangeOfRings in
set_option backward.isDefEq.respectTransparency false in
private theorem level_hom_ext (X : Scheme.{u})
    {R S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    (φ : R ⟶ S) (M N : reductionModules X R)
    (f g : (reductionRestrict X φ).obj ((reductionChange X φ).obj M) ⟶ N)
    (h : ∀ (U : X.ProEtᵒᵖ)
      (s : S.obj.obj U) (x : M.val.obj U),
      f.val.app U (reductionTensorSection X φ M U s x) =
        g.val.app U (reductionTensorSection X φ M U s x)) : f = g := by
  let hM := scalarChange_obj X φ M
  apply (SheafOfModules.toSheaf (reductionModuleRing X R)).map_injective
  let adjS := sheafificationAdjunction (ProEt.topology X) AddCommGrpCat.{u + 1}
  let j := (SheafOfModules.toSheaf _).map (eqToHom hM.symm)
  apply (cancel_epi j).mp
  apply (adjS.homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  ext U t
  induction t using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add t t' ht ht' => simp only [map_add, ht, ht']
  | tmul s x => exact h U s x

private theorem scalarExtension_tmul (X : Scheme.{u})
    {R S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}} (φ : R ⟶ S)
    (M : reductionModules X R) (N : reductionModules X S)
    (a : M ⟶ (reductionRestrict X φ).obj N) (U : X.ProEtᵒᵖ)
    (s : S.obj.obj U) (x : M.val.obj U) :
    (((pbcScalarAdjunction φ).homEquiv _ _).symm a).val.app U
      (reductionTensorSection X φ M U s x) =
        s • (show N.val.obj U from a.val.app U x) := by
  let adj := pbcScalarAdjunction φ
  let b := (adj.homEquiv M N).symm a
  have he := (adj.homEquiv M N).apply_symm_apply a
  rw [Adjunction.homEquiv_unit] at he
  have he' := congrArg (fun k ↦ k.val.app U x) he
  change b.val.app U ((adj.unit.app M).val.app U x) = a.val.app U x at he'
  erw [scalarAdj_unit] at he'
  have hm := tensorSection_smul X φ M U s 1 x
  simp only [mul_one] at hm
  change b.val.app U (reductionTensorSection X φ M U s x) = _
  rw [← hm, map_smul, he']

open scoped ChangeOfRings in
set_option backward.isDefEq.respectTransparency false in
private theorem step_map_exists (X : Scheme.{u})
    {R S T : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    (φ : R ⟶ S) (ψ : R ⟶ T) (q : S ⟶ T) (hcomp : φ ≫ q = ψ)
    (M : reductionModules X R) (unitMap : M ⟶ (reductionRestrict X ψ).obj
      ((reductionChange X ψ).obj M))
    (hunit : ∀ (U : X.ProEtᵒᵖ) (x : M.val.obj U),
      unitMap.val.app U x = reductionTensorSection X ψ M U 1 x) :
    ∃ b : (reductionRestrict X φ).obj ((reductionChange X φ).obj M) ⟶
        (reductionRestrict X ψ).obj ((reductionChange X ψ).obj M),
      ∀ (U : X.ProEtᵒᵖ) (s : S.obj.obj U) (x : M.val.obj U),
        b.val.app U (reductionTensorSection X φ M U s x) =
          reductionTensorSection X ψ M U (q.hom.app U s) x := by
  let N := (reductionRestrict X q).obj ((reductionChange X ψ).obj M)
  have hq (U : X.ProEtᵒᵖ) (r : R.obj.obj U) :
      q.hom.app U (φ.hom.app U r) = ψ.hom.app U r :=
    ConcreteCategory.congr_hom (congrArg (fun k ↦ k.hom.app U) hcomp) r
  let ua := (PresheafOfModules.toPresheaf (reductionModuleRing X R).obj).map unitMap.val
  let a : M ⟶ (reductionRestrict X φ).obj N :=
    ⟨PresheafOfModules.homMk ua (by
        intro U r x
        have h := (unitMap.val.app U).hom.map_smul r x
        change unitMap.val.app U (r • x) =
          q.hom.app U (φ.hom.app U r) •
            (show ((reductionChange X ψ).obj M).val.obj U from unitMap.val.app U x)
        rw [hq]
        exact h)⟩
  let b : (reductionChange X φ).obj M ⟶ N :=
    ((pbcScalarAdjunction φ).homEquiv M N).symm a
  let ub := (PresheafOfModules.toPresheaf (reductionModuleRing X S).obj).map b.val
  let c : (reductionRestrict X φ).obj ((reductionChange X φ).obj M) ⟶
      (reductionRestrict X ψ).obj ((reductionChange X ψ).obj M) :=
    ⟨PresheafOfModules.homMk ub (by
        intro U r x
        have h := (b.val.app U).hom.map_smul (φ.hom.app U r) x
        change b.val.app U ((φ.hom.app U r) •
            (show ((reductionChange X φ).obj M).val.obj U from x)) =
          ψ.hom.app U r •
            (show ((reductionChange X ψ).obj M).val.obj U from b.val.app U x)
        rw [← hq]
        exact h)⟩
  refine ⟨c, ?_⟩
  intro U s x
  change b.val.app U (reductionTensorSection X φ M U s x) = _
  erw [scalarExtension_tmul]
  change q.hom.app U s •
    (show ((reductionChange X ψ).obj M).val.obj U from unitMap.val.app U x) = _
  rw [hunit, tensorSection_smul, mul_one]

private theorem quotientStep_comp (X : Scheme.{u}) (n : ℕ) :
    quotient I X (n + 1) ≫ quotientStep I X n = quotient I X n := by
  dsimp only [quotient, quotientStep]
  rw [← Functor.map_comp]
  congr 1

/-- Quotient transitions are the unique maps on sheafified pure tensors.
Source: Stacks 06YY (blueprint: lem-sf-cbc-constant-tower-direct-image-normalization).
Proof: quotient maps commute with the scalar maps from A, so s tensor x maps to
q(s) tensor x by a balanced linear map. Sheafification extends it uniquely. The
formula proves compatibility with site restrictions and naturality in the module. -/
theorem step_existsUnique (X : Scheme.{u}) (n : ℕ) :
    ∃! τ : level I X (n + 1) ⟶ level I X n,
      ∀ (M : Modules A X) (U : X.ProEtᵒᵖ)
        (s : (coefficients (A ⧸ I ^ (n + 2)) X).obj.obj U) (x : M.val.obj U),
        (τ.app M).val.app U (reductionTensorSection X (quotient I X (n + 1)) M U s x) =
          reductionTensorSection X (quotient I X n) M U
            ((quotientStep I X n).hom.app U s) x := by
  let b (M : Modules A X) := (step_map_exists X (quotient I X (n + 1)) (quotient I X n)
    (quotientStep I X n) (quotientStep_comp I X n) M (levelUnitMap I X n M)
    (levelUnitMap_apply I X n M)).choose
  have hb (M : Modules A X) := (step_map_exists X (quotient I X (n + 1)) (quotient I X n)
    (quotientStep I X n) (quotientStep_comp I X n) M (levelUnitMap I X n M)
    (levelUnitMap_apply I X n M)).choose_spec
  let τ : level I X (n + 1) ⟶ level I X n :=
    { app := b
      naturality := by
        intro M N f
        apply level_hom_ext X (quotient I X (n + 1)) M ((level I X n).obj N)
        intro U s x
        change (b N).val.app U (((level I X (n + 1)).map f).val.app U
            (reductionTensorSection X (quotient I X (n + 1)) M U s x)) =
          ((level I X n).map f).val.app U ((b M).val.app U
            (reductionTensorSection X (quotient I X (n + 1)) M U s x))
        rw [tensorSection_map, hb, hb, tensorSection_map] }
  refine ⟨τ, ?_, ?_⟩
  · intro M U s x
    exact hb M U s x
  · intro τ' hτ'
    apply NatTrans.ext
    funext M
    apply level_hom_ext X (quotient I X (n + 1)) M ((level I X n).obj M)
    intro U s x
    exact (hτ' M U s x).trans (hb M U s x).symm

/-- The strict reduction functor, including all coefficient transition maps.
Source: Stacks 099M (blueprint: lem-sf-cbc-constant-tower-direct-image-normalization). -/
def reductionModule (X : Scheme.{u}) : Modules A X ⥤ Towers A X :=
  (Functor.ofOpSequence (fun n ↦ (step_existsUnique I X n).exists.choose)).flip

/-- Reduction is additive before localization.
Source: Stacks 06YY (blueprint: lem-sf-cbc-constant-tower-direct-image-normalization).
Proof: every level is scalar extension followed by additive scalar restriction.
Evaluation jointly detects equality of maps of strict diagrams. -/
@[instance] theorem reductionModule_additive (X : Scheme.{u}) :
    (reductionModule I X).Additive := by
  constructor
  intro M N f g
  apply NatTrans.ext
  funext n
  have : (level I X n.unop).Additive := by
    dsimp [level]
    infer_instance
  exact (level I X n.unop).map_add

/-- The homotopy functor to be left derived.
Source: Stacks 06YY (blueprint: lem-sf-cbc-constant-tower-direct-image-normalization). -/
def reductionHomotopy (X : Scheme.{u}) :
    HomotopyCategory (Modules A X) (.up ℤ) ⥤ Derived A X :=
  (reductionModule I X).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh

/-- A derived reduction pair, retaining its determining universal property and K-flat
computation. Source: Stacks 06YS, 06YY
(blueprint: lem-sf-cbc-constant-tower-direct-image-normalization). -/
abbrev ReductionModel (X : Scheme.{u}) :=
  DerivedReductionModelData (reductionModule I X)
    (CochainComplex.IsKFlatIndependentCoefficients (R := coefficients A X))

/-- Universal derived reduction, with its K-flat representative normalization.
Source: Stacks 06YS, 06YY (blueprint: lem-sf-cbc-constant-tower-direct-image-normalization).
Proof: choose flat-term K-flat resolutions. Their diagonal is K-flat: tensoring an
acyclic tower evaluates to tensoring an acyclic complex with the K-flat model at
every level. Evaluations are exact and jointly detect acyclicity. The strict
quotient construction therefore inverts resolving quasi-isomorphisms. The resolving
class left-derived theorem gives the universal counit, invertible on these models.
This universal property determines the derived pair up to its unique comparison. -/
theorem reduction_exists (X : Scheme.{u}) : Nonempty (ReductionModel I X) := by
  apply derivedModel_exists (reductionModule I X)
    (CochainComplex.IsKFlatIndependentCoefficients (R := coefficients A X))
  · intro E
    exact exists_kflat_resolution (R := coefficients A X) E
  · intro P Q a hP hQ ha
    rw [HomologicalComplex.quasiIso_iff_evaluation]
    intro n
    let φ := quotient I X n.unop
    have hchange : QuasiIso
        (((reductionChange X φ).mapHomologicalComplex (.up ℤ)).map a) :=
      scalarChange_quasiIso X φ a hP hQ ha
    have := hchange
    change QuasiIso (((reductionRestrict X φ).mapHomologicalComplex (.up ℤ)).map
      (((reductionChange X φ).mapHomologicalComplex (.up ℤ)).map a))
    exact scalarRestriction_quasiIso X φ _

/-- Select the derived pair by its universal property, retaining its comparison.
Source: Stacks 06YY (blueprint: lem-sf-cbc-constant-tower-direct-image-normalization). -/
def reductionModel (X : Scheme.{u}) : ReductionModel I X :=
  Classical.choice (reduction_exists I X)

/-- Reduction is the functor of the universal derived pair.
Source: Stacks 06YY (blueprint: lem-sf-cbc-constant-tower-direct-image-normalization). -/
def reduction (X : Scheme.{u}) : DerivedCategory (Modules A X) ⥤ Derived A X :=
  (reductionModel I X).functor

/-- The universal reduction counit, retained rather than forgotten.
Source: Stacks 06YY (blueprint: lem-sf-cbc-constant-tower-direct-image-normalization). -/
def reductionCounit (X : Scheme.{u}) :
    DerivedCategory.Qh ⋙ reduction I X ⟶ reductionHomotopy I X :=
  (reductionModel I X).counit

/-- Ordinary quotient augmentation, uniquely fixed by the tensor unit at every level.
Source: Stacks 06YY (blueprint: lem-sf-cbc-constant-tower-direct-image-normalization).
Proof: insert 1 tensor x. Quotient transitions preserve 1 and their pure tensor
formula therefore makes these maps a strict tower map, natural in the module.
The formula on all sections determines every component uniquely. -/
theorem ordinaryAugmentation_existsUnique (X : Scheme.{u}) :
    ∃! η : (Functor.const ℕᵒᵖ : Modules A X ⥤ Towers A X) ⟶ reductionModule I X,
      ∀ (M : Modules A X) (n : ℕ) (U : X.ProEtᵒᵖ) (x : M.val.obj U),
        ((η.app M).app (op n)).val.app U x =
          reductionTensorSection X (quotient I X n) M U 1 x := by
  let η : (Functor.const ℕᵒᵖ : Modules A X ⥤ Towers A X) ⟶ reductionModule I X :=
    { app := fun M ↦ NatTrans.ofOpSequence (fun n ↦ levelUnitMap I X n M) (by
        intro n
        change levelUnitMap I X n M = levelUnitMap I X (n + 1) M ≫
          ((Functor.ofOpSequence (fun k ↦ (step_existsUnique I X k).exists.choose)).map
            (homOfLE (n.le_add_right 1)).op).app M
        rw [Functor.ofOpSequence_map_homOfLE_succ]
        ext U x
        change (levelUnitMap I X n M).val.app U x =
          (((step_existsUnique I X n).exists.choose).app M).val.app U
            ((levelUnitMap I X (n + 1) M).val.app U x)
        rw [levelUnitMap_apply, levelUnitMap_apply,
          (step_existsUnique I X n).exists.choose_spec]
        simp only [map_one])
      naturality := by
        intro M N a
        apply NatTrans.ext
        funext n
        ext U x
        change (levelUnitMap I X n.unop N).val.app U (a.val.app U x) =
          ((level I X n.unop).map a).val.app U
            ((levelUnitMap I X n.unop M).val.app U x)
        rw [levelUnitMap_apply, levelUnitMap_apply, tensorSection_map] }
  refine ⟨η, ?_, ?_⟩
  · intro M n U x
    exact levelUnitMap_apply I X n M U x
  · intro η' hη'
    apply NatTrans.ext
    funext M
    apply NatTrans.ext
    funext n
    ext U x
    exact (hη' M n.unop U x).trans (levelUnitMap_apply I X n.unop M U x).symm

/-- The actual ordinary quotient augmentation.
Source: Stacks 06YY (blueprint: lem-sf-cbc-constant-tower-direct-image-normalization). -/
def ordinaryAugmentation (X : Scheme.{u}) :
    (Functor.const ℕᵒᵖ : Modules A X ⥤ Towers A X) ⟶ reductionModule I X :=
  (ordinaryAugmentation_existsUnique I X).exists.choose

attribute [local irreducible] reductionModel

/-- The ordinary augmentation after homotopy localization, with the diagonal
localization factor. Source: Stacks 06YY
(blueprint: lem-sf-cbc-constant-tower-direct-image-normalization). -/
def augmentationHomotopy (X : Scheme.{u}) :
    DerivedCategory.Qh ⋙ delta A X ⟶ reductionHomotopy I X :=
  (Functor.const ℕᵒᵖ : Modules A X ⥤ Towers A X).mapDerivedCategoryFactorsh.hom ≫
    Functor.whiskerRight (NatTrans.mapHomotopyCategory (ordinaryAugmentation I X) (.up ℤ))
      DerivedCategory.Qh

/-- The specified tensor-with-quotient map i_M, constructed by the determining
universal property of derived reduction. Its factorization is the ordinary
x maps to 1 tensor x formula after homotopy localization.
Source: Stacks 06YY (blueprint: lem-sf-cbc-constant-tower-direct-image-normalization). -/
def augmentation (X : Scheme.{u}) : delta A X ⟶ reduction I X :=
  haveI : (reduction I X).IsLeftDerivedFunctor (reductionCounit I X)
      (HomotopyCategory.quasiIso (Modules A X) (.up ℤ)) := (reductionModel I X).universal
  (reduction I X).leftDerivedLift (reductionCounit I X)
    (HomotopyCategory.quasiIso (Modules A X) (.up ℤ)) (delta A X)
    (augmentationHomotopy I X)

namespace OrdinaryComparisonProof
private theorem quotient_pull_comm {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    (constantRingIso A f).hom ≫ quotient I X n =
      (proEtaleSheafInverseImage f CommRingCat.{u + 1}).map (quotient I Y n) ≫
        (constantRingIso (A ⧸ I ^ (n + 1)) f).hom :=
  (proEtaleConstantInverseImageMap_naturality f
    (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1))))).symm

private def extensionPullIso {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    reductionChange Y (quotient I Y n) ⋙
        proEtaleRingModulePullback f
          (coefficients (A ⧸ I ^ (n + 1)) Y) (coefficients (A ⧸ I ^ (n + 1)) X)
          (constantRingIso (A ⧸ I ^ (n + 1)) f) ≅
      modulePullback A f ⋙ reductionChange X (quotient I X n) :=
  ((conjugateIsoEquiv
    ((pbcScalarAdjunction (quotient I Y n)).comp
      (proEtaleRingModuleAdjunction f
        (coefficients (A ⧸ I ^ (n + 1)) Y) (coefficients (A ⧸ I ^ (n + 1)) X)
        (constantRingIso (A ⧸ I ^ (n + 1)) f)))
    ((proEtaleRingModuleAdjunction f (coefficients A Y) (coefficients A X)
      (constantRingIso A f)).comp (pbcScalarAdjunction (quotient I X n)))).symm
    (proEtaleRingRestrictionDirectImage f
      (coefficients A Y) (coefficients (A ⧸ I ^ (n + 1)) Y)
      (coefficients A X) (coefficients (A ⧸ I ^ (n + 1)) X)
      (quotient I Y n) (quotient I X n) (constantRingIso A f)
      (constantRingIso (A ⧸ I ^ (n + 1)) f) (quotient_pull_comm I f n))).symm

private def levelPullIso {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    level I Y n ⋙ modulePullback A f ≅ modulePullback A f ⋙ level I X n := by
  let β := proEtaleRingRestrictionPullbackInv f
    (coefficients A Y) (coefficients (A ⧸ I ^ (n + 1)) Y)
    (coefficients A X) (coefficients (A ⧸ I ^ (n + 1)) X)
    (quotient I Y n) (quotient I X n) (constantRingIso A f)
    (constantRingIso (A ⧸ I ^ (n + 1)) f) (quotient_pull_comm I f n)
  have : IsIso β := proEtaleRingRestrictionPullbackInv_isIso f
    (coefficients A Y) (coefficients (A ⧸ I ^ (n + 1)) Y)
    (coefficients A X) (coefficients (A ⧸ I ^ (n + 1)) X)
    (quotient I Y n) (quotient I X n) (constantRingIso A f)
    (constantRingIso (A ⧸ I ^ (n + 1)) f) (quotient_pull_comm I f n)
  exact Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (reductionChange Y (quotient I Y n)) (asIso β) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (extensionPullIso I f n) (reductionRestrict X (quotient I X n)) ≪≫
    Functor.associator _ _ _

private theorem conjugate_unit {C D : Type*} [Category C] [Category D]
    {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C}
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (d : R₁ ≅ R₂) (M : C) :
    a₁.unit.app M ≫ d.hom.app (L₁.obj M) ≫
      R₂.map (((conjugateIsoEquiv a₁ a₂).symm d).inv.app M) = a₂.unit.app M := by
  have h := unit_conjugateEquiv_symm a₁ a₂ d.hom M
  have hc := congrArg (fun k ↦ k ≫
    R₂.map (((conjugateIsoEquiv a₁ a₂).symm d).inv.app M)) h
  change (a₁.unit.app M ≫ d.hom.app (L₁.obj M)) ≫
      R₂.map (((conjugateIsoEquiv a₁ a₂).symm d).inv.app M) =
    (a₂.unit.app M ≫ R₂.map (((conjugateIsoEquiv a₁ a₂).symm d).hom.app M)) ≫
      R₂.map (((conjugateIsoEquiv a₁ a₂).symm d).inv.app M) at hc
  simp only [Category.assoc, ← R₂.map_comp, Iso.hom_inv_id_app, R₂.map_id] at hc
  exact hc.trans (Category.comp_id _)

attribute [local irreducible] proEtaleRingModulePullback proEtaleRingModuleAdjunction

private theorem extensionPullIso_unit {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    (M : Modules A Y) (U : Y.ProEtᵒᵖ) (x : M.val.obj U) :
    ((extensionPullIso I f n).hom.app M).val.app
      (op ((proEtaleBaseChange f).obj U.unop))
      (((proEtaleRingModuleAdjunction f
        (coefficients (A ⧸ I ^ (n + 1)) Y) (coefficients (A ⧸ I ^ (n + 1)) X)
        (constantRingIso (A ⧸ I ^ (n + 1)) f)).unit.app
        ((reductionChange Y (quotient I Y n)).obj M)).val.app U
          (reductionTensorSection Y (quotient I Y n) M U 1 x)) =
      reductionTensorSection X (quotient I X n) ((modulePullback A f).obj M)
        (op ((proEtaleBaseChange f).obj U.unop)) 1
        (((proEtaleRingModuleAdjunction f (coefficients A Y) (coefficients A X)
          (constantRingIso A f)).unit.app M).val.app U x) := by
  let aR := proEtaleRingModuleAdjunction f (coefficients A Y) (coefficients A X)
    (constantRingIso A f)
  let aS := proEtaleRingModuleAdjunction f
    (coefficients (A ⧸ I ^ (n + 1)) Y) (coefficients (A ⧸ I ^ (n + 1)) X)
    (constantRingIso (A ⧸ I ^ (n + 1)) f)
  let a₁ := (pbcScalarAdjunction (quotient I Y n)).comp aS
  let a₂ := aR.comp (pbcScalarAdjunction (quotient I X n))
  let d := proEtaleRingRestrictionDirectImage f
    (coefficients A Y) (coefficients (A ⧸ I ^ (n + 1)) Y)
    (coefficients A X) (coefficients (A ⧸ I ^ (n + 1)) X)
    (quotient I Y n) (quotient I X n) (constantRingIso A f)
    (constantRingIso (A ⧸ I ^ (n + 1)) f) (quotient_pull_comm I f n)
  have ht := conjugate_unit a₁ a₂ d M
  dsimp only [a₁, a₂] at ht
  rw [Adjunction.comp_unit_app, Adjunction.comp_unit_app] at ht
  have hx := congrArg (fun k ↦ k.val.app U x) ht
  simp only [SheafOfModules.comp_val,
    PresheafOfModules.comp_app, CategoryTheory.comp_apply] at hx
  change ((extensionPullIso I f n).hom.app M).val.app
      (op ((proEtaleBaseChange f).obj U.unop))
      ((d.hom.app _).val.app U
        ((aS.unit.app ((reductionChange Y (quotient I Y n)).obj M)).val.app U
          (((pbcScalarAdjunction (quotient I Y n)).unit.app M).val.app U x))) =
    ((pbcScalarAdjunction (quotient I X n)).unit.app ((modulePullback A f).obj M)).val.app
      (op ((proEtaleBaseChange f).obj U.unop)) ((aR.unit.app M).val.app U x) at hx
  erw [(Classical.choose_spec (proEtaleRingRestrictionDirectImage_existsUnique f
    (coefficients A Y) (coefficients (A ⧸ I ^ (n + 1)) Y)
    (coefficients A X) (coefficients (A ⧸ I ^ (n + 1)) X)
    (quotient I Y n) (quotient I X n) (constantRingIso A f)
    (constantRingIso (A ⧸ I ^ (n + 1)) f) (quotient_pull_comm I f n))).1] at hx
  erw [(pbcScalarAdjunction_exists (quotient I Y n)).exists.choose_spec,
    (pbcScalarAdjunction_exists (quotient I X n)).exists.choose_spec] at hx
  exact hx
private theorem restrictionPullback_unit {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    (N : proEtaleRingModules Y (coefficients (A ⧸ I ^ (n + 1)) Y))
    (U : Y.ProEtᵒᵖ) (z : N.val.obj U) :
    ((proEtaleRingRestrictionPullbackInv f
      (coefficients A Y) (coefficients (A ⧸ I ^ (n + 1)) Y)
      (coefficients A X) (coefficients (A ⧸ I ^ (n + 1)) X)
      (quotient I Y n) (quotient I X n) (constantRingIso A f)
      (constantRingIso (A ⧸ I ^ (n + 1)) f) (quotient_pull_comm I f n)).app N).val.app
        (op ((proEtaleBaseChange f).obj U.unop))
        (((proEtaleRingModuleAdjunction f (coefficients A Y) (coefficients A X)
          (constantRingIso A f)).unit.app
          ((reductionRestrict Y (quotient I Y n)).obj N)).val.app U z) =
      ((proEtaleRingModuleAdjunction f
        (coefficients (A ⧸ I ^ (n + 1)) Y) (coefficients (A ⧸ I ^ (n + 1)) X)
        (constantRingIso (A ⧸ I ^ (n + 1)) f)).unit.app N).val.app U z := by
  let aR := proEtaleRingModuleAdjunction f (coefficients A Y) (coefficients A X)
    (constantRingIso A f)
  let aS := proEtaleRingModuleAdjunction f
    (coefficients (A ⧸ I ^ (n + 1)) Y) (coefficients (A ⧸ I ^ (n + 1)) X)
    (constantRingIso (A ⧸ I ^ (n + 1)) f)
  let d := proEtaleRingRestrictionDirectImage f
    (coefficients A Y) (coefficients (A ⧸ I ^ (n + 1)) Y)
    (coefficients A X) (coefficients (A ⧸ I ^ (n + 1)) X)
    (quotient I Y n) (quotient I X n) (constantRingIso A f)
    (constantRingIso (A ⧸ I ^ (n + 1)) f) (quotient_pull_comm I f n)
  let g := (reductionRestrict Y (quotient I Y n)).map (aS.unit.app N) ≫
    d.hom.app ((proEtaleRingModulePullback f _ _ _).obj N)
  let β := proEtaleRingRestrictionPullbackInv f
    (coefficients A Y) (coefficients (A ⧸ I ^ (n + 1)) Y)
    (coefficients A X) (coefficients (A ⧸ I ^ (n + 1)) X)
    (quotient I Y n) (quotient I X n) (constantRingIso A f)
    (constantRingIso (A ⧸ I ^ (n + 1)) f) (quotient_pull_comm I f n)
  have hβ : β.app N = (aR.homEquiv _ _).symm g := by
    dsimp only [g, β, proEtaleRingRestrictionPullbackInv,
      proEtaleRingRestrictionPullbackApp]
    simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
    rfl
  have ht := (aR.homEquiv _ _).apply_symm_apply g
  rw [← hβ, Adjunction.homEquiv_unit] at ht
  have hx := congrArg (fun k ↦ k.val.app U z) ht
  change ((β.app N).val.app (op ((proEtaleBaseChange f).obj U.unop)))
      ((aR.unit.app _).val.app U z) =
      (d.hom.app _).val.app U ((aS.unit.app N).val.app U z) at hx
  erw [(Classical.choose_spec (proEtaleRingRestrictionDirectImage_existsUnique f
    (coefficients A Y) (coefficients (A ⧸ I ^ (n + 1)) Y)
    (coefficients A X) (coefficients (A ⧸ I ^ (n + 1)) X)
    (quotient I Y n) (quotient I X n) (constantRingIso A f)
    (constantRingIso (A ⧸ I ^ (n + 1)) f) (quotient_pull_comm I f n))).1] at hx
  exact hx

private theorem constant_direct_map {B : Type (u + 1)} [CommRing B]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    proEtaleRingDirectImageMap f (coefficients B Y) (coefficients B X)
      (constantRingIso B f) =
      proEtaleConstantDirectImageMap f CommRingCat.{u + 1} (CommRingCat.of B) := by
  change ((proEtaleSheafAdjunction f CommRingCat.{u + 1}).homEquiv _ _)
    (((proEtaleSheafAdjunction f CommRingCat.{u + 1}).homEquiv _ _).symm
      (proEtaleConstantDirectImageMap f CommRingCat.{u + 1} (CommRingCat.of B))) = _
  exact Equiv.apply_symm_apply _ _

set_option backward.isDefEq.respectTransparency false in
private theorem levelPullIso_formula {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    (M : Modules A Y) (U : Y.ProEtᵒᵖ)
    (s : (coefficients (A ⧸ I ^ (n + 1)) Y).obj.obj U) (x : M.val.obj U) :
    ((levelPullIso I f n).hom.app M).val.app
      (op ((proEtaleBaseChange f).obj U.unop))
      (((proEtaleRingModuleAdjunction f (coefficients A Y) (coefficients A X)
        (constantRingIso A f)).unit.app ((level I Y n).obj M)).val.app U
        (reductionTensorSection Y (quotient I Y n) M U s x)) =
      reductionTensorSection X (quotient I X n) ((modulePullback A f).obj M)
        (op ((proEtaleBaseChange f).obj U.unop))
        ((proEtaleConstantDirectImageMap f CommRingCat.{u + 1}
          (CommRingCat.of (A ⧸ I ^ (n + 1)))).hom.app U s)
        (((proEtaleRingModuleAdjunction f (coefficients A Y) (coefficients A X)
          (constantRingIso A f)).unit.app M).val.app U x) := by
  let V := op ((proEtaleBaseChange f).obj U.unop)
  let aS := proEtaleRingModuleAdjunction f
    (coefficients (A ⧸ I ^ (n + 1)) Y) (coefficients (A ⧸ I ^ (n + 1)) X)
    (constantRingIso (A ⧸ I ^ (n + 1)) f)
  change ((extensionPullIso I f n).hom.app M).val.app V
    (((proEtaleRingRestrictionPullbackInv f
      (coefficients A Y) (coefficients (A ⧸ I ^ (n + 1)) Y)
      (coefficients A X) (coefficients (A ⧸ I ^ (n + 1)) X)
      (quotient I Y n) (quotient I X n) (constantRingIso A f)
      (constantRingIso (A ⧸ I ^ (n + 1)) f) (quotient_pull_comm I f n)).app
        ((reductionChange Y (quotient I Y n)).obj M)).val.app V
        (((proEtaleRingModuleAdjunction f (coefficients A Y) (coefficients A X)
          (constantRingIso A f)).unit.app ((level I Y n).obj M)).val.app U
            (reductionTensorSection Y (quotient I Y n) M U s x))) = _
  dsimp only [V]
  erw [restrictionPullback_unit I f n
    ((reductionChange Y (quotient I Y n)).obj M) U
    (reductionTensorSection Y (quotient I Y n) M U s x)]
  have ht : reductionTensorSection Y (quotient I Y n) M U s x =
      s • reductionTensorSection Y (quotient I Y n) M U 1 x := by
    rw [tensorSection_smul, mul_one]
  rw [ht, map_smul]
  let N := (proEtaleRingModulePullback f
    (coefficients (A ⧸ I ^ (n + 1)) Y) (coefficients (A ⧸ I ^ (n + 1)) X)
    (constantRingIso (A ⧸ I ^ (n + 1)) f)).obj
      ((reductionChange Y (quotient I Y n)).obj M)
  let y : N.val.obj V :=
    (aS.unit.app ((reductionChange Y (quotient I Y n)).obj M)).val.app U
      (reductionTensorSection Y (quotient I Y n) M U 1 x)
  let r : (coefficients (A ⧸ I ^ (n + 1)) X).obj.obj V :=
    (proEtaleRingDirectImageMap f _ _
      (constantRingIso (A ⧸ I ^ (n + 1)) f)).hom.app U s
  change ((extensionPullIso I f n).hom.app M).val.app V (r • y) = _
  rw [map_smul]
  dsimp only [y]
  rw [extensionPullIso_unit]
  rw [tensorSection_smul, mul_one]
  change reductionTensorSection X (quotient I X n) _ _ r _ = _
  congr 1
  exact congrArg (fun q ↦ q.hom.app U s) (constant_direct_map f)

attribute [local irreducible] extensionPullIso levelPullIso

private theorem pull_level_hom_ext {X Y : Scheme.{u}} (f : X ⟶ Y)
    (n : ℕ) (M : Modules A Y) (N : Modules A X)
    (a b : (modulePullback A f).obj ((level I Y n).obj M) ⟶ N)
    (h : ∀ (U : Y.ProEtᵒᵖ)
      (s : (coefficients (A ⧸ I ^ (n + 1)) Y).obj.obj U) (x : M.val.obj U),
      a.val.app (op ((proEtaleBaseChange f).obj U.unop))
        (((proEtaleRingModuleAdjunction f (coefficients A Y) (coefficients A X)
          (constantRingIso A f)).unit.app ((level I Y n).obj M)).val.app U
          (reductionTensorSection Y (quotient I Y n) M U s x)) =
      b.val.app (op ((proEtaleBaseChange f).obj U.unop))
        (((proEtaleRingModuleAdjunction f (coefficients A Y) (coefficients A X)
          (constantRingIso A f)).unit.app ((level I Y n).obj M)).val.app U
          (reductionTensorSection Y (quotient I Y n) M U s x))) : a = b := by
  apply ((proEtaleRingModuleAdjunction f (coefficients A Y) (coefficients A X)
    (constantRingIso A f)).homEquiv _ _).injective
  apply level_hom_ext Y (quotient I Y n) M _
  intro U s x
  exact h U s x

private def stepMap (X : Scheme.{u}) (n : ℕ) : level I X (n + 1) ⟶ level I X n :=
  (step_existsUnique I X n).exists.choose

private theorem stepMap_formula (X : Scheme.{u}) (n : ℕ) (M : Modules A X)
    (U : X.ProEtᵒᵖ) (s : (coefficients (A ⧸ I ^ (n + 2)) X).obj.obj U)
    (x : M.val.obj U) :
    ((stepMap I X n).app M).val.app U
        (reductionTensorSection X (quotient I X (n + 1)) M U s x) =
      reductionTensorSection X (quotient I X n) M U
        ((quotientStep I X n).hom.app U s) x :=
  (step_existsUnique I X n).exists.choose_spec M U s x

private theorem quotientStep_direct {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    quotientStep I Y n ≫ proEtaleConstantDirectImageMap f CommRingCat.{u + 1}
      (CommRingCat.of (A ⧸ I ^ (n + 1))) =
    proEtaleConstantDirectImageMap f CommRingCat.{u + 1}
      (CommRingCat.of (A ⧸ I ^ (n + 2))) ≫
      (proEtaleSheafDirectImage f CommRingCat.{u + 1}).map (quotientStep I X n) := by
  rw [← constant_direct_map, ← constant_direct_map]
  apply restrictionDirectImageMap_square
  exact (proEtaleConstantInverseImageMap_naturality f
    (CommRingCat.ofHom (Ideal.Quotient.factorPow I (Nat.le_succ (n + 1))))).symm

set_option backward.isDefEq.respectTransparency false in
private theorem levelPullIso_step {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    (M : Modules A Y) :
    (modulePullback A f).map ((stepMap I Y n).app M) ≫
        (levelPullIso I f n).hom.app M =
      (levelPullIso I f (n + 1)).hom.app M ≫
        (stepMap I X n).app ((modulePullback A f).obj M) := by
  apply pull_level_hom_ext I f (n + 1) M _
  intro U s x
  let a := proEtaleRingModuleAdjunction f (coefficients A Y) (coefficients A X)
    (constantRingIso A f)
  have hu := congrArg (fun k ↦ k.val.app U
      (reductionTensorSection Y (quotient I Y (n + 1)) M U s x))
    (a.unit_naturality ((stepMap I Y n).app M)).symm
  change (a.unit.app ((level I Y n).obj M)).val.app U
      (((stepMap I Y n).app M).val.app U
        (reductionTensorSection Y (quotient I Y (n + 1)) M U s x)) =
    ((modulePullback A f).map ((stepMap I Y n).app M)).val.app
      (op ((proEtaleBaseChange f).obj U.unop))
      ((a.unit.app ((level I Y (n + 1)).obj M)).val.app U
        (reductionTensorSection Y (quotient I Y (n + 1)) M U s x)) at hu
  change ((levelPullIso I f n).hom.app M).val.app _
      (((modulePullback A f).map ((stepMap I Y n).app M)).val.app _
        ((a.unit.app ((level I Y (n + 1)).obj M)).val.app U
          (reductionTensorSection Y (quotient I Y (n + 1)) M U s x))) =
    ((stepMap I X n).app ((modulePullback A f).obj M)).val.app _
      (((levelPullIso I f (n + 1)).hom.app M).val.app _
        ((a.unit.app ((level I Y (n + 1)).obj M)).val.app U
          (reductionTensorSection Y (quotient I Y (n + 1)) M U s x)))
  let V := op ((proEtaleBaseChange f).obj U.unop)
  have hl₁ := congrArg (((levelPullIso I f n).hom.app M).val.app V) hu.symm
  have hl₂ := congrArg (fun z : ((level I Y n).obj M).val.obj U ↦
      ((levelPullIso I f n).hom.app M).val.app V
        ((a.unit.app ((level I Y n).obj M)).val.app U z))
    (stepMap_formula I Y n M U s x)
  have hl₃ := levelPullIso_formula I f n M U ((quotientStep I Y n).hom.app U s) x
  have hr₁ := congrArg
    (((stepMap I X n).app ((modulePullback A f).obj M)).val.app V)
    (levelPullIso_formula I f (n + 1) M U s x)
  have hr₂ := stepMap_formula I X n ((modulePullback A f).obj M) V
    ((proEtaleConstantDirectImageMap f CommRingCat.{u + 1}
      (CommRingCat.of (A ⧸ I ^ (n + 2)))).hom.app U s)
    ((a.unit.app M).val.app U x)
  have hc := congrArg (fun q ↦ q.hom.app U s) (quotientStep_direct I f n)
  have hm := congrArg (fun t ↦ reductionTensorSection X (quotient I X n)
    ((modulePullback A f).obj M) V t ((a.unit.app M).val.app U x)) hc
  exact (hl₁.trans (hl₂.trans hl₃)).trans (hm.trans (hr₁.trans hr₂).symm)


private theorem reductionModule_step (X : Scheme.{u}) (M : Modules A X) (n : ℕ) :
    ((reductionModule I X).obj M).map (homOfLE (Nat.le_add_right n 1)).op =
      (stepMap I X n).app M := by
  change ((Functor.ofOpSequence (fun n ↦ (stepMap I X n))).map
    (homOfLE (Nat.le_add_right n 1)).op).app M = _
  rw [Functor.ofOpSequence_map_homOfLE_succ]

private def comparisonApp {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Modules A Y) :
    (towerPullback A f).obj ((reductionModule I Y).obj M) ⟶
      (reductionModule I X).obj ((modulePullback A f).obj M) :=
  NatTrans.ofOpSequence (fun n ↦ (levelPullIso I f n).hom.app M) (by
    intro n
    change (modulePullback A f).map
        (((reductionModule I Y).obj M).map (homOfLE (Nat.le_add_right n 1)).op) ≫
        (levelPullIso I f n).hom.app M =
      (levelPullIso I f (n + 1)).hom.app M ≫
        ((reductionModule I X).obj ((modulePullback A f).obj M)).map
          (homOfLE (Nat.le_add_right n 1)).op
    rw [reductionModule_step, reductionModule_step]
    exact levelPullIso_step I f n M)

private def ordinaryComparisonIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    reductionModule I Y ⋙ towerPullback A f ≅
      modulePullback A f ⋙ reductionModule I X := by
  let σ : reductionModule I Y ⋙ towerPullback A f ⟶
      modulePullback A f ⋙ reductionModule I X :=
    { app := comparisonApp I f
      naturality := by
        intro M N g
        apply NatTrans.ext
        funext n
        exact (levelPullIso I f n.unop).hom.naturality g }
  have (M : Modules A Y) : IsIso (σ.app M) := by
    have (n : ℕᵒᵖ) : IsIso ((σ.app M).app n) := by
      change IsIso ((levelPullIso I f n.unop).hom.app M)
      infer_instance
    exact NatIso.isIso_of_isIso_app _
  have : IsIso σ := NatIso.isIso_of_isIso_app _
  exact asIso σ

end OrdinaryComparisonProof

/-- Ordinary tensor/pullback comparison on the entire strict quotient tower.
Its formula is imposed on all inverse-image generators, not only constant sections.
Source: Stacks 07A4, 03EL
(blueprint: lem-sf-cbc-constant-tower-direct-image-normalization).
Proof: pullback of each constant quotient ring is its canonical constant sheaf.
The scalar square commutes on constants and therefore on the sheafifications.
Tensor balancing sends the inverse image of s tensor x to the inverse image of s
 tensored with the inverse image of x. The reverse reassociation is inverse.
The quotient transition formulas make these maps a strict diagram isomorphism.
Local generation of inverse-image sections and sheafification prove uniqueness. -/
theorem ordinaryReductionPull_existsUnique {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ∃! σ : reductionModule I Y ⋙ towerPullback A f ≅
        modulePullback A f ⋙ reductionModule I X,
      ∀ (M : Modules A Y) (n : ℕ) (U : Y.ProEt)
        (s : (coefficients (A ⧸ I ^ (n + 1)) Y).obj.obj (op U))
        (x : M.val.obj (op U)),
        ((σ.hom.app M).app (op n)).val.app (op ((proEtaleBaseChange f).obj U))
            (((proEtaleRingModuleAdjunction f (coefficients A Y) (coefficients A X)
              (constantRingIso A f)).unit.app ((level I Y n).obj M)).val.app (op U)
                (reductionTensorSection Y (quotient I Y n) M (op U) s x)) =
          reductionTensorSection X (quotient I X n) ((modulePullback A f).obj M)
            (op ((proEtaleBaseChange f).obj U))
            ((proEtaleConstantDirectImageMap f CommRingCat.{u + 1}
              (CommRingCat.of (A ⧸ I ^ (n + 1)))).hom.app (op U) s)
            (((proEtaleRingModuleAdjunction f (coefficients A Y) (coefficients A X)
              (constantRingIso A f)).unit.app M).val.app (op U) x) := by
  open OrdinaryComparisonProof in
    refine ⟨ordinaryComparisonIso I f, ?_, ?_⟩
    · intro M n U s x
      exact levelPullIso_formula I f n M (op U) s x
    · intro σ hσ
      apply Iso.ext
      apply NatTrans.ext
      funext M
      apply NatTrans.ext
      funext n
      apply pull_level_hom_ext I f n.unop M _
      intro U s x
      exact (hσ M n.unop U.unop s x).trans
        (levelPullIso_formula I f n.unop M U s x).symm
  
/-- The normalized ordinary comparison, retaining its strict transition maps.
Source: Stacks 07A4 (blueprint: lem-sf-cbc-constant-tower-direct-image-normalization). -/
def ordinaryReductionPull {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  (ordinaryReductionPull_existsUnique I f).exists.choose

namespace DerivedComparisonConcrete
set_option backward.isDefEq.respectTransparency false in
private theorem pull_kflat {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (S : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (c₀ : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R ≅ S)
    (P : CochainComplex (proEtaleRingModules Y R) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (R := R) P)
    (hflat : ∀ i : ℤ, SheafOfModules.IsFlatOnSite
      (J := ProEt.topology Y) (R := R) (P.X i)) :
    CochainComplex.IsKFlatIndependentCoefficients (R := S)
      (((proEtaleRingModulePullback f R S c₀).mapHomologicalComplex (.up ℤ)).obj P) := by
  obtain ⟨J, hJ⟩ := proEtaleAlgebraicInverseImage_exists f (R)
  have : PreservesFiniteLimits (proEtaleSheafInverseImage f (Type (u + 1))) :=
    (AlgebraicGeometry.ProEtale.toposFunctorialityInverseImage f (𝟙 Y)).2.2.2.1
  let C := proEtaleRingModules Y R
  let D := proEtaleRingModules X
    ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj (R))
  let c := c₀.hom
  have hmap' (F : C ⥤ D) (h : J.modules = F) {M N : C} (g : M ⟶ N) :
      SheafOfModules.changeOfRingsHom.{u, u + 1, u + 1} c (F.obj M) (F.map g) =
        eqToHom (congrArg (fun G : C ⥤ D ↦
          SheafOfModules.changeOfRings.{u, u + 1, u + 1} c (G.obj M)) h.symm) ≫
        SheafOfModules.changeOfRingsHom.{u, u + 1, u + 1}
          c (J.modules.obj M) (J.modules.map g) ≫
        eqToHom (congrArg (fun G : C ⥤ D ↦
          SheafOfModules.changeOfRings.{u, u + 1, u + 1} c (G.obj N)) h.symm).symm := by
    subst F
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  exact (SheafOfModules.isKFlat_ringedToposPullback
    (proEtaleSheafInverseImage f (Type (u + 1)))
    (proEtaleSheafDirectImage f (Type (u + 1)))
    (proEtaleSheafAdjunction f (Type (u + 1))) J c (proEtaleRingModulePullback f R S c₀)
    (fun M ↦ congrArg (fun F : C ⥤ D ↦
      SheafOfModules.changeOfRings.{u, u + 1, u + 1} c (F.obj M)) hJ.symm)
    (fun {M N} g ↦ hmap' _ hJ g) P hP hflat).1

private theorem exists_pull_kflat_resolution {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : CochainComplex (Modules A Y) ℤ) :
    ∃ (P : CochainComplex (Modules A Y) ℤ) (s : P ⟶ K),
      CochainComplex.IsKFlatIndependentCoefficients (R := coefficients A Y) P ∧
      CochainComplex.IsKFlatIndependentCoefficients (R := coefficients A X)
        (((modulePullback A f).mapHomologicalComplex (.up ℤ)).obj P) ∧ QuasiIso s := by
  obtain ⟨P, s, hP, hf, hs, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients (R := coefficients A Y) K
  have hf' (i : ℤ) : SheafOfModules.IsFlatOnSite
      (J := ProEt.topology Y) (R := coefficients A Y) (P.X i) :=
    (exactFunctor _ _).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso (coefficients A Y) (P.X i)).symm (hf i)
  exact ⟨P, s, hP,
    pull_kflat f (coefficients A Y) (coefficients A X) (constantRingIso A f) P hP hf', hs⟩

private theorem reductionComparison_existsUnique {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ∃! τ : reduction I Y ⋙ G A f ≅ pull A f ⋙ reduction I X,
      ∀ P : CochainComplex (Modules A Y) ℤ,
        CochainComplex.IsKFlatIndependentCoefficients (R := coefficients A Y) P →
        IsReductionPullAt (reductionModule I Y) (reductionModule I X)
          (modulePullback A f) (towerPullback A f) (reduction I Y) (reduction I X)
          (reductionCounit I Y) (reductionCounit I X) (ordinaryReductionPull I f) τ
          ((HomotopyCategory.quotient _ (.up ℤ)).obj P) := by
  obtain ⟨d⟩ := DerivedComparisonProof.model_square_exists_complexes
    (modulePullback A f) (towerPullback A f) (reductionModule I Y) (reductionModule I X)
    (CochainComplex.IsKFlatIndependentCoefficients (R := coefficients A Y))
    (CochainComplex.IsKFlatIndependentCoefficients (R := coefficients A X))
    (reductionModel I Y) (reductionModel I X) (ordinaryReductionPull I f)
    (fun K ↦ by
      obtain ⟨P, s, hP, hFP, hs⟩ := exists_pull_kflat_resolution f K
      exact ⟨P, s, ⟨hP, hFP⟩, hs⟩)
  refine ⟨d.iso, ?_, ?_⟩
  · intro P _
    exact d.normalized _
  · intro τ' hτ'
    apply d.unique τ'
    intro P hP
    exact hτ' P hP.1

end DerivedComparisonConcrete

/-- Derived tensor/pullback comparison characterized on K-flat representatives.
Source: Stacks 06YS, 07A4
(blueprint: lem-sf-cbc-constant-tower-direct-image-normalization).
Proof: a flat-term K-flat model P remains K-flat with flat terms after exact
constant-coefficient inverse image. The reduction counits are invertible there.
Conjugate the ordinary strict comparison by these counits and the localization
factors. This descends through chain maps, homotopies and resolving
quasi-isomorphisms. Every object has such a model, proving uniqueness. -/
theorem reductionPull_existsUnique {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ∃! τ : reduction I Y ⋙ G A f ≅ pull A f ⋙ reduction I X,
      ∀ P : CochainComplex (Modules A Y) ℤ,
        CochainComplex.IsKFlatIndependentCoefficients (R := coefficients A Y) P →
        IsReductionPullAt (reductionModule I Y) (reductionModule I X)
          (modulePullback A f) (towerPullback A f) (reduction I Y) (reduction I X)
          (reductionCounit I Y) (reductionCounit I X) (ordinaryReductionPull I f) τ
          ((HomotopyCategory.quotient _ (.up ℤ)).obj P) := by
  exact DerivedComparisonConcrete.reductionComparison_existsUnique I f

/-- The canonical whole-tower tensor/pullback comparison.
Source: Stacks 07A4 (blueprint: lem-sf-cbc-constant-tower-direct-image-normalization). -/
def reductionPull {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  (reductionPull_existsUnique I f).exists.choose

/-- The projection map h, defined by its counit-tensor adjunction mate. The comparison
being transposed is the canonical tensor balancing map on the full quotient diagram.
Its source therefore includes precisely the diagonal identification chi.
Source: Stacks 0B56 (blueprint: lem-sf-cbc-constant-tower-direct-image-normalization). -/
def projection {X Y : Scheme.{u}} (f : X ⟶ Y) :
    push A f ⋙ reduction I Y ⟶ reduction I X ⋙ R A f :=
  mateEquiv
    (proEtaleRingDerivedAdjunction f (coefficients A Y) (coefficients A X)
      (constantRingIso A f)) (adj A f) (reductionPull I f).hom


end CoefficientConstructions

attribute [local irreducible] proEtaleRingModulePullback proEtaleRingModuleAdjunction

namespace Proofs
section ConcreteMates
variable (A : Type (u + 1)) [CommRing A]
set_option backward.isDefEq.respectTransparency false in
private theorem constant_mate {C D : Type*} [Category C] [Category D]
    {L : C ⥤ D} {F : D ⥤ C} (a : L ⊣ F) (J : Type*) [Category J] :
    (mateEquiv a (a.whiskerRight J)
      (TwoSquare.mk _ _ _ _ (Functor.compConstIso J L).inv)).natTrans =
        (Functor.compConstIso J F).hom := by
  apply NatTrans.ext
  funext M
  apply NatTrans.ext
  funext n
  simp [mateEquiv_apply, TwoSquare.mk, Adjunction.whiskerRight, Functor.compConstIso]

set_option backward.isDefEq.respectTransparency false in
private theorem chi_mate {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (chi A f).hom =
      (mateEquiv
        (proEtaleRingDerivedAdjunction f (coefficients A Y) (coefficients A X)
          (constantRingIso A f)) (adj A f)
        (TwoSquare.mk _ _ _ _ (deltaPull A f).hom)).natTrans := by
  exact derivedSquare_mate (V := modulePullback A f) (W := towerPullback A f)
    (moduleDirectImage A f) (Functor.const ℕᵒᵖ)
    (Functor.const ℕᵒᵖ) (towerDirectImage A f)
    (Functor.compConstIso ℕᵒᵖ (moduleDirectImage A f))
    (proEtaleRingModuleAdjunction f (coefficients A Y) (coefficients A X)
      (constantRingIso A f))
    ((proEtaleRingModuleAdjunction f (coefficients A Y) (coefficients A X)
      (constantRingIso A f)).whiskerRight ℕᵒᵖ)
    (Functor.compConstIso ℕᵒᵖ (modulePullback A f)).symm (constant_mate
      (proEtaleRingModuleAdjunction f (coefficients A Y) (coefficients A X)
        (constantRingIso A f)) ℕᵒᵖ)

private theorem chi_normalized {X Y : Scheme.{u}} (f : X ⟶ Y) :
    IsDirectImageNormalizedOnKInjectives (moduleDirectImage A f)
      (Functor.const ℕᵒᵖ : Modules A X ⥤ Towers A X)
      (Functor.const ℕᵒᵖ : Modules A Y ⥤ Towers A Y) (towerDirectImage A f)
      (Functor.compConstIso ℕᵒᵖ (moduleDirectImage A f)) (chi A f) :=
  derivedSquare_normalized (moduleDirectImage A f)
    (Functor.const ℕᵒᵖ) (Functor.const ℕᵒᵖ) (towerDirectImage A f)
    (Functor.compConstIso ℕᵒᵖ (moduleDirectImage A f))

end ConcreteMates
namespace EvalTest
universe ue ve we
variable {C D T U : Type ue} [Category.{ve} C] [Category.{ve} D]
  [Category.{ve} T] [Category.{ve} U] [Abelian C] [Abelian D] [Abelian T] [Abelian U]
  [HasDerivedCategory.{we} C] [HasDerivedCategory.{we} D]
  [HasDerivedCategory.{we} T] [HasDerivedCategory.{we} U]
  (F : C ⥤ D) (H : T ⥤ U) (P : C ⥤ T) (Q : D ⥤ U)
  [F.Additive] [H.Additive] [P.Additive] [Q.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits H] [PreservesFiniteColimits H]
  [PreservesFiniteLimits P] [PreservesFiniteColimits P]
  [PreservesFiniteLimits Q] [PreservesFiniteColimits Q]
private theorem square_fac (e : P ⋙ H ≅ F ⋙ Q) (K : HomotopyCategory C (.up ℤ)) :
    (Functor.mapDerivedCategorySquareIso e).hom.app (DerivedCategory.Qh.obj K) ≫
      Q.mapDerivedCategory.map (F.mapDerivedCategoryFactorsh.hom.app K) ≫
        Q.mapDerivedCategoryFactorsh.hom.app ((F.mapHomotopyCategory (.up ℤ)).obj K) =
      H.mapDerivedCategory.map (P.mapDerivedCategoryFactorsh.hom.app K) ≫
        H.mapDerivedCategoryFactorsh.hom.app ((P.mapHomotopyCategory (.up ℤ)).obj K) ≫
          DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory e.hom (.up ℤ)).app K) := by
  simp only [Functor.mapDerivedCategorySquareIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Category.assoc]
  rw [Functor.mapDerivedCategoryCompIso_hom_app_factorsh,
    Functor.mapDerivedCategoryNatIso_fach,
    ← Functor.mapDerivedCategoryCompIso_hom_app_factorsh]
  simp only [Category.assoc]
  erw [Iso.inv_hom_id_app_assoc]

private def collapse {C T : Type ue} [Category.{ve} C] [Category.{ve} T]
    [Abelian C] [Abelian T] [HasDerivedCategory.{we} C] [HasDerivedCategory.{we} T]
    {P : C ⥤ T} {E : T ⥤ C} [P.Additive] [E.Additive]
    [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    [PreservesFiniteLimits E] [PreservesFiniteColimits E] (c : P ⋙ E ≅ 𝟭 C) :
    P.mapDerivedCategory ⋙ E.mapDerivedCategory ≅ 𝟭 _ :=
  (Functor.mapDerivedCategoryCompIso P E).symm ≪≫
    Functor.mapDerivedCategoryNatIso c ≪≫ Functor.mapDerivedCategoryIdIso C

private theorem collapse_fac {C T : Type ue} [Category.{ve} C] [Category.{ve} T]
    [Abelian C] [Abelian T] [HasDerivedCategory.{we} C] [HasDerivedCategory.{we} T]
    {P : C ⥤ T} {E : T ⥤ C} [P.Additive] [E.Additive]
    [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    [PreservesFiniteLimits E] [PreservesFiniteColimits E] (c : P ⋙ E ≅ 𝟭 C)
    (K : HomotopyCategory C (.up ℤ)) :
    (collapse c).hom.app (DerivedCategory.Qh.obj K) =
      E.mapDerivedCategory.map (P.mapDerivedCategoryFactorsh.hom.app K) ≫
        E.mapDerivedCategoryFactorsh.hom.app ((P.mapHomotopyCategory (.up ℤ)).obj K) ≫
          DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory c.hom (.up ℤ)).app K) := by
  simp only [collapse, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app]
  rw [Functor.mapDerivedCategoryIdIso_hom_app_Qh_obj,
    Functor.mapDerivedCategoryNatIso_fach,
    ← Functor.mapDerivedCategoryCompIso_hom_app_factorsh]
  simp only [Category.assoc]
  erw [Iso.inv_hom_id_app_assoc]

variable (EY : T ⥤ C) (EX : U ⥤ D) [EY.Additive] [EX.Additive]
  [PreservesFiniteLimits EY] [PreservesFiniteColimits EY]
  [PreservesFiniteLimits EX] [PreservesFiniteColimits EX]
  (s : P ⋙ H ≅ F ⋙ Q) (t : EY ⋙ F ≅ H ⋙ EX)
  (cy : P ⋙ EY ≅ 𝟭 C) (cx : Q ⋙ EX ≅ 𝟭 D)
  (h : ∀ M, t.hom.app (P.obj M) ≫ EX.map (s.hom.app M) ≫ cx.hom.app (F.obj M) =
    F.map (cy.hom.app M))

include h in
private theorem exact_evaluation (M : DerivedCategory C) :
    (Functor.mapDerivedCategorySquareIso t).hom.app (P.mapDerivedCategory.obj M) ≫
      EX.mapDerivedCategory.map ((Functor.mapDerivedCategorySquareIso s).hom.app M) ≫
        (collapse cx).hom.app (F.mapDerivedCategory.obj M) =
      F.mapDerivedCategory.map ((collapse cy).hom.app M) := by
  suffices he : Functor.whiskerLeft P.mapDerivedCategory
      (Functor.mapDerivedCategorySquareIso t).hom ≫
      Functor.whiskerRight (Functor.mapDerivedCategorySquareIso s).hom EX.mapDerivedCategory ≫
      Functor.whiskerLeft F.mapDerivedCategory (collapse cx).hom =
    Functor.whiskerRight (collapse cy).hom F.mapDerivedCategory from congr_app he M
  refine Localization.natTrans_ext DerivedCategory.Qh (HomotopyCategory.quasiIso C (.up ℤ))
    (fun K ↦ ?_)
  obtain ⟨J, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
  let K := (HomotopyCategory.quotient C (.up ℤ)).obj J
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
  apply (cancel_mono (F.mapDerivedCategoryFactorsh.hom.app K)).1
  simp only [Category.assoc]
  erw [← (collapse cx).hom.naturality]
  dsimp only [Functor.comp_obj, Functor.comp_map, Functor.id_map]
  rw [collapse_fac]
  erw [← EX.mapDerivedCategory.map_comp_assoc, ← EX.mapDerivedCategory.map_comp_assoc]
  have hs := congrArg EX.mapDerivedCategory.map (square_fac F H P Q s K)
  rw [← Category.assoc] at hs
  erw [hs]
  simp only [EX.mapDerivedCategory.map_comp, Category.assoc]
  erw [← (Functor.mapDerivedCategorySquareIso t).hom.naturality_assoc]
  dsimp only [Functor.comp_obj, Functor.comp_map]
  erw [EX.mapDerivedCategoryFactorsh.hom.naturality_assoc]
  erw [reassoc_of% square_fac H F EY EX t ((P.mapHomotopyCategory (.up ℤ)).obj K)]
  rw [collapse_fac]
  simp only [F.mapDerivedCategory.map_comp, Category.assoc]
  erw [F.mapDerivedCategoryFactorsh.hom.naturality]
  dsimp only [Functor.comp_map]
  congr 3
  rw [← DerivedCategory.Qh.map_comp, ← DerivedCategory.Qh.map_comp]
  congr 1
  change (HomotopyCategory.quotient D (.up ℤ)).map _ ≫
      (HomotopyCategory.quotient D (.up ℤ)).map _ ≫
        (HomotopyCategory.quotient D (.up ℤ)).map _ =
    (HomotopyCategory.quotient D (.up ℤ)).map _
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1
  ext i
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
    NatTrans.mapHomologicalComplex_app_f]
  exact h (J.X i)
end EvalTest

namespace NormalizationTest
variable {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
  {P : A ⥤ B} {F : B ⥤ A} {G : C ⥤ D} {H : D ⥤ C}
  {DY RY : A ⥤ C} {DX RX : B ⥤ D}
  (a : P ⊣ F) (b : G ⊣ H)
  (s : DY ⋙ G ⟶ P ⋙ DX) (t : RY ⋙ G ⟶ P ⋙ RX)
  (eY : DY ⟶ RY) (eX : DX ⟶ RX)
  (h : ∀ N, s.app N ≫ eX.app (P.obj N) = G.map (eY.app N) ≫ t.app N)
include h in
private theorem mate_naturality (M : B) :
    eY.app (F.obj M) ≫ (mateEquiv a b (TwoSquare.mk _ _ _ _ t)).app M =
      (mateEquiv a b (TwoSquare.mk _ _ _ _ s)).app M ≫ H.map (eX.app M) := by
  simp only [mateEquiv_apply, TwoSquare.mk, NatTrans.comp_app, Functor.comp_obj,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.rightUnitor_inv_app, Functor.leftUnitor_hom_app,
    Category.id_comp, Category.assoc]
  dsimp only [TwoSquare.natTrans, Functor.comp_obj, Functor.comp_map, Functor.id_obj]
  erw [Category.comp_id, Category.id_comp]
  change eY.app (F.obj M) ≫ b.unit.app (RY.obj (F.obj M)) ≫
      H.map (t.app (F.obj M)) ≫ H.map (RX.map (a.counit.app M)) =
    b.unit.app (DY.obj (F.obj M)) ≫ H.map (s.app (F.obj M)) ≫
      H.map (DX.map (a.counit.app M)) ≫ H.map (eX.app M)
  rw [← b.unit_naturality_assoc]
  rw [← H.map_comp_assoc, ← h]
  simp only [H.map_comp, Category.assoc]
  simp only [← H.map_comp]
  congr 2
  exact congrArg (fun k ↦ s.app (F.obj M) ≫ k) (eX.naturality (a.counit.app M)).symm
end NormalizationTest

namespace EvalTest
open CategoryTheory CategoryTheory.TwoSquare
variable {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
  {P : A ⥤ B} {F : B ⥤ A} {G : C ⥤ D} {H : D ⥤ C}
  {DY : A ⥤ C} {DX : B ⥤ D} {EY : C ⥤ A} {EX : D ⥤ B}
  (a : P ⊣ F) (b : G ⊣ H)
  (s : DY ⋙ G ⟶ P ⋙ DX) (t : EY ⋙ P ⟶ G ⋙ EX)
  (eY : DY ⋙ EY ⟶ 𝟭 A) (eX : DX ⋙ EX ⟶ 𝟭 B)
  (h : ∀ N, t.app (DY.obj N) ≫ EX.map (s.app N) ≫ eX.app (P.obj N) = P.map (eY.app N))
include h in
private theorem eval_mate (M : B) :
    EY.map ((mateEquiv a b (TwoSquare.mk _ _ _ _ s)).app M) ≫
      (mateEquiv b a (TwoSquare.mk _ _ _ _ t)).app (DX.obj M) ≫
        F.map (eX.app M) = eY.app (F.obj M) := by
  let α := TwoSquare.mk _ _ _ _ s
  let β := TwoSquare.mk _ _ _ _ t
  have hc := mateEquiv_vcomp a b a α β
  let idSquare : (𝟭 A) ⋙ P ⟶ P ⋙ (𝟭 B) := P.leftUnitor.hom ≫ P.rightUnitor.inv
  have hn := NormalizationTest.mate_naturality a a (α ≫ₕ β).natTrans
    idSquare eY eX (by
      intro N
      simpa [α, β, TwoSquare.hComp, idSquare] using h N) M
  have hm : (mateEquiv a a (TwoSquare.mk _ _ _ _ idSquare)).app M = 𝟙 _ := by
    simp [mateEquiv_apply, TwoSquare.mk, idSquare, a.right_triangle_components]
  rw [hm] at hn
  erw [Category.comp_id] at hn
  have hca := congrArg (fun z ↦ z.app M) hc
  change eY.app (F.obj M) =
    (mateEquiv a a (α ≫ₕ β)).app M ≫ F.map (eX.app M) at hn
  erw [hca] at hn
  simpa [TwoSquare.vComp, α, β] using hn.symm
end EvalTest

section Evaluation

open AlgebraicGeometry AlgebraicGeometry.Scheme Opposite
open AlgebraicGeometry.ProEtale.StrictTower
open AlgebraicGeometry.ProEtale.StrictTower.ConstantNormalization
variable (A : Type (u + 1)) [CommRing A]
set_option backward.isDefEq.respectTransparency false in
private theorem evaluation_normalized {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : DerivedCategory (Modules A X)) (n : ℕ) :
    (ev A Y n).map ((chi A f).hom.app M) ≫
        (evalR A f n).app ((delta A X).obj M) ≫
        (push A f).map ((deltaEval A X n).hom.app M) =
      (deltaEval A Y n).hom.app ((push A f).obj M) := by
  let F := modulePullback A f
  let H := towerPullback A f
  let P := (Functor.const ℕᵒᵖ : Modules A Y ⥤ Towers A Y)
  let Q := (Functor.const ℕᵒᵖ : Modules A X ⥤ Towers A X)
  let EY := (evaluation ℕᵒᵖ (Modules A Y)).obj (op n)
  let EX := (evaluation ℕᵒᵖ (Modules A X)).obj (op n)
  let s := (Functor.compConstIso ℕᵒᵖ F).symm
  let t := (eqToIso (evaluationPullback A f n)).symm
  let cy := Functor.constCompEvaluationObj (D := Modules A Y) (op n)
  let cx := Functor.constCompEvaluationObj (D := Modules A X) (op n)
  have ht : (Functor.mapDerivedCategorySquareIso t).hom = (evalG A f n).inv := by
    dsimp only [t, evalG]
    simp only [Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
      Functor.mapDerivedCategoryNatIso_symm, Category.assoc]
  have he (N : DerivedCategory (Modules A Y)) :
      (evalG A f n).inv.app ((delta A Y).obj N) ≫
        (ev A X n).map ((deltaPull A f).hom.app N) ≫
          (deltaEval A X n).hom.app ((pull A f).obj N) =
        (pull A f).map ((deltaEval A Y n).hom.app N) := by
    rw [← ht]
    exact EvalTest.exact_evaluation F H P Q EY EX s t cy cx (by
      intro N
      change (𝟙 (F.obj N)) ≫ 𝟙 _ ≫ 𝟙 _ = F.map (𝟙 N)
      simp only [Category.id_comp, F.map_id]) N
  have hm := EvalTest.eval_mate
    (proEtaleRingDerivedAdjunction f (coefficients A Y) (coefficients A X)
      (constantRingIso A f)) (adj A f) (deltaPull A f).hom (evalG A f n).inv
    (deltaEval A Y n).hom (deltaEval A X n).hom he M
  rw [chi_mate A f]
  exact hm

end Evaluation
namespace LimitTest
variable {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
  {P : A ⥤ B} {F : B ⥤ A} {G : C ⥤ D} {H : D ⥤ C}
  {DX : B ⥤ D} {LX : D ⥤ B} {DY : A ⥤ C} {LY : C ⥤ A}
  (a : P ⊣ F) (b : G ⊣ H) (c : DY ⊣ LY) (d : DX ⊣ LX)
  (s : DY ⋙ G ≅ P ⋙ DX) (χ : F ⋙ DY ≅ DX ⋙ H)
  (hχ : (mateEquiv a b (TwoSquare.mk _ _ _ _ s.hom)).natTrans = χ.hom)

include hχ in
private theorem limit_mate_unit (M : B) :
    F.map (d.unit.app M) ≫
      (conjugateIsoEquiv (a.comp d) (c.comp b) s).hom.app (DX.obj M) =
    c.unit.app (F.obj M) ≫ LY.map (χ.hom.app M) := by
  have hh := iterated_mateEquiv_conjugateEquiv a b c d (TwoSquare.mk _ _ _ _ s.hom)
  have h := unit_mateEquiv d c (TwoSquare.mk _ _ _ _ χ.hom) M
  have hs : (mateEquiv d c (TwoSquare.mk _ _ _ _ χ.hom)).natTrans =
      (conjugateIsoEquiv (a.comp d) (c.comp b) s).hom := by
    rw [← hχ]
    exact hh
  change F.map (d.unit.app M) ≫
      (mateEquiv d c (TwoSquare.mk _ _ _ _ χ.hom)).natTrans.app (DX.obj M) = _ at h
  rw [hs] at h
  exact h

end LimitTest
section Limit

open AlgebraicGeometry AlgebraicGeometry.Scheme Opposite
open AlgebraicGeometry.ProEtale.StrictTower
open AlgebraicGeometry.ProEtale.StrictTower.ConstantNormalization
variable (A : Type (u + 1)) [CommRing A]
set_option backward.isDefEq.respectTransparency false in
private theorem limit_normalized_concrete {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : DerivedCategory (Modules A X)) :
    (push A f).map ((deltaLimit A X).inv.app M) ≫
        (limitPush A f).hom.app ((delta A X).obj M) ≫
        (L A Y).map ((chi A f).inv.app M) ≫
        (deltaLimit A Y).hom.app ((push A f).obj M) = 𝟙 _ := by
  have h : (push A f).map ((deltaLimit A X).inv.app M) ≫
      (limitPush A f).hom.app ((delta A X).obj M) =
    (deltaLimit A Y).inv.app ((push A f).obj M) ≫ (L A Y).map ((chi A f).hom.app M) := by
    dsimp only [limitPush, deltaLimit, Iso.symm_inv, asIso_hom]
    have ht := LimitTest.limit_mate_unit
        (F := push A f) (P := pull A f) (G := G A f) (H := R A f)
        (DY := delta A Y) (DX := delta A X) (LY := L A Y) (LX := L A X)
        (proEtaleRingDerivedAdjunction f (coefficients A Y) (coefficients A X)
          (constantRingIso A f)) (adj A f) (deltaAdj A Y) (deltaAdj A X)
        (deltaPull A f) (chi A f) (chi_mate A f).symm M
    convert ht using 3
    congr 1
  rw [reassoc_of% h]
  rw [← (L A Y).map_comp_assoc, Iso.hom_inv_id_app]
  erw [(L A Y).map_id, Category.id_comp]
  exact (deltaLimit A Y).inv_hom_id_app ((push A f).obj M)

end Limit
section AugmentationProof
private theorem natTrans_ext_of_resolutions
    {C D E : Type*} [Category C] [Category D] [Category E]
    (Q : C ⥤ D) (W : MorphismProperty C) [Q.IsLocalization W]
    (S : C → Prop)
    (hres : ∀ K, ∃ (P : C) (s : P ⟶ K), S P ∧ W s)
    {F G : D ⥤ E} (a b : F ⟶ G)
    (h : ∀ P, S P → a.app (Q.obj P) = b.app (Q.obj P)) : a = b := by
  apply Localization.natTrans_ext Q W
  intro K
  obtain ⟨P, s, hP, hs⟩ := hres K
  have : IsIso (Q.map s) := Localization.inverts Q W s hs
  apply (cancel_epi (F.map (Q.map s))).1
  rw [a.naturality, b.naturality, h P hP]


section HomotopyAugmentation
universe u₂ v₂
variable {C D T U : Type u₂} [Category.{v₂} C] [Category.{v₂} D]
  [Category.{v₂} T] [Category.{v₂} U] [Abelian C] [Abelian D] [Abelian T] [Abelian U]
  (F : C ⥤ D) (H : T ⥤ U) (P₀ P : C ⥤ T) (Q₀ Q : D ⥤ U)
  [F.Additive] [H.Additive] [P₀.Additive] [P.Additive] [Q₀.Additive] [Q.Additive]
  (e₀ : P₀ ⋙ H ≅ F ⋙ Q₀) (e : P ⋙ H ≅ F ⋙ Q)
  (a : P₀ ⟶ P) (b : Q₀ ⟶ Q)
  (h : ∀ M, e₀.hom.app M ≫ b.app (F.obj M) = H.map (a.app M) ≫ e.hom.app M)
private theorem homotopy_square_component (K : HomotopyCategory C (.up ℤ)) :
    (Functor.mapHomotopyCategoryCompIso e (.up ℤ)).hom.app K ≫
      (Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ Q)) (.up ℤ)).inv.app K =
        (NatTrans.mapHomotopyCategory e.hom (.up ℤ)).app K := by
  obtain ⟨P, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
  change (HomotopyCategory.quotient U (.up ℤ)).map _ ≫
    (HomotopyCategory.quotient U (.up ℤ)).map _ =
      (HomotopyCategory.quotient U (.up ℤ)).map _
  rw [← Functor.map_comp]
  congr 1
  ext i
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplexCompIso,
    NatIso.mapHomologicalComplex_hom_app_f, NatIso.mapHomologicalComplex_inv_app_f,
    Iso.refl_inv, NatTrans.id_app, NatTrans.mapHomologicalComplex_app_f]
  erw [Category.comp_id]
  rfl

include h in
private theorem homotopy_augmentation_square (K : HomotopyCategory C (.up ℤ)) :
    ((Functor.mapHomotopyCategoryCompIso e₀ (.up ℤ)).hom.app K ≫
      (Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ Q₀)) (.up ℤ)).inv.app K) ≫
        (NatTrans.mapHomotopyCategory b (.up ℤ)).app ((F.mapHomotopyCategory (.up ℤ)).obj K) =
    (H.mapHomotopyCategory (.up ℤ)).map ((NatTrans.mapHomotopyCategory a (.up ℤ)).app K) ≫
      ((Functor.mapHomotopyCategoryCompIso e (.up ℤ)).hom.app K ≫
        (Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ Q)) (.up ℤ)).inv.app K) := by
  obtain ⟨P, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
  change ((_ : _ ⟶ _) ≫ (HomotopyCategory.quotient U (.up ℤ)).map _) ≫
    (HomotopyCategory.quotient U (.up ℤ)).map _ =
    (HomotopyCategory.quotient U (.up ℤ)).map _ ≫
      ((_ : _ ⟶ _) ≫ (HomotopyCategory.quotient U (.up ℤ)).map _)
  change ((HomotopyCategory.quotient U (.up ℤ)).map _ ≫
    (HomotopyCategory.quotient U (.up ℤ)).map _) ≫
    (HomotopyCategory.quotient U (.up ℤ)).map _ =
    (HomotopyCategory.quotient U (.up ℤ)).map _ ≫
      ((HomotopyCategory.quotient U (.up ℤ)).map _ ≫
        (HomotopyCategory.quotient U (.up ℤ)).map _)
  simp only [← Functor.map_comp]
  congr 1
  ext i
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
    NatTrans.mapHomologicalComplex_app_f, Functor.mapHomologicalComplexCompIso,
    NatIso.mapHomologicalComplex_hom_app_f, NatIso.mapHomologicalComplex_inv_app_f,
    Iso.refl_inv, NatTrans.id_app]
  erw [Category.comp_id, Category.comp_id]
  exact h (P.X i)
end HomotopyAugmentation

section Augmentation
universe u₁ v₁ w₁
variable {C D T U : Type u₁} [Category.{v₁} C] [Category.{v₁} D]
  [Category.{v₁} T] [Category.{v₁} U] [Abelian C] [Abelian D] [Abelian T] [Abelian U]
  [HasDerivedCategory.{w₁} C] [HasDerivedCategory.{w₁} D]
  [HasDerivedCategory.{w₁} T] [HasDerivedCategory.{w₁} U]
  (F : C ⥤ D) (H : T ⥤ U) (P₀ P : C ⥤ T) (Q₀ Q : D ⥤ U)
  [F.Additive] [H.Additive] [P₀.Additive] [P.Additive] [Q₀.Additive] [Q.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits H] [PreservesFiniteColimits H]
  [PreservesFiniteLimits P₀] [PreservesFiniteColimits P₀]
  [PreservesFiniteLimits Q₀] [PreservesFiniteColimits Q₀]
  (RP : DerivedCategory C ⥤ DerivedCategory T)
  (RQ : DerivedCategory D ⥤ DerivedCategory U)
  (cP : DerivedCategory.Qh ⋙ RP ⟶ P.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
  (cQ : DerivedCategory.Qh ⋙ RQ ⟶ Q.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
  (a : P₀ ⟶ P) (b : Q₀ ⟶ Q)
  (aD : P₀.mapDerivedCategory ⟶ RP) (bD : Q₀.mapDerivedCategory ⟶ RQ)
  (s₀ : P₀.mapDerivedCategory ⋙ H.mapDerivedCategory ≅ F.mapDerivedCategory ⋙ Q₀.mapDerivedCategory)
  (s : RP ⋙ H.mapDerivedCategory ≅ F.mapDerivedCategory ⋙ RQ)
  (K : HomotopyCategory C (.up ℤ))
  (t₀ : (H.mapHomotopyCategory (.up ℤ)).obj ((P₀.mapHomotopyCategory (.up ℤ)).obj K) ⟶
    (Q₀.mapHomotopyCategory (.up ℤ)).obj ((F.mapHomotopyCategory (.up ℤ)).obj K))
  (t : (H.mapHomotopyCategory (.up ℤ)).obj ((P.mapHomotopyCategory (.up ℤ)).obj K) ⟶
    (Q.mapHomotopyCategory (.up ℤ)).obj ((F.mapHomotopyCategory (.up ℤ)).obj K))

private theorem square_fac_normalized
    [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    [PreservesFiniteLimits Q] [PreservesFiniteColimits Q]
    (e : P ⋙ H ≅ F ⋙ Q) :
    (Functor.mapDerivedCategorySquareIso e).hom.app (DerivedCategory.Qh.obj K) ≫
      Q.mapDerivedCategory.map (F.mapDerivedCategoryFactorsh.hom.app K) ≫
        Q.mapDerivedCategoryFactorsh.hom.app ((F.mapHomotopyCategory (.up ℤ)).obj K) =
      H.mapDerivedCategory.map (P.mapDerivedCategoryFactorsh.hom.app K) ≫
        H.mapDerivedCategoryFactorsh.hom.app ((P.mapHomotopyCategory (.up ℤ)).obj K) ≫
          DerivedCategory.Qh.map
            ((Functor.mapHomotopyCategoryCompIso e (.up ℤ)).hom.app K ≫
              (Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ Q)) (.up ℤ)).inv.app K) := by
  rw [homotopy_square_component F H P Q e K]
  exact EvalTest.square_fac F H P Q e K

set_option backward.isDefEq.respectTransparency false in
private theorem augmentation_square_at
    [IsIso (cP.app K)] [IsIso t]
    (ha : aD.app (DerivedCategory.Qh.obj K) ≫ cP.app K =
      P₀.mapDerivedCategoryFactorsh.hom.app K ≫
        DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory a (.up ℤ)).app K))
    (hb : bD.app (DerivedCategory.Qh.obj ((F.mapHomotopyCategory (.up ℤ)).obj K)) ≫
      cQ.app ((F.mapHomotopyCategory (.up ℤ)).obj K) =
      Q₀.mapDerivedCategoryFactorsh.hom.app ((F.mapHomotopyCategory (.up ℤ)).obj K) ≫
        DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory b (.up ℤ)).app
          ((F.mapHomotopyCategory (.up ℤ)).obj K)))
    (h₀ : s₀.hom.app (DerivedCategory.Qh.obj K) ≫
      Q₀.mapDerivedCategory.map (F.mapDerivedCategoryFactorsh.hom.app K) ≫
        Q₀.mapDerivedCategoryFactorsh.hom.app ((F.mapHomotopyCategory (.up ℤ)).obj K) =
      H.mapDerivedCategory.map (P₀.mapDerivedCategoryFactorsh.hom.app K) ≫
        H.mapDerivedCategoryFactorsh.hom.app ((P₀.mapHomotopyCategory (.up ℤ)).obj K) ≫
          DerivedCategory.Qh.map t₀)
    (h : s.hom.app (DerivedCategory.Qh.obj K) ≫
      RQ.map (F.mapDerivedCategoryFactorsh.hom.app K) ≫
        cQ.app ((F.mapHomotopyCategory (.up ℤ)).obj K) =
      H.mapDerivedCategory.map (cP.app K) ≫
        H.mapDerivedCategoryFactorsh.hom.app ((P.mapHomotopyCategory (.up ℤ)).obj K) ≫
          DerivedCategory.Qh.map t)
    (ht : t₀ ≫ (NatTrans.mapHomotopyCategory b (.up ℤ)).app
        ((F.mapHomotopyCategory (.up ℤ)).obj K) =
      (H.mapHomotopyCategory (.up ℤ)).map
        ((NatTrans.mapHomotopyCategory a (.up ℤ)).app K) ≫ t) :
    s₀.hom.app (DerivedCategory.Qh.obj K) ≫ bD.app (F.mapDerivedCategory.obj
        (DerivedCategory.Qh.obj K)) =
      H.mapDerivedCategory.map (aD.app (DerivedCategory.Qh.obj K)) ≫
        s.hom.app (DerivedCategory.Qh.obj K) := by
  have hc : IsIso (RQ.map (F.mapDerivedCategoryFactorsh.hom.app K) ≫
      cQ.app ((F.mapHomotopyCategory (.up ℤ)).obj K)) := by
    have hi : IsIso (s.hom.app (DerivedCategory.Qh.obj K) ≫
      RQ.map (F.mapDerivedCategoryFactorsh.hom.app K) ≫
        cQ.app ((F.mapHomotopyCategory (.up ℤ)).obj K)) := by
      rw [h]
      infer_instance
    exact IsIso.of_isIso_comp_left (s.hom.app (DerivedCategory.Qh.obj K)) _
  apply (cancel_mono (RQ.map (F.mapDerivedCategoryFactorsh.hom.app K) ≫
    cQ.app ((F.mapHomotopyCategory (.up ℤ)).obj K))).1
  simp only [Category.assoc]
  rw [← bD.naturality_assoc]
  dsimp only [Functor.comp_obj]
  erw [hb, reassoc_of% h₀, h]
  rw [← H.mapDerivedCategory.map_comp_assoc, ha, H.mapDerivedCategory.map_comp]
  simp only [Category.assoc]
  erw [H.mapDerivedCategoryFactorsh.hom.naturality_assoc]
  simp only [Functor.comp_map]
  rw [← DerivedCategory.Qh.map_comp, ← DerivedCategory.Qh.map_comp, ht]

private theorem exact_normalized
    [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    [PreservesFiniteLimits Q] [PreservesFiniteColimits Q]
    (e : P ⋙ H ≅ F ⋙ Q) :
    IsReductionPullAt P Q F H P.mapDerivedCategory Q.mapDerivedCategory
      P.mapDerivedCategoryFactorsh.hom Q.mapDerivedCategoryFactorsh.hom e
      (Functor.mapDerivedCategorySquareIso e) K :=
  square_fac_normalized F H P Q K e

set_option backward.isDefEq.respectTransparency false in
private theorem augmentation_square_normalized [IsIso (cP.app K)]
    (e₀ : P₀ ⋙ H ≅ F ⋙ Q₀) (e : P ⋙ H ≅ F ⋙ Q)
    (ha : aD.app (DerivedCategory.Qh.obj K) ≫ cP.app K =
      P₀.mapDerivedCategoryFactorsh.hom.app K ≫
        DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory a (.up ℤ)).app K))
    (hb : bD.app (DerivedCategory.Qh.obj ((F.mapHomotopyCategory (.up ℤ)).obj K)) ≫
      cQ.app ((F.mapHomotopyCategory (.up ℤ)).obj K) =
      Q₀.mapDerivedCategoryFactorsh.hom.app ((F.mapHomotopyCategory (.up ℤ)).obj K) ≫
        DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory b (.up ℤ)).app
          ((F.mapHomotopyCategory (.up ℤ)).obj K)))
    (h₀ : IsReductionPullAt P₀ Q₀ F H P₀.mapDerivedCategory Q₀.mapDerivedCategory
      P₀.mapDerivedCategoryFactorsh.hom Q₀.mapDerivedCategoryFactorsh.hom e₀ s₀ K)
    (h : IsReductionPullAt P Q F H RP RQ cP cQ e s K)
    (he : ∀ M, e₀.hom.app M ≫ b.app (F.obj M) = H.map (a.app M) ≫ e.hom.app M) :
    s₀.hom.app (DerivedCategory.Qh.obj K) ≫ bD.app (F.mapDerivedCategory.obj
        (DerivedCategory.Qh.obj K)) =
      H.mapDerivedCategory.map (aD.app (DerivedCategory.Qh.obj K)) ≫
        s.hom.app (DerivedCategory.Qh.obj K) :=
  augmentation_square_at F H P₀ P Q₀ Q RP RQ cP cQ a b aD bD s₀ s K _ _ ha hb h₀ h
    (homotopy_augmentation_square F H P₀ P Q₀ Q e₀ e a b he K)

set_option backward.isDefEq.respectTransparency false in
private theorem augmentation_square_natural (hCP : IsIso (cP.app K))
    (e₀ : P₀ ⋙ H ≅ F ⋙ Q₀) (e : P ⋙ H ≅ F ⋙ Q)
    (aH : DerivedCategory.Qh ⋙ P₀.mapDerivedCategory ⟶
      P.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (bH : DerivedCategory.Qh ⋙ Q₀.mapDerivedCategory ⟶
      Q.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (hβP : aH = P₀.mapDerivedCategoryFactorsh.hom ≫ Functor.whiskerRight
      (NatTrans.mapHomotopyCategory a (.up ℤ)) DerivedCategory.Qh)
    (hβQ : bH = Q₀.mapDerivedCategoryFactorsh.hom ≫ Functor.whiskerRight
      (NatTrans.mapHomotopyCategory b (.up ℤ)) DerivedCategory.Qh)
    (ha : aD.app (DerivedCategory.Qh.obj K) ≫ cP.app K = aH.app K)
    (hb : bD.app (DerivedCategory.Qh.obj ((F.mapHomotopyCategory (.up ℤ)).obj K)) ≫
      cQ.app ((F.mapHomotopyCategory (.up ℤ)).obj K) =
        bH.app ((F.mapHomotopyCategory (.up ℤ)).obj K))
    (h₀ : IsReductionPullAt P₀ Q₀ F H P₀.mapDerivedCategory Q₀.mapDerivedCategory
      P₀.mapDerivedCategoryFactorsh.hom Q₀.mapDerivedCategoryFactorsh.hom e₀ s₀ K)
    (h : IsReductionPullAt P Q F H RP RQ cP cQ e s K)
    (he : ∀ M, e₀.hom.app M ≫ b.app (F.obj M) = H.map (a.app M) ≫ e.hom.app M) :
    s₀.hom.app (DerivedCategory.Qh.obj K) ≫ bD.app (F.mapDerivedCategory.obj
        (DerivedCategory.Qh.obj K)) =
      H.mapDerivedCategory.map (aD.app (DerivedCategory.Qh.obj K)) ≫
        s.hom.app (DerivedCategory.Qh.obj K) := by
  let := hCP
  apply augmentation_square_normalized F H P₀ P Q₀ Q RP RQ cP cQ a b aD bD s₀ s K e₀ e
  · simpa only [NatTrans.comp_app, Functor.whiskerRight_app] using
      ha.trans (congr_app hβP K)
  · simpa only [NatTrans.comp_app, Functor.whiskerRight_app] using
      hb.trans (congr_app hβQ ((F.mapHomotopyCategory (.up ℤ)).obj K))
  · exact h₀
  · exact h
  · exact he

end Augmentation

variable {A : Type (u + 1)} [CommRing A] (I : Ideal A)
set_option backward.isDefEq.respectTransparency false in
private theorem ordinary_augmentation_pull {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : Modules A Y) :
    (Functor.compConstIso ℕᵒᵖ (modulePullback A f)).inv.app M ≫
        (ordinaryAugmentation I X).app ((modulePullback A f).obj M) =
      (towerPullback A f).map ((ordinaryAugmentation I Y).app M) ≫
        (ordinaryReductionPull I f).hom.app M := by
  apply NatTrans.ext
  funext n
  let a := proEtaleRingModuleAdjunction f (coefficients A Y) (coefficients A X)
    (constantRingIso A f)
  apply (a.homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  simp only [NatTrans.comp_app, Functor.compConstIso_inv_app_app]
  change a.unit.app M ≫ (moduleDirectImage A f).map
      (((ordinaryAugmentation I X).app ((modulePullback A f).obj M)).app n) =
    a.unit.app M ≫ (moduleDirectImage A f).map
      ((modulePullback A f).map (((ordinaryAugmentation I Y).app M).app n) ≫
        ((ordinaryReductionPull I f).hom.app M).app n)
  rw [Functor.map_comp]
  erw [a.unit_naturality_assoc]
  ext U x
  change (((ordinaryAugmentation I X).app ((modulePullback A f).obj M)).app n).val.app
      (op ((proEtaleBaseChange f).obj U.unop)) ((a.unit.app M).val.app U x) =
    (((ordinaryReductionPull I f).hom.app M).app n).val.app
      (op ((proEtaleBaseChange f).obj U.unop))
      ((a.unit.app ((level I Y n.unop).obj M)).val.app U
        ((((ordinaryAugmentation I Y).app M).app n).val.app U x))
  erw [(ordinaryAugmentation_existsUnique I X).exists.choose_spec,
    (ordinaryAugmentation_existsUnique I Y).exists.choose_spec,
    (ordinaryReductionPull_existsUnique I f).exists.choose_spec]
  simp only [map_one]
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem augmentation_fac (Z : Scheme.{u}) (K : HomotopyCategory (Modules A Z) (.up ℤ)) :
    (augmentation I Z).app (DerivedCategory.Qh.obj K) ≫ (reductionCounit I Z).app K =
      (augmentationHomotopy I Z).app K := by
  have : (reduction I Z).IsLeftDerivedFunctor (reductionCounit I Z)
      (HomotopyCategory.quasiIso (Modules A Z) (.up ℤ)) := (reductionModel I Z).universal
  exact (reduction I Z).leftDerived_fac_app (reductionCounit I Z)
    (HomotopyCategory.quasiIso (Modules A Z) (.up ℤ))
    (delta A Z) (augmentationHomotopy I Z) K


private theorem reductionPull_spec {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ∀ P : CochainComplex (Modules A Y) ℤ,
      CochainComplex.IsKFlatIndependentCoefficients (R := coefficients A Y) P →
      IsReductionPullAt (reductionModule I Y) (reductionModule I X)
        (modulePullback A f) (towerPullback A f) (reduction I Y) (reduction I X)
        (reductionCounit I Y) (reductionCounit I X) (ordinaryReductionPull I f)
        (reductionPull I f) ((HomotopyCategory.quotient _ (.up ℤ)).obj P) :=
  (reductionPull_existsUnique I f).exists.choose_spec


private theorem augmentationHomotopy_spec (Z : Scheme.{u}) :
    augmentationHomotopy I Z =
      (Functor.const ℕᵒᵖ : Modules A Z ⥤ Towers A Z).mapDerivedCategoryFactorsh.hom ≫
        Functor.whiskerRight
          (NatTrans.mapHomotopyCategory (ordinaryAugmentation I Z) (.up ℤ))
          DerivedCategory.Qh := rfl

private theorem reduction_computes (Z : Scheme.{u})
    (P : CochainComplex (Modules A Z) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (R := coefficients A Z) P) :
    IsIso ((reductionCounit I Z).app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) :=
  (reductionModel I Z).computes P hP

private theorem projection_spec {X Y : Scheme.{u}} (f : X ⟶ Y) :
    projection I f =
      (mateEquiv
        (proEtaleRingDerivedAdjunction f (coefficients A Y) (coefficients A X)
          (constantRingIso A f)) (adj A f)
        (TwoSquare.mk _ _ _ _ (reductionPull I f).hom)).natTrans := rfl

attribute [local irreducible] augmentation augmentationHomotopy reduction reductionCounit
  reductionPull ordinaryReductionPull projection

set_option backward.isDefEq.respectTransparency true in
private theorem augmentation_pull_at_homotopy {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : HomotopyCategory (Modules A Y) (.up ℤ))
    (hC : IsIso ((reductionCounit I Y).app K))
    (hS : IsReductionPullAt (reductionModule I Y) (reductionModule I X)
      (modulePullback A f) (towerPullback A f) (reduction I Y) (reduction I X)
      (reductionCounit I Y) (reductionCounit I X) (ordinaryReductionPull I f)
      (reductionPull I f) K) :
    (deltaPull A f).hom.app (DerivedCategory.Qh.obj K) ≫
        (augmentation I X).app ((pull A f).obj (DerivedCategory.Qh.obj K)) =
      (G A f).map ((augmentation I Y).app (DerivedCategory.Qh.obj K)) ≫
        (reductionPull I f).hom.app (DerivedCategory.Qh.obj K) := by
  exact augmentation_square_natural (modulePullback A f) (towerPullback A f)
    (Functor.const ℕᵒᵖ) (reductionModule I Y) (Functor.const ℕᵒᵖ) (reductionModule I X)
    (reduction I Y) (reduction I X) (reductionCounit I Y) (reductionCounit I X)
    (ordinaryAugmentation I Y) (ordinaryAugmentation I X) (augmentation I Y) (augmentation I X)
    (deltaPull A f) (reductionPull I f) K hC
    (Functor.compConstIso ℕᵒᵖ (modulePullback A f)).symm (ordinaryReductionPull I f)
    (augmentationHomotopy I Y) (augmentationHomotopy I X)
    (augmentationHomotopy_spec I Y) (augmentationHomotopy_spec I X)
    (augmentation_fac I Y K) (augmentation_fac I X _)
    (exact_normalized (modulePullback A f) (towerPullback A f)
      (Functor.const ℕᵒᵖ) (Functor.const ℕᵒᵖ) K
      (Functor.compConstIso ℕᵒᵖ (modulePullback A f)).symm)
    hS (ordinary_augmentation_pull I f)


set_option backward.isDefEq.respectTransparency true in
private theorem augmentation_pull_at {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P : CochainComplex (Modules A Y) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (R := coefficients A Y) P) :
    (deltaPull A f).hom.app (DerivedCategory.Qh.obj
          ((HomotopyCategory.quotient (Modules A Y) (.up ℤ)).obj P)) ≫
        (augmentation I X).app ((pull A f).obj (DerivedCategory.Qh.obj
          ((HomotopyCategory.quotient (Modules A Y) (.up ℤ)).obj P))) =
      (G A f).map ((augmentation I Y).app (DerivedCategory.Qh.obj
          ((HomotopyCategory.quotient (Modules A Y) (.up ℤ)).obj P))) ≫
        (reductionPull I f).hom.app (DerivedCategory.Qh.obj
          ((HomotopyCategory.quotient (Modules A Y) (.up ℤ)).obj P)) := by
  exact augmentation_pull_at_homotopy I f _ (reduction_computes I Y P hP)
    (reductionPull_spec I f P hP)

set_option backward.isDefEq.respectTransparency true in
private theorem augmentation_pull {X Y : Scheme.{u}} (f : X ⟶ Y)
    (N : DerivedCategory (Modules A Y)) :
    (deltaPull A f).hom.app N ≫ (augmentation I X).app ((pull A f).obj N) =
      (G A f).map ((augmentation I Y).app N) ≫ (reductionPull I f).hom.app N := by
  have h : (deltaPull A f).hom ≫ Functor.whiskerLeft (pull A f) (augmentation I X) =
      Functor.whiskerRight (augmentation I Y) (G A f) ≫ (reductionPull I f).hom := by
    let H := HomotopyCategory.quotient (Modules A Y) (.up ℤ)
    apply natTrans_ext_of_resolutions DerivedCategory.Qh
      (HomotopyCategory.quasiIso (Modules A Y) (.up ℤ))
      (fun K ↦ ∃ P : CochainComplex (Modules A Y) ℤ,
        CochainComplex.IsKFlatIndependentCoefficients (R := coefficients A Y) P ∧
          H.obj P = K)
    · intro K
      obtain ⟨E, rfl⟩ := K.quotient_obj_surjective
      obtain ⟨P, s, hP, hs⟩ := exists_kflat_resolution (R := coefficients A Y) E
      exact ⟨H.obj P, H.map s, ⟨P, hP, rfl⟩,
        (HomotopyCategory.quotient_map_mem_quasiIso_iff s).2 hs⟩
    · rintro K ⟨P, hP, rfl⟩
      exact augmentation_pull_at I f P hP
  exact congr_app h N



set_option backward.isDefEq.respectTransparency true in
private theorem projection_normalized {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : DerivedCategory (Modules A X)) :
    (augmentation I Y).app ((push A f).obj M) ≫ (projection I f).app M =
      (chi A f).hom.app M ≫ (R A f).map ((augmentation I X).app M) := by
  rw [projection_spec]
  have hm := NormalizationTest.mate_naturality
    (proEtaleRingDerivedAdjunction f (coefficients A Y) (coefficients A X)
      (constantRingIso A f)) (adj A f)
    (deltaPull A f).hom (reductionPull I f).hom
    (augmentation I Y) (augmentation I X) (augmentation_pull I f) M
  exact hm.trans (congrArg
    (fun t ↦ t ≫ (R A f).map ((augmentation I X).app M))
    (congr_app (chi_mate A f) M).symm)


end AugmentationProof
end Proofs

variable (A : Type (u + 1)) [CommRing A]

/-- Constant strict towers have normalized derived direct image, evaluation, inverse
limit and quotient augmentation, for the given coefficient datum and every object.
Source: agent argument supporting fix-lem-exchanges Step 5, using Stacks 08BJ, 070K,
0940, 0941, 0A07, 06YS, 07A4 and 0B56
(blueprint: lem-sf-cbc-constant-tower-direct-image-normalization).

Proof:
1. The universal units of the canonical right-derived composition isomorphisms give
   the stated formula for chi on K-injectives. Applying exact evaluation and the
   ordinary constant-square mate gives its evaluation normalization.
2. The diagonal/limit unit is invertible. The unit identity for conjugate adjunctions,
   together with the identification of chi as the diagonal pullback square's mate,
   gives the inverse-limit equation.
3. The ordinary quotient comparison is constructed through scalar-extension and
   inverse-image adjunctions. Its formula on every pure tensor proves strict
   transition compatibility and uniqueness. Flat K-flat resolutions and invertible
   reduction counits descend this square to the derived categories; equality on the
   resolving class proves its uniqueness.
4. The ordinary augmentation square commutes on 1 tensor x. The reduction counit
   factorization and the normalized comparison give its derived version on K-flat
   models, and resolutions extend equality to every object. Naturality of mates then
   gives exactly the projection/augmentation equation in the strict tower category. -/
theorem constantTowerDirectImageNormalization
    (d : CompleteCoefficientDatum A) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    IsDirectImageNormalizedOnKInjectives (moduleDirectImage A f)
      (Functor.const ℕᵒᵖ : Modules A X ⥤ Towers A X)
      (Functor.const ℕᵒᵖ : Modules A Y ⥤ Towers A Y) (towerDirectImage A f)
      (Functor.compConstIso ℕᵒᵖ (moduleDirectImage A f)) (chi A f) ∧
    (∀ (M : DerivedCategory (Modules A X)) (n : ℕ),
      (ev A Y n).map ((chi A f).hom.app M) ≫
          (evalR A f n).app ((delta A X).obj M) ≫
          (push A f).map ((deltaEval A X n).hom.app M) =
        (deltaEval A Y n).hom.app ((push A f).obj M)) ∧
    (∀ M : DerivedCategory (Modules A X),
      (push A f).map ((deltaLimit A X).inv.app M) ≫
          (limitPush A f).hom.app ((delta A X).obj M) ≫
          (L A Y).map ((chi A f).inv.app M) ≫
          (deltaLimit A Y).hom.app ((push A f).obj M) = 𝟙 _) ∧
    (∀ M : DerivedCategory (Modules A X),
      (augmentation d.ideal Y).app ((push A f).obj M) ≫
          (projection d.ideal f).app M =
        (chi A f).hom.app M ≫ (R A f).map ((augmentation d.ideal X).app M))   := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact Proofs.chi_normalized A f
  · intro M n
    exact Proofs.evaluation_normalized A f M n
  · intro M
    exact Proofs.limit_normalized_concrete A f M
  · intro M
    exact Proofs.projection_normalized d.ideal f M

end AlgebraicGeometry.ProEtale.StrictTower.ConstantNormalization
