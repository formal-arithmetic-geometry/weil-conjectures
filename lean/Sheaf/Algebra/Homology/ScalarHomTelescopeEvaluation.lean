/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q97
-/
module

public import Sheaf.Algebra.Homology.LocalizationHomComparisonData
import all Sheaf.Algebra.Homology.InternalHomLocalizationComparison
public import Sheaf.CategoryTheory.ScalarLocalizationCoefficientActions
public import Sheaf.CategoryTheory.RingedSiteLocalization
public import Sheaf.Algebra.Homology.ScalarInternalHomAdjunction
public import Sheaf.Algebra.Homology.ScalarInternalHomData
public import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
import all Sheaf.CategoryTheory.ScalarLocalizationModuleColimit
import Sheaf.Algebra.Homology.RationalTermHomComparison

/-! # Scalar internal Hom: telescope legs and evaluation

Source: Bhatt--Scholze, Lemma 6.8.12 and Proposition 6.8.14(2), pp. 61--62;
Stacks Project, Tags 070I, 03ET, 03CY, 03EK and 00CM
(blueprint: lem-sfb-scalar-hom-telescope-evaluation).
The helpers package the actual scalar telescope, its legs, and the representative
normalizations in the statement. No boundedness is imposed on representatives.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u a w b h

open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures SheafOfModules

namespace CategoryTheory

/-- The repeated-scalar diagram, functorial in its input object.
Source: Stacks 00CM, 03CY and 03EK
(blueprint: lem-sfb-scalar-hom-telescope-evaluation). -/
def scalarHomTelescopeDiagram (A : Type a) [CommRing A]
    {B : Type b} [Category.{h} B] [Preadditive B] [Linear A B] (t : A) :
    B ⥤ (ℕ ⥤ B) where
  obj P := Functor.ofSequence (X := fun _ : ℕ ↦ P) (fun _ ↦ t • 𝟙 P)
  map f := NatTrans.ofSequence (fun _ ↦ f) (fun _ ↦ by
    simp only [Functor.ofSequence_map_homOfLE_succ]
    change (t • 𝟙 _) ≫ f = f ≫ (t • 𝟙 _)
    simp only [Linear.smul_comp, Linear.comp_smul, Category.id_comp, Category.comp_id])
  map_id P := by ext n; rfl
  map_comp f g := by ext n; rfl

set_option linter.style.haveILetI false

attribute [local instance 100000] RationalTermHom.coefficientSheafify
attribute [local instance 100000] RationalTermHom.coefficientCompose
  RationalTermHom.coefficientLocallyBijective

set_option backward.isDefEq.respectTransparency true in
private theorem map_scalar_of_iso
    {B D : Type*} [Category B] [Category D] [Preadditive B] [Preadditive D]
    {R S : Type*} [CommRing R] [CommRing S] [Linear R B] [Linear S D]
    (F : B ⥤ D) {X Y : B} (e : X ≅ Y) (r : R) (s : S)
    (h : F.map (r • 𝟙 X) = s • 𝟙 (F.obj X)) :
    F.map (r • 𝟙 Y) = s • 𝟙 (F.obj Y) := by
  have he : r • 𝟙 Y = e.inv ≫ (r • 𝟙 X) ≫ e.hom := by
    simp only [Linear.comp_smul, Linear.smul_comp, Category.id_comp, Iso.inv_hom_id]
  rw [he, F.map_comp, F.map_comp, h]
  simp only [Linear.smul_comp, Linear.comp_smul, Category.id_comp,
    ← F.map_comp, Iso.inv_hom_id, F.map_id]

set_option backward.isDefEq.respectTransparency true in
private theorem exactDerived_scalar
    {B D : Type*} [Category B] [Category D] [Abelian B] [Abelian D]
    [HasDerivedCategory.{w} B] [HasDerivedCategory.{w} D]
    {R S : Type*} [CommRing R] [CommRing S] [Linear R B] [Linear S D]
    (F : B ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (r : R) (s : S) (h : ∀ X : B, F.map (r • 𝟙 X) = s • 𝟙 (F.obj X))
    (N : DerivedCategory B) :
    F.mapDerivedCategory.map (r • 𝟙 N) = s • 𝟙 (F.mapDerivedCategory.obj N) := by
  have hQ (P : CochainComplex B ℤ) :
      F.mapDerivedCategory.map (r • 𝟙 (DerivedCategory.Q.obj P)) =
        s • 𝟙 (F.mapDerivedCategory.obj (DerivedCategory.Q.obj P)) := by
    have hc : (F.mapHomologicalComplex (.up ℤ)).map (r • 𝟙 P) =
        s • 𝟙 ((F.mapHomologicalComplex (.up ℤ)).obj P) := by
      apply HomologicalComplex.hom_ext
      intro i
      exact h (P.X i)
    have hq : DerivedCategory.Q.map (r • 𝟙 P) =
        r • 𝟙 (DerivedCategory.Q.obj P) := by
      rw [Functor.map_smul, Functor.map_id]
    rw [← hq]
    apply (cancel_mono (F.mapDerivedCategoryFactors.hom.app P)).mp
    rw [F.mapDerivedCategoryFactors_hom_naturality, hc, Functor.map_smul, Functor.map_id]
    simp only [Linear.comp_smul, Linear.smul_comp, Category.id_comp]
    exact congrArg (fun f ↦ s • f) (Category.comp_id _)
  exact map_scalar_of_iso F.mapDerivedCategory
    (DerivedCategory.Q.objObjPreimageIso N) r s (hQ _)

set_option backward.isDefEq.respectTransparency true in
private theorem scalar_of_comparison
    {B D : Type*} [Category B] [Category D] [Preadditive B] [Preadditive D]
    {S : Type*} [CommRing S] [Linear S B] [Linear S D]
    (F : B ⥤ D) {X : B} {Y : D} (e : Y ≅ F.obj X) (s : S)
    (f : X ⟶ X) (g : Y ⟶ Y) (hf : f = s • 𝟙 X) (hg : g = s • 𝟙 Y)
    (hn : g ≫ e.hom = e.hom ≫ F.map f) : F.map (s • 𝟙 X) = s • 𝟙 (F.obj X) := by
  rw [hf, hg] at hn
  apply (cancel_epi e.hom).mp
  rw [← hn]
  simp only [Linear.smul_comp, Linear.comp_smul, Category.id_comp, Category.comp_id]

private theorem scalar_sequence_eq
    {B : Type*} [Category B] [Preadditive B]
    {R : Type*} [CommRing R] [Linear R B] {X Y : B}
    (t : R) [Mono (t • 𝟙 Y)] (f g : ℕ → (X ⟶ Y))
    (hf : ∀ n, (t • 𝟙 X) ≫ f (n + 1) = f n)
    (hg : ∀ n, (t • 𝟙 X) ≫ g (n + 1) = g n)
    (hzero : f 0 = g 0) : ∀ n, f n = g n := by
  intro n
  induction n with
  | zero => exact hzero
  | succ n ih =>
    apply (cancel_mono (t • 𝟙 Y)).mp
    calc
      _ = (t • 𝟙 X) ≫ f (n + 1) := by simp only
        [Linear.comp_smul, Linear.smul_comp, Category.comp_id, Category.id_comp]
      _ = f n := hf n
      _ = g n := ih
      _ = (t • 𝟙 X) ≫ g (n + 1) := (hg n).symm
      _ = _ := by simp only
        [Linear.comp_smul, Linear.smul_comp, Category.comp_id, Category.id_comp]

private theorem telescopeLeg_map
    {B : Type*} [Category B] [Preadditive B]
    {S : Type*} [CommRing S] [Linear S B] [HasColimitsOfShape ℕ B]
    (s : S) {X Y : B} (f : X ⟶ Y) (n : ℕ) :
    colimit.ι ((scalarHomTelescopeDiagram S s).obj X) n ≫
        colim.map ((scalarHomTelescopeDiagram S s).map f) =
      f ≫ colimit.ι ((scalarHomTelescopeDiagram S s).obj Y) n :=
  colimit.ι_map ((scalarHomTelescopeDiagram S s).map f) n

private theorem zero_leg_square
    {B : Type*} [Category B] {P P' C C' T W : B}
    {f : P ⟶ P'} {j : P ⟶ C} {j' : P' ⟶ C'} {g : C ⟶ C'}
    {e : P ⟶ T} {e' : P' ⟶ T} {b : C ⟶ W} {b' : C' ⟶ W} {l : T ⟶ W}
    (hmap : j ≫ g = f ≫ j') (h1 : j ≫ b = e ≫ l)
    (h2 : j' ≫ b' = e' ≫ l) (he : f ≫ e' = e) :
    j ≫ g ≫ b' = j ≫ b := by
  rw [← Category.assoc, hmap, Category.assoc, h2, ← Category.assoc, he, h1]

private theorem gamma_leg
    {B : Type*} [Category B] (F : B ⥤ B)
    {P Q X Y L UH UL : B} (bH : X ≅ UH) (bL : Y ≅ UL)
    (eH : P ≅ F.obj L) (eL : Q ≅ L) (rho : UH ⟶ F.obj UL)
    (lH : F.obj L ⟶ UH) (lL : L ⟶ UL) (jH : P ⟶ X) (jL : Q ⟶ Y)
    (hH : jH ≫ bH.hom = eH.hom ≫ lH) (hL : jL ≫ bL.hom = eL.hom ≫ lL)
    (hc : lH ≫ rho = F.map lL) :
    jH ≫ (bH.hom ≫ rho ≫ F.map bL.inv) = eH.hom ≫ F.map (eL.inv ≫ jL) := by
  calc
    _ = (jH ≫ bH.hom) ≫ rho ≫ F.map bL.inv := by simp only [Category.assoc]
    _ = eH.hom ≫ (lH ≫ rho) ≫ F.map bL.inv := by
      rw [hH]
      simp only [Category.assoc]
    _ = eH.hom ≫ F.map (lL ≫ bL.inv) := by
      rw [hc, F.map_comp]
    _ = _ := by
      apply congrArg (fun k ↦ eH.hom ≫ F.map k)
      apply (cancel_mono bL.hom).mp
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
      rw [hL, Iso.inv_hom_id_assoc]

private theorem gamma_change
    {B : Type*} [Category B] (F : B ⥤ B)
    {X Y X' Y' UH UL : B} (bH : X ≅ UH) (bH' : X' ≅ UH)
    (bL : Y ≅ UL) (bL' : Y' ≅ UL) (rho : UH ⟶ F.obj UL)
    (fH : X ⟶ X') (fL : Y ⟶ Y')
    (hH : fH ≫ bH'.hom = bH.hom) (hL : fL ≫ bL'.hom = bL.hom) :
    fH ≫ (bH'.hom ≫ rho ≫ F.map bL'.inv) =
      (bH.hom ≫ rho ≫ F.map bL.inv) ≫ F.map fL := by
  rw [← Category.assoc, hH]
  simp only [Category.assoc, ← F.map_comp]
  apply congrArg (fun k ↦ bH.hom ≫ rho ≫ F.map k)
  apply (cancel_mono bL'.hom).mp
  simp only [Category.assoc, Iso.inv_hom_id]
  rw [hL, Iso.inv_hom_id]

private theorem closed_evaluation_naturality
    {B : Type*} [Category B] {H : Bᵒᵖ × B ⥤ B}
    (S : CoefficientClosedStructure H) (K : B) {X Y : B} (f : X ⟶ Y) :
    S.tensor.map (Prod.mkHom (H.map (Prod.mkHom (𝟙 (op K)) f)) (𝟙 K)) ≫
      S.evaluation K Y = S.evaluation K X ≫ f := by
  letI := S.monoidal
  simpa only [Functor.comp_map, Functor.id_map, CoefficientClosedStructure.tensor,
    MonoidalCategory.tensor_map, MonoidalCategory.tensorHom_id,
    MonoidalCategory.tensorRight, Functor.flip_obj_map,
    MonoidalCategory.curriedTensor_map_app, CoefficientClosedStructure.evaluation,
    Prod.sectR_map] using
      (S.adjunction K).counit.naturality f

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
  (A : Type a) [CommRing A] (R : Sheaf J CommRingCat.{u})
  (aR : A →+* RingCat.sectionsSubring (R.obj ⋙ forget₂ CommRingCat RingCat)) (t : A)

/-- Termwise sheaf colimit of the actual repeated-t complex diagram.
Source: Stacks 03CY and 03EK; Bhatt--Scholze 6.8.14(2)
(blueprint: lem-sfb-scalar-hom-telescope-evaluation). -/
def scalarHomTelescope :
    CochainComplex (scalarModules J R) ℤ ⥤ CochainComplex (scalarModules J R) ℤ :=
  letI := scalarLocalizationCoefficientLinear A R aR
  scalarHomTelescopeDiagram A (B := CochainComplex (scalarModules J R) ℤ) t ⋙ colim

/-- The nth ordinary complex colimit leg.
Source: Stacks 00CM, 03CY and 03EK
(blueprint: lem-sfb-scalar-hom-telescope-evaluation). -/
def scalarHomTelescopeLeg (P : CochainComplex (scalarModules J R) ℤ) (n : ℕ) :
    P ⟶ (scalarHomTelescope J A R aR t).obj P :=
  letI := scalarLocalizationCoefficientLinear A R aR
  colimit.ι ((scalarHomTelescopeDiagram A t).obj P) n

variable [∀ B : Sheaf J CommRingCat.{u}, HasDerivedCategory.{w} (scalarModules J B)]
  (M : ScalarHomModels.{u, u, u, w} J)

/-- The specified derived scalar unit followed by multiplication by t to power minus n.
Source: Bhatt--Scholze 6.8.14(2); Stacks 00CM and 07A6
(blueprint: lem-sfb-scalar-hom-telescope-evaluation). -/
def scalarHomTelescopeLambda (T : DerivedCategory (scalarModules J R)) (n : ℕ) :
    T ⟶ (scalarDerivedRestriction (ringedLocalizationRingUnit R (aR t))).obj
      ((M.scalar (ringedLocalizationRingUnit R (aR t))).derived.obj T) :=
  letI := scalarLocalizationDerivedLinear (Localization.Away t)
    (ringedLocalizationRing R (aR t)) (scalarLocalizationCoefficientMap A R aR t)
  (M.scalar (ringedLocalizationRingUnit R (aR t))).adjunction.unit.app T ≫
    (scalarDerivedRestriction (ringedLocalizationRingUnit R (aR t))).map
      (((IsLocalization.Away.invSelf t : Localization.Away t) ^ n) •
        𝟙 ((M.scalar (ringedLocalizationRingUnit R (aR t))).derived.obj T))

/-- A telescope identification for every representative of the fixed derived object,
with every leg normalized and compatible with quasi-isomorphic changes of representative.
Source: Bhatt--Scholze 6.8.14(2); Stacks 03CY, 03EK and 07A6
(blueprint: lem-sfb-scalar-hom-telescope-evaluation). -/
structure ScalarHomTelescopePresentation (T : DerivedCategory (scalarModules J R)) where
  /-- The identification for the supplied representative and its supplied isomorphism. -/
  iso : ∀ (P : CochainComplex (scalarModules J R) ℤ) (_e : DerivedCategory.Q.obj P ≅ T),
    DerivedCategory.Q.obj ((scalarHomTelescope J A R aR t).obj P) ≅
      (scalarDerivedRestriction (ringedLocalizationRingUnit R (aR t))).obj
        ((M.scalar (ringedLocalizationRingUnit R (aR t))).derived.obj T)
  /-- Every telescope leg is the corresponding inverse-scalar multiple of the unit. -/
  legs : ∀ (P : CochainComplex (scalarModules J R) ℤ) (e : DerivedCategory.Q.obj P ≅ T)
      (n : ℕ),
    DerivedCategory.Q.map (scalarHomTelescopeLeg J A R aR t P n) ≫ (iso P e).hom =
      e.hom ≫ scalarHomTelescopeLambda J A R aR t M T n
  /-- Compatibility includes arbitrary quasi-isomorphisms, in either direction. -/
  change : ∀ (P P' : CochainComplex (scalarModules J R) ℤ) (f : P ⟶ P')
      (_hf : QuasiIso f) (e : DerivedCategory.Q.obj P ≅ T)
      (e' : DerivedCategory.Q.obj P' ≅ T),
    DerivedCategory.Q.map f ≫ e'.hom = e.hom →
      DerivedCategory.Q.map ((scalarHomTelescope J A R aR t).map f) ≫ (iso P' e').hom =
        (iso P e).hom


attribute [local irreducible] monoidalCategory derivedInternalHomOfUniverses
  localizationUnderlyingDerivedIso localizationHomResolutionIso
  localizationComplexCoconeIsColimit coefficientHomResolutionIso


omit [∀ B : Sheaf J CommRingCat.{u}, HasDerivedCategory.{w} (scalarModules J B)] in
private theorem telescopeSheafifyRing :
    HasSheafify J CommRingCat.{u} := inferInstance

attribute [local instance] telescopeSheafifyRing

omit [∀ B : Sheaf J CommRingCat.{u}, HasDerivedCategory.{w} (scalarModules J B)] in
private theorem telescopeColimits :
    HasColimitsOfShape ℕ (CochainComplex (scalarModules J R) ℤ) := inferInstance

attribute [local instance] telescopeColimits

private theorem telescopeRestrictedScalar
    (N : DerivedCategory (scalarModules J (ringedLocalizationRing R (aR t)))) (r : A) :
    letI := scalarLocalizationDerivedLinear A R aR
    letI := scalarLocalizationDerivedLinear (Localization.Away t)
      (ringedLocalizationRing R (aR t)) (scalarLocalizationCoefficientMap A R aR t)
    (scalarDerivedRestriction (ringedLocalizationRingUnit R (aR t))).map
      (algebraMap A (Localization.Away t) r • 𝟙 N) =
        r • 𝟙 ((scalarDerivedRestriction (ringedLocalizationRingUnit R (aR t))).obj N) := by
  letI := scalarLocalizationCoefficientLinear A R aR
  letI := scalarLocalizationCoefficientLinear (Localization.Away t)
    (ringedLocalizationRing R (aR t)) (scalarLocalizationCoefficientMap A R aR t)
  apply exactDerived_scalar (scalarRestriction.{u, u, u}
    (ringedLocalizationRingUnit R (aR t))) (algebraMap A (Localization.Away t) r) r
  intro N'
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro V
  apply ModuleCat.hom_ext
  ext x
  change (scalarLocalizationCoefficientMap A R aR t
    (algebraMap A (Localization.Away t) r)).val V •
      (show N'.val.obj V from x) = (aR r).val V • x
  have h : scalarLocalizationCoefficientMap A R aR t
      (algebraMap A (Localization.Away t) r) =
      scalarLocalizationSectionsMap (ringedLocalizationRingUnit R (aR t)) (aR r) := by
    unfold scalarLocalizationCoefficientMap
    exact IsLocalization.Away.lift_eq (S := Localization.Away t) t
      (scalarLocalizationSections_isUnit A R aR t) r
  exact congrArg (fun z ↦ z.val V • (show N'.val.obj V from x)) h


attribute [local irreducible] scalarDerivedRestriction

private theorem telescopeLocalizedScalar_isIso (T : DerivedCategory (scalarModules J R)) :
    letI := scalarLocalizationDerivedLinear A R aR
    IsIso (t • 𝟙 ((scalarDerivedRestriction (ringedLocalizationRingUnit R (aR t))).obj
      ((M.scalar (ringedLocalizationRingUnit R (aR t))).derived.obj T))) := by
  letI := scalarLocalizationDerivedLinear A R aR
  letI := scalarLocalizationDerivedLinear (Localization.Away t)
    (ringedLocalizationRing R (aR t)) (scalarLocalizationCoefficientMap A R aR t)
  rw [← telescopeRestrictedScalar J A R aR t _ t]
  have : IsIso (algebraMap A (Localization.Away t) t •
      𝟙 ((M.scalar (ringedLocalizationRingUnit R (aR t))).derived.obj T)) :=
    isIso_scalar_of_inverse _ _ (IsLocalization.Away.invSelf t)
      (IsLocalization.Away.mul_invSelf (S := Localization.Away t) t)
  infer_instance

private theorem telescopeLambda_step (T : DerivedCategory (scalarModules J R)) (n : ℕ) :
    letI := scalarLocalizationDerivedLinear A R aR
    (t • 𝟙 T) ≫ scalarHomTelescopeLambda J A R aR t M T (n + 1) =
      scalarHomTelescopeLambda J A R aR t M T n := by
  letI := scalarLocalizationDerivedLinear A R aR
  letI := scalarLocalizationDerivedLinear (Localization.Away t)
    (ringedLocalizationRing R (aR t)) (scalarLocalizationCoefficientMap A R aR t)
  dsimp only [scalarHomTelescopeLambda]
  exact inverse_scalar_legs_step _ _ _ _ t _ _
    (IsLocalization.Away.mul_invSelf (S := Localization.Away t) t)
    (telescopeRestrictedScalar J A R aR t _ t).symm n

private def telescopeCocone (P : CochainComplex (scalarModules J R) ℤ) :
    letI := scalarLocalizationCoefficientLinear A R aR
    Cocone ((scalarHomTelescopeDiagram A t).obj P) :=
  localizationComplexCocone.{u, u, u} R (aR t) P

private def telescopeCoconeIsColimit (P : CochainComplex (scalarModules J R) ℤ) :
    letI := scalarLocalizationCoefficientLinear A R aR
    IsColimit (telescopeCocone J A R aR t P) :=
  localizationComplexCoconeIsColimit.{u, u, u} R (aR t) P

attribute [local irreducible] telescopeCoconeIsColimit

private def telescopeComplexIso (P : CochainComplex (scalarModules J R) ℤ) :
    (scalarHomTelescope J A R aR t).obj P ≅
      (localizationComplexCocone.{u, u, u} R (aR t) P).pt := by
  letI := scalarLocalizationCoefficientLinear A R aR
  exact colimit.isoColimitCocone
    ⟨telescopeCocone J A R aR t P, telescopeCoconeIsColimit J A R aR t P⟩

omit [∀ B : Sheaf J CommRingCat.{u}, HasDerivedCategory.{w} (scalarModules J B)] in
private theorem telescopeComplexIso_hom (P : CochainComplex (scalarModules J R) ℤ) :
    letI := scalarLocalizationCoefficientLinear A R aR
    (telescopeComplexIso J A R aR t P).hom =
      (colimit.isoColimitCocone
        ⟨telescopeCocone J A R aR t P, telescopeCoconeIsColimit J A R aR t P⟩).hom := rfl

attribute [local irreducible] telescopeComplexIso

private def telescopeDerivedIso (P : CochainComplex (scalarModules J R) ℤ) :
    DerivedCategory.Q.obj ((scalarHomTelescope J A R aR t).obj P) ≅
      (scalarDerivedRestriction (ringedLocalizationRingUnit R (aR t))).obj
        ((M.scalar (ringedLocalizationRingUnit R (aR t))).derived.obj
          (DerivedCategory.Q.obj P)) :=
  DerivedCategory.Q.mapIso (telescopeComplexIso J A R aR t P) ≪≫
    localizationUnderlyingDerivedIso M R (aR t) P

attribute [local irreducible] localizationHomComplex

private theorem telescopeDerivedIso_zero (P : CochainComplex (scalarModules J R) ℤ) :
    DerivedCategory.Q.map (scalarHomTelescopeLeg J A R aR t P 0) ≫
      (telescopeDerivedIso J A R aR t M P).hom =
        (M.scalar (ringedLocalizationRingUnit R (aR t))).adjunction.unit.app
          (DerivedCategory.Q.obj P) := by
  letI := scalarLocalizationCoefficientLinear A R aR
  change DerivedCategory.Q.map (scalarHomTelescopeLeg J A R aR t P 0) ≫
    (DerivedCategory.Q.map (telescopeComplexIso J A R aR t P).hom ≫
      (localizationUnderlyingDerivedIso M R (aR t) P).hom) = _
  rw [← DerivedCategory.Q.map_comp_assoc]
  have hz : scalarHomTelescopeLeg J A R aR t P 0 ≫
      (telescopeComplexIso J A R aR t P).hom =
        (localizationComplexCocone.{u, u, u} R (aR t) P).ι.app 0 :=
    by
      rw [telescopeComplexIso_hom]
      dsimp only [scalarHomTelescopeLeg]
      exact colimit.isoColimitCocone_ι_hom
        (⟨telescopeCocone J A R aR t P, telescopeCoconeIsColimit J A R aR t P⟩) 0
  rw [hz]
  exact localizationUnderlyingDerivedIso_unit M R (aR t) P

attribute [local irreducible] telescopeDerivedIso

private theorem telescopeHom_ext_zero
    (P : CochainComplex (scalarModules J R) ℤ)
    (T : DerivedCategory (scalarModules J R))
    (f g : DerivedCategory.Q.obj ((scalarHomTelescope J A R aR t).obj P) ⟶
      (scalarDerivedRestriction (ringedLocalizationRingUnit R (aR t))).obj
        ((M.scalar (ringedLocalizationRingUnit R (aR t))).derived.obj T))
    (h : DerivedCategory.Q.map (scalarHomTelescopeLeg J A R aR t P 0) ≫ f =
      DerivedCategory.Q.map (scalarHomTelescopeLeg J A R aR t P 0) ≫ g) : f = g := by
  letI : (scalarDerivedRestriction (ringedLocalizationRingUnit R (aR t))).Full :=
    localizationDerivedRestriction_full.{u, u, u, w} M R (aR t)
  let e := telescopeDerivedIso J A R aR t M P
  have hh : e.inv ≫ f = e.inv ≫ g := by
    apply LocalizationHomProof.unit_precomp_injective (M.scalar _).adjunction
      (DerivedCategory.Q.obj P) ((M.scalar _).derived.obj T)
    rw [← telescopeDerivedIso_zero J A R aR t M P]
    simpa only [e, Category.assoc, Iso.hom_inv_id_assoc] using h
  have := congrArg (fun k ↦ e.hom ≫ k) hh
  simpa only [Iso.hom_inv_id_assoc] using this

omit [∀ B : Sheaf J CommRingCat.{u}, HasDerivedCategory.{w} (scalarModules J B)] in
private theorem telescopeLeg_step (P : CochainComplex (scalarModules J R) ℤ) (n : ℕ) :
    letI := scalarLocalizationCoefficientLinear A R aR
    (t • 𝟙 P) ≫ scalarHomTelescopeLeg J A R aR t P (n + 1) =
      scalarHomTelescopeLeg J A R aR t P n := by
  letI := scalarLocalizationCoefficientLinear A R aR
  simpa only [scalarHomTelescopeDiagram, scalarHomTelescopeLeg,
    Functor.ofSequence_map_homOfLE_succ] using
    colimit.w ((scalarHomTelescopeDiagram A t).obj P) (homOfLE (Nat.le_succ n))


set_option backward.isDefEq.respectTransparency true in
private theorem telescopePresentation_legs
    (T : DerivedCategory (scalarModules J R))
    (P : CochainComplex (scalarModules J R) ℤ) (e : DerivedCategory.Q.obj P ≅ T)
    (n : ℕ) :
    DerivedCategory.Q.map (scalarHomTelescopeLeg J A R aR t P n) ≫
        (telescopeDerivedIso J A R aR t M P ≪≫
          ((M.scalar (ringedLocalizationRingUnit R (aR t))).derived ⋙
            scalarDerivedRestriction (ringedLocalizationRingUnit R (aR t))).mapIso e).hom =
      e.hom ≫ scalarHomTelescopeLambda J A R aR t M T n := by
  letI := scalarLocalizationCoefficientLinear A R aR
  letI := scalarLocalizationDerivedLinear A R aR
  letI : IsIso (t • 𝟙 (((M.scalar (ringedLocalizationRingUnit R (aR t))).derived ⋙
      scalarDerivedRestriction (ringedLocalizationRingUnit R (aR t))).obj T)) :=
    telescopeLocalizedScalar_isIso J A R aR t M T
  let b := telescopeDerivedIso J A R aR t M P ≪≫
    ((M.scalar (ringedLocalizationRingUnit R (aR t))).derived ⋙
      scalarDerivedRestriction (ringedLocalizationRingUnit R (aR t))).mapIso e
  change DerivedCategory.Q.map _ ≫ b.hom = _
  apply scalar_sequence_eq t
    (fun n ↦ DerivedCategory.Q.map (scalarHomTelescopeLeg J A R aR t P n) ≫ b.hom)
    (fun n ↦ e.hom ≫ scalarHomTelescopeLambda J A R aR t M T n) ?_ ?_ ?_ n
  · intro n
    have hq : DerivedCategory.Q.map (t • 𝟙 P) =
        t • 𝟙 (DerivedCategory.Q.obj P) := by
      rw [Functor.map_smul, Functor.map_id]
    have hh := congrArg DerivedCategory.Q.map (telescopeLeg_step J A R aR t P n)
    rw [DerivedCategory.Q.map_comp, hq] at hh
    exact (Category.assoc _ _ _).symm.trans (congrArg (fun f ↦ f ≫ b.hom) hh)
  · intro n
    calc
      _ = e.hom ≫ (t • 𝟙 T) ≫
          scalarHomTelescopeLambda J A R aR t M T (n + 1) := by
        simp only [Linear.smul_comp, Linear.comp_smul, Category.id_comp]
      _ = _ := by rw [telescopeLambda_step]
  · dsimp only [b, Iso.trans_hom, Functor.mapIso_hom, Functor.comp_map]
    rw [← Category.assoc, telescopeDerivedIso_zero]
    simp only [scalarHomTelescopeLambda, pow_zero, one_smul, Functor.map_id]
    exact ((M.scalar (ringedLocalizationRingUnit R (aR t))).adjunction.unit.naturality
      e.hom).symm.trans (congrArg (fun f ↦ e.hom ≫ f) (Category.comp_id _).symm)

set_option backward.isDefEq.respectTransparency true in
private def telescopePresentation (T : DerivedCategory (scalarModules J R)) :
    ScalarHomTelescopePresentation J A R aR t M T where
  iso P e := telescopeDerivedIso J A R aR t M P ≪≫
    ((M.scalar (ringedLocalizationRingUnit R (aR t))).derived ⋙
      scalarDerivedRestriction (ringedLocalizationRingUnit R (aR t))).mapIso e
  legs P e n := telescopePresentation_legs J A R aR t M T P e n
  change P P' f _hf e e' he := by
    letI := scalarLocalizationCoefficientLinear A R aR
    apply telescopeHom_ext_zero J A R aR t M P T
    have hn : scalarHomTelescopeLeg J A R aR t P 0 ≫
        (scalarHomTelescope J A R aR t).map f =
      f ≫ scalarHomTelescopeLeg J A R aR t P' 0 := telescopeLeg_map t f 0
    have hq := congrArg DerivedCategory.Q.map hn
    rw [DerivedCategory.Q.map_comp, DerivedCategory.Q.map_comp] at hq
    exact zero_leg_square hq
      (telescopePresentation_legs J A R aR t M T P e 0)
      (telescopePresentation_legs J A R aR t M T P' e' 0) he

attribute [local irreducible] telescopePresentation


set_option backward.isDefEq.respectTransparency true in
private theorem telescopeHom_scalar (K T : DerivedCategory (scalarModules J R)) :
    letI := scalarLocalizationDerivedLinear A R aR
    (derivedInternalHomOfUniverses.{u, u, u, w} J R).map
        (Prod.mkHom (𝟙 (op K)) (t • 𝟙 T)) =
      t • 𝟙 ((derivedInternalHomOfUniverses.{u, u, u, w} J R).obj (op K, T)) := by
  letI := scalarLocalizationCoefficientLinear A R aR
  letI := scalarLocalizationDerivedLinear A R aR
  let F := (Functor.curry.obj (derivedInternalHomOfUniverses.{u, u, u, w} J R)).obj (op K)
  have hs (P : CochainComplex (scalarModules J R) ℤ) :
      localizationComplexScalar.{u, u, u} R (aR t) P = t • 𝟙 P := by
    apply HomologicalComplex.hom_ext
    intro i
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro V
    apply ModuleCat.hom_ext
    ext x
    rfl
  have hQ (P : CochainComplex (scalarModules J R) ℤ) :
      F.map (t • 𝟙 (DerivedCategory.Q.obj P)) =
        t • 𝟙 (F.obj (DerivedCategory.Q.obj P)) := by
    let e := localizationHomResolutionIso.{u, u, u, w} R K P
    have hn := localizationHomResolutionIso_naturality.{u, u, u, w} R K
      (localizationComplexScalar.{u, u, u} R (aR t) P)
    have hq (P' : CochainComplex (scalarModules J R) ℤ) :
        DerivedCategory.Q.map (t • 𝟙 P') = t • 𝟙 (DerivedCategory.Q.obj P') := by
      rw [Functor.map_smul, Functor.map_id]
    have ht := (congrArg DerivedCategory.Q.map (hs P)).trans (hq P)
    have hΓ := (localizationHomComplex_transition.{u, u, u, w} R (aR t) K P).trans
      ((congrArg DerivedCategory.Q.map (hs _)).trans (hq _))
    exact scalar_of_comparison F e t _ _ ht hΓ hn
  exact map_scalar_of_iso F (DerivedCategory.Q.objObjPreimageIso T) t t (hQ _)

variable
  (μ : ∀ {B D : Sheaf J CommRingCat.{u}} (f : B ⟶ D), ScalarHomTensorComparison.{u, u, u, w} M f)
  (α : ScalarInternalHomAdjunction.{u, u, u, w} M μ) (K L : DerivedCategory (scalarModules J R))

set_option backward.isDefEq.respectTransparency true in
private theorem telescopeLambda_comparison
    (hK : HasLocalizationHomContinuity.{u, u, u, w} J R K)
    (hL : ∃ n : ℤ, L.IsGE n) (n : ℕ) :
    scalarHomTelescopeLambda J A R aR t M
        ((derivedInternalHomOfUniverses.{u, u, u, w} J R).obj (op K, L)) n ≫
      localizationHomRestrictedComparison M (ringedLocalizationRingUnit R (aR t)) μ α K L =
        (derivedInternalHomOfUniverses.{u, u, u, w} J R).map
          (Prod.mkHom (𝟙 (op K)) (scalarHomTelescopeLambda J A R aR t M L n)) := by
  letI := scalarLocalizationDerivedLinear A R aR
  let H := derivedInternalHomOfUniverses.{u, u, u, w} J R
  let F := (Functor.curry.obj H).obj (op K)
  letI hs := telescopeLocalizedScalar_isIso J A R aR t M L
  letI hFs : IsIso (t • 𝟙 (F.obj
      ((scalarDerivedRestriction (ringedLocalizationRingUnit R (aR t))).obj
        ((M.scalar (ringedLocalizationRingUnit R (aR t))).derived.obj L)))) := by
    change IsIso (t • 𝟙 ((derivedInternalHomOfUniverses.{u, u, u, w} J R).obj
      (op K, (scalarDerivedRestriction (ringedLocalizationRingUnit R (aR t))).obj
        ((M.scalar (ringedLocalizationRingUnit R (aR t))).derived.obj L))))
    rw [← telescopeHom_scalar J A R aR t K]
    change IsIso (F.map _)
    infer_instance
  letI : IsIso (t • 𝟙 (H.obj (op K,
      (scalarDerivedRestriction (ringedLocalizationRingUnit R (aR t))).obj
        ((M.scalar (ringedLocalizationRingUnit R (aR t))).derived.obj L)))) := hFs
  apply scalar_sequence_eq t
    (fun n ↦ scalarHomTelescopeLambda J A R aR t M (H.obj (op K, L)) n ≫
      localizationHomRestrictedComparison M (ringedLocalizationRingUnit R (aR t)) μ α K L)
    (fun n ↦ F.map (scalarHomTelescopeLambda J A R aR t M L n)) ?_ ?_ ?_ n
  · intro n
    rw [← Category.assoc, telescopeLambda_step]
  · intro n
    have ht := telescopeHom_scalar J A R aR t K L
    change F.map (t • 𝟙 L) = t • 𝟙 (F.obj L) at ht
    change (t • 𝟙 (F.obj L)) ≫ F.map _ = _
    exact (congrArg (fun f ↦ f ≫ F.map
      (scalarHomTelescopeLambda J A R aR t M L (n + 1))) ht.symm).trans
      ((F.map_comp _ _).symm.trans
        (congrArg F.map (telescopeLambda_step J A R aR t M L n)))
  · have hz (T : DerivedCategory (scalarModules J R)) :
        scalarHomTelescopeLambda J A R aR t M T 0 =
          (M.scalar (ringedLocalizationRingUnit R (aR t))).adjunction.unit.app T := by
      dsimp only [scalarHomTelescopeLambda]
      simp only [pow_zero, one_smul, Functor.map_id]
      exact Category.comp_id _
    rw [hz, hz]
    exact (internalHom_localization_comparison M R (aR t) μ α K L hK hL).2.2.1

/-- The actual evaluation-induced continuity arrow transported through beta_H and beta_L.
Its middle arrow is the restriction of extended evaluation followed by the normalized
scalar-Hom adjunction, rather than an unspecified map with the same source and target.
Source: Bhatt--Scholze 6.8.14(2), representative-normalized telescope square
(blueprint: lem-sfb-scalar-hom-telescope-evaluation). -/
def scalarHomTelescopeGamma
    (βH : ScalarHomTelescopePresentation J A R aR t M
      ((derivedInternalHomOfUniverses.{u, u, u, w} J R).obj (op K, L)))
    (βL : ScalarHomTelescopePresentation J A R aR t M L)
    (PH PL : CochainComplex (scalarModules J R) ℤ)
    (eH : DerivedCategory.Q.obj PH ≅
      (derivedInternalHomOfUniverses.{u, u, u, w} J R).obj (op K, L))
    (eL : DerivedCategory.Q.obj PL ≅ L) :
    DerivedCategory.Q.obj ((scalarHomTelescope J A R aR t).obj PH) ⟶
      (derivedInternalHomOfUniverses.{u, u, u, w} J R).obj
        (op K, DerivedCategory.Q.obj ((scalarHomTelescope J A R aR t).obj PL)) :=
  (βH.iso PH eH).hom ≫
    localizationHomRestrictedComparison M (ringedLocalizationRingUnit R (aR t)) μ α K L ≫
      (derivedInternalHomOfUniverses.{u, u, u, w} J R).map
        (Prod.mkHom (𝟙 (op K)) (βL.iso PL eL).inv)

/-- Scalar-localization internal Hom preserves every telescope leg and evaluation.
The two presentations supply beta_H and beta_L for every pair of representatives;
the explicitly defined gamma is invertible, satisfies both displayed squares, and
commutes with quasi-isomorphic changes of both representatives. Its definition fixes
it to the actual evaluation-induced comparison. The final formula includes n = 0.

Source: Bhatt--Scholze, Lemma 6.8.12 and Proposition 6.8.14(2), pp. 61--62;
Stacks Project, Tags 015F, 06YS, 06YY, 07A6, 03CY, 03EK and 00CM
(blueprint: lem-sfb-scalar-hom-telescope-evaluation).

Proof:
1. Scalar localization is exact (lem-weil-pbc-scalar-localization-sheaf-exact), as is
restriction (lem-pur-sheaf-ring-derived-coefficient-adjunction). Apply
lem-weil-pbc-exact-functor-derived-functor to compute their derived functors on
all complexes. Resolve by a flat-term K-flat complex (lem-pc-kflat-resolution);
the normalized unit there and naturality identify the unit on every complex.
2. Apply lem-weil-pbc-scalar-localization-complex-colimit and transport its cocone
to the chosen colimit. Its stage-n formula is t^(-n) times the ordinary unit.
Localize; lem-weil-pbc-scalar-localization-unit-factors identifies the same formula
with lambda_n. The complex-colimit universal property gives naturality for chain maps.
3. Apply lem-sfb-internal-hom-localization-comparison using precisely hK and hL.
It makes the specified evaluation transpose chi, hence its restricted comparison
rho under lem-sfb-dc-hom-scalar-adjunction, invertible. Only this step uses hL.
4. Transpose rho eta_H using lem-sf-ringed-derived-closed-symmetric-monoidal.
The evaluation normalization (def-coef-ringed-tensor-hom-model) and scalar-unit
normalization identify its transpose with evaluation followed by eta_L.
Thus rho eta_H = H(K, eta_L).
5. Bilinearity of evaluation identifies its scalar action with H(K, t).
Multiplication by t is invertible after localization. Every morphism commuting
with t also commutes with its inverse, so rho lambda_n(H) = H(K, lambda_n(L)).
Evaluation naturality gives the final equality, including n = 0.
6. For each e_T define beta_T as the canonical telescope identification followed
by UF(e_T). Unit naturality proves all its leg formulas. Define gamma by beta_H,
rho and H(K, beta_L inverse), exactly as scalarHomTelescopeGamma. Step 3 gives
invertibility; cancellation gives its first square. Step 5 and the beta_L leg
formula give its second square at every n.
7. Naturality of the complex-colimit construction gives the beta change formulas.
Substitute these into the defining formula for gamma; functoriality gives its
change-of-representatives square. Invert quasi-isomorphisms and compose to cover
zigzags. The comparison theorem in step 3 identifies this actual arrow with the
evaluation-induced continuity map. No termwise bound on PH or PL is used. -/
theorem scalarHom_telescope_evaluation
    (_hK : HasLocalizationHomContinuity.{u, u, u, w} J R K)
    (_hL : ∃ n : ℤ, L.IsGE n) :
    ∃ (βH : ScalarHomTelescopePresentation J A R aR t M
        ((derivedInternalHomOfUniverses.{u, u, u, w} J R).obj (op K, L)))
      (βL : ScalarHomTelescopePresentation J A R aR t M L),
      (∀ (PH PL : CochainComplex (scalarModules J R) ℤ)
        (eH : DerivedCategory.Q.obj PH ≅
          (derivedInternalHomOfUniverses.{u, u, u, w} J R).obj (op K, L))
        (eL : DerivedCategory.Q.obj PL ≅ L),
        IsIso (scalarHomTelescopeGamma J A R aR t M μ α K L βH βL PH PL eH eL) ∧
        scalarHomTelescopeGamma J A R aR t M μ α K L βH βL PH PL eH eL ≫
            (derivedInternalHomOfUniverses.{u, u, u, w} J R).map
              (Prod.mkHom (𝟙 (op K)) (βL.iso PL eL).hom) =
          (βH.iso PH eH).hom ≫ localizationHomRestrictedComparison M
            (ringedLocalizationRingUnit R (aR t)) μ α K L ∧
        ∀ n : ℕ,
          DerivedCategory.Q.map (scalarHomTelescopeLeg J A R aR t PH n) ≫
              scalarHomTelescopeGamma J A R aR t M μ α K L βH βL PH PL eH eL =
            eH.hom ≫ (derivedInternalHomOfUniverses.{u, u, u, w} J R).map
              (Prod.mkHom (𝟙 (op K))
                (eL.inv ≫ DerivedCategory.Q.map (scalarHomTelescopeLeg J A R aR t PL n)))) ∧
      (∀ (PH PL PH' PL' : CochainComplex (scalarModules J R) ℤ)
        (fH : PH ⟶ PH') (fL : PL ⟶ PL') (_hfH : QuasiIso fH) (_hfL : QuasiIso fL)
        (eH : DerivedCategory.Q.obj PH ≅
          (derivedInternalHomOfUniverses.{u, u, u, w} J R).obj (op K, L))
        (eH' : DerivedCategory.Q.obj PH' ≅
          (derivedInternalHomOfUniverses.{u, u, u, w} J R).obj (op K, L))
        (eL : DerivedCategory.Q.obj PL ≅ L) (eL' : DerivedCategory.Q.obj PL' ≅ L),
        DerivedCategory.Q.map fH ≫ eH'.hom = eH.hom →
        DerivedCategory.Q.map fL ≫ eL'.hom = eL.hom →
        DerivedCategory.Q.map ((scalarHomTelescope J A R aR t).map fH) ≫
            scalarHomTelescopeGamma J A R aR t M μ α K L βH βL PH' PL' eH' eL' =
          scalarHomTelescopeGamma J A R aR t M μ α K L βH βL PH PL eH eL ≫
            (derivedInternalHomOfUniverses.{u, u, u, w} J R).map
              (Prod.mkHom (𝟙 (op K))
                (DerivedCategory.Q.map ((scalarHomTelescope J A R aR t).map fL)))) ∧
      ∀ n : ℕ,
        (M.closed R).tensor.map (Prod.mkHom
            (scalarHomTelescopeLambda J A R aR t M
                ((derivedInternalHomOfUniverses.{u, u, u, w} J R).obj (op K, L)) n ≫
              localizationHomRestrictedComparison M
                (ringedLocalizationRingUnit R (aR t)) μ α K L) (𝟙 K)) ≫
            (M.closed R).evaluation K
              ((scalarDerivedRestriction (ringedLocalizationRingUnit R (aR t))).obj
                ((M.scalar (ringedLocalizationRingUnit R (aR t))).derived.obj L)) =
          (M.closed R).evaluation K L ≫ scalarHomTelescopeLambda J A R aR t M L n := by
  let H := derivedInternalHomOfUniverses.{u, u, u, w} J R
  let F := (Functor.curry.obj H).obj (op K)
  let βH := telescopePresentation J A R aR t M (H.obj (op K, L))
  let βL := telescopePresentation J A R aR t M L
  letI hρ : IsIso (localizationHomRestrictedComparison M
      (ringedLocalizationRingUnit R (aR t)) μ α K L) :=
    (internalHom_localization_comparison M R (aR t) μ α K L _hK _hL).2.1
  refine ⟨βH, βL, ?_, ?_, ?_⟩
  · intro PH PL eH eL
    refine ⟨?_, ?_, ?_⟩
    · dsimp only [scalarHomTelescopeGamma]
      letI : IsIso ((derivedInternalHomOfUniverses.{u, u, u, w} J R).map
          (Prod.mkHom (𝟙 (op K)) (βL.iso PL eL).inv)) := by
        change IsIso (F.map (βL.iso PL eL).inv)
        infer_instance
      infer_instance
    · change ((βH.iso PH eH).hom ≫
        localizationHomRestrictedComparison M (ringedLocalizationRingUnit R (aR t)) μ α K L ≫
          F.map (βL.iso PL eL).inv) ≫ F.map (βL.iso PL eL).hom = _
      simp only [Category.assoc, ← F.map_comp, Iso.inv_hom_id, F.map_id]
      exact congrArg (fun k ↦ (βH.iso PH eH).hom ≫ k) (Category.comp_id _)
    · intro n
      change DerivedCategory.Q.map _ ≫ ((βH.iso PH eH).hom ≫
        localizationHomRestrictedComparison M (ringedLocalizationRingUnit R (aR t)) μ α K L ≫
          F.map (βL.iso PL eL).inv) = _
      exact gamma_leg F _ _ eH eL _ _ _ _ _
        (βH.legs PH eH n) (βL.legs PL eL n)
        (telescopeLambda_comparison J A R aR t M μ α K L _hK _hL n)
  · intro PH PL PH' PL' fH fL hfH hfL eH eH' eL eL' heH heL
    change DerivedCategory.Q.map _ ≫ ((βH.iso PH' eH').hom ≫
        localizationHomRestrictedComparison M (ringedLocalizationRingUnit R (aR t)) μ α K L ≫
          F.map (βL.iso PL' eL').inv) =
      ((βH.iso PH eH).hom ≫
        localizationHomRestrictedComparison M (ringedLocalizationRingUnit R (aR t)) μ α K L ≫
          F.map (βL.iso PL eL).inv) ≫ F.map _
    exact gamma_change F _ _ _ _ _ _ _
      (βH.change PH PH' fH hfH eH eH' heH) (βL.change PL PL' fL hfL eL eL' heL)
  · intro n
    rw [telescopeLambda_comparison J A R aR t M μ α K L _hK _hL n]
    exact closed_evaluation_naturality (M.closed R) K
      (scalarHomTelescopeLambda J A R aR t M L n)


end CategoryTheory
