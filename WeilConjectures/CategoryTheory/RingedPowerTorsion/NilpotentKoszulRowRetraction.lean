/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.Algebra.Homology.BifunctorShift
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.CategoryTheory.PrincipalQuotientCompletion.PrincipalQuotientCompletionModel
public import WeilConjectures.Algebra.Homology.RegularQuotientCone.RegularQuotientConeBasic
public import WeilConjectures.Algebra.Homology.SixFunctors.OrdinaryDerivedChangeOfRings
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import Mathlib.CategoryTheory.Endomorphism
import Mathlib.CategoryTheory.Preadditive.Basic
import Mathlib.RingTheory.Nilpotent.Basic
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import all WeilConjectures.CategoryTheory.PrincipalQuotientCompletion.FiniteFreeQuotientRoosComparison
import all WeilConjectures.CategoryTheory.Principal.PrincipalConeKoszulRoosComparison
import WeilConjectures.Algebra.Homology.PrincipalCone.PrincipalConeTower
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.Algebra.Homology.KernelShiftedMappingCone
import WeilConjectures.Algebra.Homology.RoosSplitComparison
import WeilConjectures.CategoryTheory.RoosConeCalculus.RoosConeCalculus

/-! # Nilpotent rows in the strict principal Koszul tower

Source: Bhatt--Scholze, Lemma 3.4.9 and the proof of Lemma 3.5.7.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u v r w a b

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite

namespace CategoryTheory.RingedPowerTorsion

private def zeroConeSnd {B : Type a} [Category.{b} B] [Abelian B]
    (X Y : CochainComplex B ℤ) : CochainComplex.mappingCone (0 : X ⟶ Y) ⟶ Y where
  f k := (CochainComplex.mappingCone.snd (0 : X ⟶ Y)).v k k (add_zero k)
  comm' k l h := by
    obtain rfl : l = k + 1 := h.symm
    simpa using (CochainComplex.mappingCone.d_snd_v (0 : X ⟶ Y) k (k + 1) rfl).symm

private def zeroConeFst {B : Type a} [Category.{b} B] [Abelian B]
    (X Y : CochainComplex B ℤ) :
    CochainComplex.mappingCone (0 : X ⟶ Y) ⟶ X⟦(1 : ℤ)⟧ :=
  ((CochainComplex.mappingCone.fst (0 : X ⟶ Y)).rightShift 1 0 (by omega)).homOf

private theorem cone_sndX {B : Type a} [Category.{b} B] [Abelian B]
    {X Y : CochainComplex B ℤ} (f : X ⟶ Y) (n m : ℤ) (h : (ComplexShape.up ℤ).Rel n m) :
    HomologicalComplex.homotopyCofiber.sndX f n =
      (HomologicalComplex.homotopyCofiber.XIsoBiprod f n m h).hom ≫ biprod.snd := by
  obtain rfl := (ComplexShape.up ℤ).next_eq' h
  dsimp only [HomologicalComplex.homotopyCofiber.sndX]
  rw [dif_pos h]

private def zeroConeIso {B : Type a} [Category.{b} B] [Abelian B]
    (X Y : CochainComplex B ℤ) :
    CochainComplex.mappingCone (0 : X ⟶ Y) ≅ Y ⊞ X⟦(1 : ℤ)⟧ := by
  let f := biprod.lift (zeroConeSnd X Y) (zeroConeFst X Y)
  let e (k : ℤ) : (CochainComplex.mappingCone (0 : X ⟶ Y)).X k ≅
      (Y ⊞ X⟦(1 : ℤ)⟧).X k :=
    HomologicalComplex.homotopyCofiber.XIsoBiprod (0 : X ⟶ Y) k (k + 1) rfl ≪≫
      biprod.mapIso (X.shiftFunctorObjXIso 1 k (k + 1) rfl).symm (Iso.refl _) ≪≫
      biprod.braiding _ _ ≪≫ (HomologicalComplex.biprodXIso Y (X⟦(1 : ℤ)⟧) k).symm
  have hf (k : ℤ) : f.f k = (e k).hom := by
    apply (cancel_mono (HomologicalComplex.biprodXIso Y (X⟦(1 : ℤ)⟧) k).hom).mp
    apply biprod.hom_ext
    · simp only [Category.assoc, HomologicalComplex.biprodXIso_hom_fst,
        ← HomologicalComplex.comp_f, f, biprod.lift_fst]
      simp only [zeroConeSnd, CochainComplex.mappingCone.snd,
        CochainComplex.HomComplex.Cochain.ofHoms_v,
        cone_sndX (0 : X ⟶ Y) k (k + 1) rfl, CochainComplex.shiftFunctorObjXIso,
        HomologicalComplex.XIsoOfEq_rfl, CochainComplex.shiftFunctor_obj_X',
        Iso.trans_hom, biprod.mapIso_hom, Iso.symm_hom, Iso.refl_inv, Iso.refl_hom,
        biprod.braiding_hom, Category.assoc, Iso.cancel_iso_hom_left, e]
      rw [← HomologicalComplex.biprodXIso_hom_fst, Iso.inv_hom_id_assoc]
      erw [biprod.lift_fst]
      simpa only [Category.comp_id] using!
        (biprod.map_snd (𝟙 (X.X (k + 1))) (𝟙 (Y.X k))).symm
    · simp only [Category.assoc, HomologicalComplex.biprodXIso_hom_snd,
        ← HomologicalComplex.comp_f, f, biprod.lift_snd]
      simp only [CochainComplex.shiftFunctor_obj_X', zeroConeFst,
        CochainComplex.HomComplex.Cocycle.homOf, CochainComplex.mappingCone.fst,
        HomologicalComplex.homotopyCofiber.fstX,
        CochainComplex.HomComplex.Cocycle.rightShift_coe,
        CochainComplex.HomComplex.Cocycle.mk_coe,
        CochainComplex.HomComplex.Cochain.rightShift_v,
        CochainComplex.HomComplex.Cochain.mk_v, CochainComplex.shiftFunctorObjXIso,
        HomologicalComplex.XIsoOfEq_rfl, Iso.refl_inv, Category.comp_id, Iso.trans_hom,
        biprod.mapIso_hom, Iso.symm_hom, Iso.refl_hom, biprod.braiding_hom,
        Category.assoc, Iso.cancel_iso_hom_left, e]
      rw [← HomologicalComplex.biprodXIso_hom_snd, Iso.inv_hom_id_assoc]
      erw [biprod.lift_snd]
      simpa only [Category.comp_id] using!
        (biprod.map_fst (𝟙 (X.X (k + 1))) (𝟙 (Y.X k))).symm
  have (k : ℤ) : IsIso (f.f k) := by rw [hf]; infer_instance
  have : IsIso f := HomologicalComplex.Hom.isIso_of_components f
  exact asIso f

private theorem zeroConeIso_hom {B : Type a} [Category.{b} B] [Abelian B]
    (X Y : CochainComplex B ℤ) :
    (zeroConeIso X Y).hom = biprod.lift (zeroConeSnd X Y) (zeroConeFst X Y) := rfl

private theorem zeroConeIso_inr {B : Type a} [Category.{b} B] [Abelian B]
    (X Y : CochainComplex B ℤ) :
    CochainComplex.mappingCone.inr (0 : X ⟶ Y) ≫ (zeroConeIso X Y).hom =
      biprod.inl := by
  rw [zeroConeIso_hom]
  apply biprod.hom_ext
  · ext k : 1
    simp only [Category.assoc, biprod.lift_fst, HomologicalComplex.comp_f,
      zeroConeSnd, CochainComplex.mappingCone.inr_f_snd_v, HomologicalComplex.biprod_inl_fst_f]
  · ext k : 1
    simp only [Category.assoc, biprod.lift_snd, HomologicalComplex.comp_f,
      zeroConeFst, CochainComplex.HomComplex.Cocycle.homOf,
      CochainComplex.HomComplex.Cocycle.rightShift_coe,
      CochainComplex.HomComplex.Cochain.rightShift_v, Category.assoc,
      CochainComplex.mappingCone.inr_f_fst_v_assoc, zero_comp,
      HomologicalComplex.biprod_inl_snd_f]

/- The product algebra needed for the row contraction, including both inverse
identities. These calculations apply to complexes as well as module sheaves. -/
variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [HasSheafify J AddCommGrpCat.{r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
  (R : Sheaf J CommRingCat.{r})

set_option hygiene false in
local notation "A" => ringedSiteModules.{r}
  (SheafOfModules.derivedChangeRingIndependentCoefficients J R)

attribute [local instance] SheafOfModules.isMonoidal_W_independentCoefficients
attribute [local instance] SheafOfModules.monoidalCategory
attribute [local instance]
  SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients
attribute [local instance]
  SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients

private def unitTensorIso (P : CochainComplex A ℤ) :
    (((MonoidalCategory.curriedTensor A).map₂CochainComplex).obj
      ((CochainComplex.singleFunctor A 0).obj (SheafOfModules.unit
        (SheafOfModules.derivedChangeRingIndependentCoefficients J R)))).obj P ≅ P :=
  CochainComplex.mapBifunctorSingle₁Iso (MonoidalCategory.curriedTensor A)
      (SheafOfModules.unit (SheafOfModules.derivedChangeRingIndependentCoefficients J R)) P
    ≪≫ (NatIso.mapHomologicalComplex (MonoidalCategory.leftUnitorNatIso A) (.up ℤ)).app P
    ≪≫ (Functor.mapHomologicalComplexIdIso A (.up ℤ)).app P

private theorem unitTensorIso_inv (P : CochainComplex A ℤ) :
    (unitTensorIso R P).inv = koszulTensorUnitInclusion R P := by
  ext i : 1
  simp only [unitTensorIso, Iso.trans_inv, HomologicalComplex.comp_f,
    CochainComplex.mapBifunctorSingle₁Iso_inv_f,
    koszulTensorUnitInclusion, koszulTensorUnitComponent]
  rfl

omit [EssentiallySmall.{r} C] [HasSheafify J AddCommGrpCat.{r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] in
private theorem complexScalar_pow_f (P : CochainComplex A ℤ) (t : (SheafOfModules.unit
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R)).sections)
    (n : ℕ) (a : ℤ) :
    (endoPow ((SheafOfModules.RegularQuotientCone.complexScalar R t).app P) n).f a =
      endoPow ((SheafOfModules.RegularQuotientCone.scalar R t).app (P.X a)) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [endoPow, HomologicalComplex.comp_f, ih]
    rfl

omit [EssentiallySmall.{r} C] [HasSheafify J AddCommGrpCat.{r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] in
private theorem complexScalar_nilpotent (P : CochainComplex A ℤ) (t : (SheafOfModules.unit
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R)).sections)
    (n : ℕ) (hn : ∀ a : ℤ,
      endoPow ((SheafOfModules.RegularQuotientCone.scalar R t).app (P.X a)) n = 0) :
    endoPow ((SheafOfModules.RegularQuotientCone.complexScalar R t).app P) n = 0 := by
  ext a : 1
  exact (complexScalar_pow_f R P t n a).trans (hn a)

set_option maxHeartbeats 1600000 in
-- The fixed tensor inclusions require unfolding the chosen total tensor complex.
private theorem scalar_tensor_conjugacy (P : CochainComplex A ℤ)
    (t : (SheafOfModules.unit
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R)).sections) (n : ℕ) :
    endoPow ((SheafOfModules.RegularQuotientCone.complexScalar R t).app P) n ≫
      (unitTensorIso R P).inv =
    (unitTensorIso R P).inv ≫ (koszulTensorFunctor R P).map
      ((CochainComplex.singleFunctor A 0).map
        (endoPow (globalSectionMultiplication R t) n)) := by
  rw [unitTensorIso_inv R P]
  ext i : 1
  simp only [HomologicalComplex.comp_f, koszulTensorUnitInclusion,
    koszulTensorUnitComponent, koszulTensorFunctor, Functor.flip_obj_map,
    Functor.map₂HomologicalComplex_map_app, Category.assoc]
  erw [HomologicalComplex.ι_mapBifunctorMap]
  simp only [CochainComplex.singleFunctor, CochainComplex.singleFunctors,
    HomologicalComplex.single_map_f_self, HomologicalComplex.id_f,
    curriedTensor_map_app, Functor.map_id, comp_whiskerRight, Category.assoc]
  rw [complexScalar_pow_f R P t n i]
  have hs := CategoryTheory.PrincipalQuotientCompletion.scalar_tensor R t (P.X i) n
  change endoPow ((SheafOfModules.RegularQuotientCone.scalar R t).app (P.X i)) n ≫
    (λ_ (P.X i)).inv =
    (λ_ (P.X i)).inv ≫ (endoPow (globalSectionMultiplication R t) n) ▷ (P.X i) at hs
  erw [← comp_whiskerRight_assoc, Iso.inv_hom_id]
  simp only [id_whiskerRight, Category.id_comp]
  rw [← reassoc_of% hs]

private theorem endoPow_as_pow {B : Type a} [Category.{b} B] {X : B}
    (μ : End X) (n : ℕ) : endoPow μ n = μ ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [endoPow, ih, pow_succ']; rfl


set_option maxHeartbeats 1600000 in
-- The scalar conjugacy is checked against the fixed total-tensor representative.
private def scalarConeIso (P : CochainComplex A ℤ) (t : (SheafOfModules.unit
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R)).sections) (n : ℕ) :
    CochainComplex.mappingCone
        (End.of ((SheafOfModules.RegularQuotientCone.complexScalar R t).app P) ^ (n + 1)) ≅
      (koszulTensorTower R P t).obj (op n) := by
  let G := koszulTensorFunctor R P
  let f := (CochainComplex.singleFunctor A 0).map
    (endoPow (globalSectionMultiplication R t) (n + 1))
  change CochainComplex.mappingCone _ ≅ G.obj (CochainComplex.mappingCone f)
  have h := scalar_tensor_conjugacy R P t (n + 1)
  rw [endoPow_as_pow] at h
  apply functorConeConjugate G _ f (unitTensorIso R P).symm h
  exact genericTensorConeIso (curriedTensor A) P f

set_option maxHeartbeats 1600000 in
-- The inclusion identity converts the same fixed total tensor representative.
private theorem scalarConeIso_inr (P : CochainComplex A ℤ)
    (t : (SheafOfModules.unit
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R)).sections) (n : ℕ) :
    CochainComplex.mappingCone.inr
        (End.of ((SheafOfModules.RegularQuotientCone.complexScalar R t).app P) ^ (n + 1)) ≫
      (scalarConeIso R P t n).hom = koszulRepresentativeAugmentation R P t n := by
  rw [koszulRepresentativeAugmentation, ← unitTensorIso_inv R P]
  unfold scalarConeIso
  apply functorConeConjugate_inr
  exact genericTensorConeIso_inr (curriedTensor A) P _


set_option maxHeartbeats 1600000 in
-- Naturality converts the fixed total-tensor comparison at two adjacent levels.
private theorem scalarConeIso_step (P : CochainComplex A ℤ)
    (t : (SheafOfModules.unit
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R)).sections) (n : ℕ) :
    CochainComplex.PrincipalCone.step
        (End.of ((SheafOfModules.RegularQuotientCone.complexScalar R t).app P)) n ≫
      (scalarConeIso R P t n).hom =
    (scalarConeIso R P t (n + 1)).hom ≫
      (koszulTensorTower R P t).map (homOfLE (Nat.le_succ n)).op := by
  let G := koszulTensorFunctor R P
  let S := CochainComplex.singleFunctor A 0
  let f := S.map (endoPow (globalSectionMultiplication R t) (n + 1 + 1))
  let g := S.map (endoPow (globalSectionMultiplication R t) (n + 1))
  let b := S.map (globalSectionMultiplication R t)
  have ha : (SheafOfModules.RegularQuotientCone.complexScalar R t).app P ≫
      (unitTensorIso R P).inv = (unitTensorIso R P).inv ≫ G.map b := by
    simpa only [endoPow, Category.id_comp] using scalar_tensor_conjugacy R P t 1
  dsimp only [koszulTensorTower, Functor.comp_map, principalKoszulTower]
  rw [Functor.ofOpSequence_map_homOfLE_succ]
  unfold scalarConeIso CochainComplex.PrincipalCone.step
  change _ = _ ≫ G.map (principalKoszulTransition R t n)
  apply functorConeConjugate_natural
  · exact ha
  · have ht := genericTensorConeIso_natural (curriedTensor A) P f g b (𝟙 _)
      (principalKoszul_transition_square R t n) (by
        change G.map f ≫ G.map (𝟙 _) = G.map b ≫ G.map g
        rw [← G.map_comp, ← G.map_comp]
        exact congrArg G.map (principalKoszul_transition_square R t n))
    simpa only [G, koszulTensorFunctor, Functor.map_id] using ht

private theorem zeroConeIso_natural {B : Type a} [Category.{b} B] [Abelian B]
    (P : CochainComplex B ℤ) (μ : P ⟶ P) :
    CochainComplex.mappingCone.map (0 : P ⟶ P) 0 μ (𝟙 P) (by simp) ≫
      (zeroConeIso P P).hom =
    (zeroConeIso P P).hom ≫ biprod.map (𝟙 P) (μ⟦(1 : ℤ)⟧') := by
  apply biprod.hom_ext
  · ext k : 1
    simp only [Category.assoc, zeroConeIso_hom, biprod.lift_fst,
      biprod.map_fst, Category.comp_id, HomologicalComplex.comp_f, zeroConeSnd]
    apply CochainComplex.mappingCone.ext_from (0 : P ⟶ P) (k + 1) k rfl <;>
      simp [CochainComplex.mappingCone.map]
  · ext k : 1
    simp only [Category.assoc, zeroConeIso_hom, biprod.lift_snd, biprod.map_snd,
      HomologicalComplex.comp_f, zeroConeFst,
      CochainComplex.HomComplex.Cocycle.homOf,
      CochainComplex.HomComplex.Cocycle.rightShift_coe,
      CochainComplex.HomComplex.Cochain.rightShift_v]
    apply CochainComplex.mappingCone.ext_from (0 : P ⟶ P) (k + 1) k rfl <;>
      simp [CochainComplex.mappingCone.map, CochainComplex.shiftFunctor_map_f']

private def coneZeroIso {B : Type a} [Category.{b} B] [Abelian B]
    {P : CochainComplex B ℤ} (f : P ⟶ P) (h : f = 0) :
    CochainComplex.mappingCone f ≅ P ⊞ P⟦(1 : ℤ)⟧ :=
  eqToIso (by rw [h]) ≪≫ zeroConeIso P P

private theorem coneZeroIso_inr {B : Type a} [Category.{b} B] [Abelian B]
    {P : CochainComplex B ℤ} (f : P ⟶ P) (h : f = 0) :
    CochainComplex.mappingCone.inr f ≫ (coneZeroIso f h).hom = biprod.inl := by
  subst f
  simpa only [coneZeroIso, Iso.trans_hom, eqToIso_refl, Iso.refl_hom, Category.id_comp] using
    zeroConeIso_inr P P

private theorem coneZeroIso_natural {B : Type a} [Category.{b} B] [Abelian B]
    {P : CochainComplex B ℤ} (f g : P ⟶ P) (hf : f = 0) (hg : g = 0)
    (μ : P ⟶ P) (h : f ≫ 𝟙 P = μ ≫ g) :
    CochainComplex.mappingCone.map f g μ (𝟙 P) h ≫ (coneZeroIso g hg).hom =
      (coneZeroIso f hf).hom ≫ biprod.map (𝟙 P) (μ⟦(1 : ℤ)⟧') := by
  subst f
  subst g
  simpa only [coneZeroIso, Iso.trans_hom, eqToIso_refl, Iso.refl_hom, Category.id_comp] using
    zeroConeIso_natural P μ

private def rowRoosModelIso (T : ℕᵒᵖ ⥤ CochainComplex A ℤ) :
    WeilConjectures.integralOperationsRoos T ≅ (limitComplex R).obj T := Iso.refl _

private theorem rowRoosModelIso_unit (P : CochainComplex A ℤ)
    (T : ℕᵒᵖ ⥤ CochainComplex A ℤ) (γ : (Functor.const ℕᵒᵖ).obj P ⟶ T) :
    normalizedCoconeLift _ (Pi.lift (fun n ↦ γ.app (op n)))
        (towerAugmentationCondition T γ) ≫ (rowRoosModelIso R T).hom =
      roosAugment (X := koszulTowerComplex R T) (fun n ↦ γ.app (op n))
        (fun n ↦ by
          exact (γ.naturality (homOfLE (Nat.le_succ n)).op).symm.trans
            (Category.id_comp (γ.app (op n)))) := by
  dsimp only [rowRoosModelIso, Iso.refl_hom]
  erw [Category.comp_id]
  rfl

attribute [local irreducible] rowRoosModelIso

variable [HasDerivedCategory.{w} (ringedSiteModules.{r}
    (SheafOfModules.derivedChangeRingIndependentCoefficients J R))]
  [HasExactLimitsOfShape (Discrete ℕ) (ringedSiteModules.{r}
    (SheafOfModules.derivedChangeRingIndependentCoefficients J R))]

-- Preserve the existing exact-products binder, although the new proof does not need it.
set_option linter.unusedSectionVars false in
set_option maxHeartbeats 1600000 in
-- The fixed representative signatures require the same budget as their parent theorem.
/-- A nilpotent scalar gives a retraction of the actual Koszul completion unit,
and a compatible splitting of its sufficiently high levels.
Source: Bhatt--Scholze, Lemmas 3.4.9 and 3.5.7; Stacks Tags 08TC and 0941
(blueprint: lem-sp-nilpotent-koszul-row-retraction).

Proof: For j=rP-1+k the exponent j+1 is at least rP, so t^(j+1) acts by zero
on every term of P. The two-term total tensor therefore splits in degree a as
P^a ⊕ P^(a+1). The first-variable tensor--cone isomorphism identifies its
second differential with the usual negative differential of P[1]. This fixes the
splitting, carries the actual Koszul inclusion to biprod.inl, and gives transitions (1,t[1]).
Restrict the strict Roos cone to this tail. Its deleted finite block has a
nilpotent shift; the finite geometric series gives its inverse and a contraction
of its mapping cocone, compatibly with the original augmentation.
For the shifted summand the transition shift S satisfies S^rP=0; hence
1+S+...+S^(rP-1) is an inverse to 1-S, and its Roos cocone is contractible.
For the constant summand, (ev_0,1-S) is an isomorphism from the product to
P ⊕ product, with inverse x_0=u, x_(j+1)=x_j-y_j. Its Roos cocone is P plus
an identity cocone, and its augmentation induces the identity on P. Projection
to this P defines back. It satisfies rowUnit ≫ back = 1 strictly, and the two
contractible summands show rowUnit is a quasi-isomorphism. Localizing the strict
retraction then shows Q(back) is an isomorphism. The proof includes rP=1
(empty deleted block), zero complexes, and unbounded internal degrees. -/
theorem nilpotent_koszul_row_retraction
    (t : (SheafOfModules.unit
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R)).sections)
    (P : CochainComplex (ringedSiteModules.{r}
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R)) ℤ) (rP : ℕ) (hr : 1 ≤ rP)
    (hn : ∀ a : ℤ, endoPow ((SheafOfModules.RegularQuotientCone.scalar R t).app
      (P.X a)) rP = 0) :
    (QuasiIso (rowUnit R t (P)) ∧
          ∃ back : (limitComplex R).obj
              (koszulTensorTower R (P) t) ⟶ P,
            rowUnit R t (P) ≫ back = 𝟙 _ ∧
            IsIso (DerivedCategory.Q.map back)) ∧
    (∃ φ : ∀ k : ℕ,
            (koszulTensorTower R (P) t).obj
                (op (rP - 1 + k)) ≅
              P ⊞ (P)⟦(1 : ℤ)⟧,
          (∀ k : ℕ,
            koszulRepresentativeAugmentation R (P) t
                (rP - 1 + k) ≫ (φ k).hom = biprod.inl) ∧
          (∀ k : ℕ,
            (koszulTensorTower R (P) t).map
                (homOfLE (Nat.le_succ (rP - 1 + k))).op ≫ (φ k).hom =
              (φ (k + 1)).hom ≫ biprod.map (𝟙 _)
                (((SheafOfModules.RegularQuotientCone.complexScalar R t).app
                  (P))⟦(1 : ℤ)⟧'))) := by
  classical
  let μ : End P := (SheafOfModules.RegularQuotientCone.complexScalar R t).app P
  have hμ : μ ^ rP = 0 := by
    simpa only [endoPow_as_pow] using complexScalar_nilpotent R P t rP hn
  have hz (k : ℕ) : μ ^ (rP - 1 + k + 1) = 0 := by
    exact pow_eq_zero_of_le (a := μ) (m := rP) (n := rP - 1 + k + 1) (by omega) hμ
  let φ (k : ℕ) := (scalarConeIso R P t (rP - 1 + k)).symm ≪≫
    coneZeroIso (μ ^ (rP - 1 + k + 1)) (hz k)
  have hi (k : ℕ) : koszulRepresentativeAugmentation R P t (rP - 1 + k) ≫
      (φ k).hom = biprod.inl := by
    rw [← scalarConeIso_inr R P t (rP - 1 + k)]
    simp only [φ, Iso.trans_hom, Iso.symm_hom, Category.assoc,
      Iso.hom_inv_id_assoc]
    exact coneZeroIso_inr _ (hz k)
  have hs (k : ℕ) : (koszulTensorTower R P t).map
      (homOfLE (Nat.le_succ (rP - 1 + k))).op ≫ (φ k).hom =
      (φ (k + 1)).hom ≫ biprod.map (𝟙 P) (μ⟦(1 : ℤ)⟧') := by
    dsimp only [φ]
    apply (cancel_epi (scalarConeIso R P t (rP - 1 + k + 1)).hom).mp
    rw [← Category.assoc, ← scalarConeIso_step R P t (rP - 1 + k)]
    simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc]
    erw [Iso.hom_inv_id_assoc]
    exact coneZeroIso_natural _ _ (hz (k + 1)) (hz k) μ _
  let back : (limitComplex R).obj (koszulTensorTower R P t) ⟶ P :=
    roosEval (koszulTowerComplex R (koszulTensorTower R P t)) (rP - 1) ≫
      (φ 0).hom ≫ biprod.fst
  have hback : rowUnit R t P ≫ back = 𝟙 P := by
    have he : rowUnit R t P ≫
        roosEval (koszulTowerComplex R (koszulTensorTower R P t)) (rP - 1) =
        koszulRepresentativeAugmentation R P t (rP - 1) := by
      change rowUnit R t P ≫
          (CochainComplex.mappingCocone.fst _ ≫ Pi.π _ (rP - 1)) = _
      dsimp only [rowUnit, roosAugment, roosLift]
      rw [← Category.assoc, CochainComplex.mappingCocone.lift_fst]
      exact Pi.lift_π _ _
    dsimp only [back]
    rw [← Category.assoc, ← Category.assoc, he]
    simpa only [Nat.add_zero, biprod.inl_fst] using
      congrArg (fun f ↦ f ≫ biprod.fst) (hi 0)
  have hq : QuasiIso (rowUnit R t P) := by
    let T := koszulTensorTower R P t
    let γ := koszulStrictAugmentation R P t
    obtain ⟨c, hc⟩ := normalizedConeComparison μ T γ (scalarConeIso R P t)
      (scalarConeIso_step R P t) (scalarConeIso_inr R P t)
    have hunit : QuasiIso (CochainComplex.PrincipalCone.unit μ) :=
      quasiIso_principalConeUnit_of_nilpotent P μ rP hμ
    let d := DerivedCategory.Q.mapIso (rowRoosModelIso R T)
    have he : DerivedCategory.Q.map (CochainComplex.PrincipalCone.unit μ) ≫
        (c ≪≫ d).hom = DerivedCategory.Q.map (rowUnit R t P) := by
      dsimp only [Iso.trans_hom, d, Functor.mapIso_hom]
      rw [← Category.assoc, hc, ← Functor.map_comp]
      exact congrArg DerivedCategory.Q.map (rowRoosModelIso_unit R P T γ)
    apply (DerivedCategory.isIso_Q_map_iff_quasiIso A _).mp
    rw [← he]
    infer_instance
  have hbq : IsIso (DerivedCategory.Q.map back) := by
    have := hq
    have he : DerivedCategory.Q.map (rowUnit R t P) ≫
        DerivedCategory.Q.map back = 𝟙 _ := by
      rw [← Functor.map_comp, hback, Functor.map_id]
    have hcomp : IsIso (DerivedCategory.Q.map (rowUnit R t P) ≫
        DerivedCategory.Q.map back) := by
      rw [he]
      infer_instance
    exact IsIso.of_isIso_comp_left (DerivedCategory.Q.map (rowUnit R t P))
      (DerivedCategory.Q.map back)
  exact ⟨⟨hq, back, hback, hbq⟩, φ, hi, hs⟩

end CategoryTheory.RingedPowerTorsion
