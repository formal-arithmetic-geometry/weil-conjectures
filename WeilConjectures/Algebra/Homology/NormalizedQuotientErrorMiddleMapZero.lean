/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Category.Ring.Sheaf.PrincipalPowerQuotients
public import WeilConjectures.Algebra.Homology.NormalizedQuotientErrorBasic
import WeilConjectures.CategoryTheory.SystemScalarGenerators
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.Algebra.Category.Ring.Colimits

/-! # Normalized quotient error helper

Source: blueprint sk-lem-sp-tower proof, paragraph 2; Stacks 03CZ and 03EK.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option linter.unusedSectionVars false
universe u v r
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open SheafOfModules.RegularQuotientCone
namespace SheafOfModules.NormalizedQuotientError
variable {S : Type u} [Category.{v} S] {J : GrothendieckTopology S}
  [EssentiallySmall.{r} S]
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify J AddCommGrpCat.{r}]

private instance quotientLocallyBijectiveCommRing :
    J.WEqualsLocallyBijective CommRingCat.{r} := by
  let : PreservesFilteredColimitsOfSize.{r, r}
      (CategoryTheory.forget CommRingCat.{r}) := preservesFilteredColimitsOfSize_shrink _
  exact GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall J

private theorem quotientProjection_locallySurjective (R : Sheaf J CommRingCat.{r})
    [HasSheafify J CommRingCat.{r}]
    (t : (R.obj ⋙ CategoryTheory.forget CommRingCat.{r}).sections) (n : ℕ) :
    Presheaf.IsLocallySurjective J
      (((sheafCompose J (forget₂ CommRingCat RingCat)).map
        (principalPowerRingProjection R t n)).hom) := by
  have : Presheaf.IsLocallySurjective J (sectionPowerQuotientProjection R t n) := by
    apply Presheaf.isLocallySurjective_of_surjective
    intro U
    exact Ideal.Quotient.mk_surjective
  unfold principalPowerRingProjection principalPowerRingQuotient
  apply (Presheaf.isLocallySurjective_iff_whisker_forget J _).2
  change Presheaf.IsLocallySurjective J (Functor.whiskerRight
    (sectionPowerQuotientProjection R t n ≫
      toSheafify J (sectionPowerQuotientPresheaf R t n)) (CategoryTheory.forget CommRingCat))
  infer_instance

private theorem restriction_full {R T : Sheaf J CommRingCat.{r}} (a : R ⟶ T)
    [Presheaf.IsLocallySurjective J
      (((sheafCompose J (forget₂ CommRingCat RingCat)).map a).hom)] :
    (restriction a).Full where
  map_surjective {M N} g := by
    let e := PresheafOfModules.restrictHomEquivOfIsLocallySurjective
      (J := J) (M₁ := M.val)
      (((sheafCompose J (forget₂ CommRingCat RingCat)).map a).hom) N.isSheaf
    refine ⟨⟨e.symm g.val⟩, ?_⟩
    apply SheafOfModules.hom_ext
    exact e.apply_symm_apply g.val

attribute [local instance] isMonoidal_W_independentCoefficients monoidalCategory
  preservesZeroMorphisms_curriedTensor_independentCoefficients
  preservesZeroMorphisms_curriedTensor_obj_independentCoefficients

private theorem minusGenerator_augmentation (R : Sheaf J CommRingCat.{r})
    (t : (unit (derivedChangeRingIndependentCoefficients J R)).sections)
    (m : ℕ) (P : CochainComplex (Modules R) ℤ)
    (Q : CochainComplex (Modules R) ℤ) (b : principalKoszul R t m ⟶ Q)
    (hb : (CochainComplex.mappingCone.inl (principalKoszulScalarComplex R t m)).v
      0 (-1) (by decide) ≫ b.f (-1) = 0) (i : ℤ) :
    minusGenerator R t m P i ≫ ((koszulTensorFunctor R P).map b).f i = 0 := by
  change minusGenerator R t m P i ≫
    (HomologicalComplex.mapBifunctorMap b (𝟙 P)
      (MonoidalCategory.curriedTensor (Modules R)) (.up ℤ)).f i = 0
  dsimp only [minusGenerator]
  simp only [Category.assoc]
  rw [HomologicalComplex.ι_mapBifunctorMap]
  dsimp only [HomologicalComplex.id_f, MonoidalCategory.curriedTensor_map_app,
    MonoidalCategory.curriedTensor_obj_map]
  simp only [MonoidalCategory.whiskerLeft_id]
  erw [← MonoidalCategory.comp_whiskerRight_assoc]
  simp only [Category.assoc, hb, comp_zero]
  have hz : MonoidalCategory.whiskerRight
      (0 : unit (derivedChangeRingIndependentCoefficients J R) ⟶ Q.X (-1))
      (P.X (i + 1)) = 0 := by
    exact congrArg (fun f ↦ f.app (P.X (i + 1)))
      ((MonoidalCategory.curriedTensor (Modules R)).map_zero
        (unit (derivedChangeRingIndependentCoefficients J R)) (Q.X (-1)))
  erw [hz, zero_comp, comp_zero]

/-- The canonical middle component is killed by the quotient augmentation.
Source: blueprint sk-lem-sp-tower proof, paragraph 2; Stacks 03CZ and 03EK.
(blueprint: lem-sp-normalized-quotient-error-map-middle-zero)

Proof: by `ε_eq`, at level n the composite with `(M.ν n).hom` is the quotient
augmentation tensored with `P_(m+n)`, followed by `M.μ n`. By `hα`, the composite of `α`
with the augmentation sends the transported unit tensor of x to the augmentation of
`minusGenerator (t^n x)`, i.e. of the degree -1 Koszul summand, which is zero by
`augmentation_inl`. The unit tensors `1 ⊗ x` generate the scalar extension locally as a
`B_m`-module, and `R → B_m` is locally surjective (by `q`, `hq`), so an `R`-linear map of
sheaves vanishing on them vanishes; degreewise and levelwise vanishing reassemble into
the morphism identity.
-/
theorem errorComparisonMiddleMap_comp_epsilon_zero (R : Sheaf J CommRingCat.{r})
    [HasSheafify J CommRingCat.{r}]
    (t : (unit (derivedChangeRingIndependentCoefficients J R)).sections)
    (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{r})
    (a : (Functor.const ℕᵒᵖ).obj R ⟶ B)
    (q : ∀ n : ℕ, B.obj (op n) ≅
      principalPowerRingQuotient R (ringSection R t) (n + 1))
    (hq : ∀ n : ℕ, a.app (op n) ≫ (q n).hom =
      principalPowerRingProjection R (ringSection R t) (n + 1))
    (A : SystemScalarAssignment (J := J))
    (P : CochainComplex (StrictRingSystem B) ℤ) (m : ℕ)
    (M : QuotientModel R t B a A P m)
    (α : shiftedTwist R t M.V ⟶ middle R t m (representative R B a P))
    (hα : ∀ (n : ℕ) (i : ℤ) (U : Sᵒᵖ)
      (x : ((restrictedLevel R B a P (m + n)).X (i + 1)).val.obj U),
      ((((α).f i).app (op n)).val.app U
        (((CochainComplex.shiftFunctorObjXIso ((towerView R M.V).obj (op n))
          (1 : ℤ) i (i + 1) rfl).inv).val.app U
          (((M.ν n).inv.f (i + 1)).val.app U
            (systemModelTmul (A (B.map (homOfLE (Nat.le_add_right m n)).op)).model
              ((level B P (m + n)).X (i + 1)) U 1 x)))) =
        (minusGenerator R t m (restrictedLevel R B a P (m + n)) i).val.app U
          (((endoPow ((complexScalar R t).app (restrictedLevel R B a P (m + n))) n).f
            (i + 1)).val.app U x)) :
    α ≫ M.ε = 0 := by
  have ha : a.app (op m) =
      principalPowerRingProjection R (ringSection R t) (m + 1) ≫ (q m).inv := by
    rw [← hq m, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have : Presheaf.IsLocallySurjective J
      (((sheafCompose J (forget₂ CommRingCat RingCat)).map (a.app (op m))).hom) := by
    rw [ha]
    have := quotientProjection_locallySurjective R (ringSection R t) (m + 1)
    change Presheaf.IsLocallySurjective J
      ((((sheafCompose J (forget₂ CommRingCat RingCat)).map
        (principalPowerRingProjection R (ringSection R t) (m + 1))) ≫
        ((sheafCompose J (forget₂ CommRingCat RingCat)).map (q m).inv)).hom)
    infer_instance
  let F := restriction (a.app (op m))
  have : F.Full := restriction_full (a.app (op m))
  apply HomologicalComplex.hom_ext
  intro i
  apply NatTrans.ext
  funext n
  obtain ⟨n⟩ := n
  let s := CochainComplex.shiftFunctorObjXIso ((towerView R M.V).obj (op n))
    (1 : ℤ) i (i + 1) rfl
  let e := s ≪≫ (HomologicalComplex.eval (Modules R) (.up ℤ) (i + 1)).mapIso (M.ν n)
  let g := e.inv ≫ (α.f i).app (op n) ≫ (M.ε.f i).app (op n) ≫ (M.ν n).hom.f i
  have hg : g = 0 := by
    obtain ⟨g', hg'⟩ := F.map_surjective g
    have hz : g' = 0 := by
      apply systemScalarModel_hom_ext (A (B.map (homOfLE (Nat.le_add_right m n)).op))
      intro U x
      have hgx := congrArg (fun f ↦ f.val.app U
        (systemModelTmul (A (B.map (homOfLE (Nat.le_add_right m n)).op)).model
          ((level B P (m + n)).X (i + 1)) U 1 x)) hg'
      change g'.val.app U _ = 0
      erw [hgx]
      change ((M.ν n).hom.f i).val.app U
        (((M.ε.f i).app (op n)).val.app U
          (((α.f i).app (op n)).val.app U
            (s.inv.val.app U (((M.ν n).inv.f (i + 1)).val.app U _)))) = 0
      rw [hα n i U x]
      have he := congrArg (fun f ↦ (f.f i).val.app U
        ((minusGenerator R t m (restrictedLevel R B a P (m + n)) i).val.app U
          (((endoPow ((complexScalar R t).app
            (restrictedLevel R B a P (m + n))) n).f (i + 1)).val.app U x)))
        (M.ε_eq n)
      erw [he]
      have hz := minusGenerator_augmentation R t m (restrictedLevel R B a P (m + n))
        _ M.augmentation M.augmentation_inl i
      have hx := congrArg (fun f ↦ f.val.app U
        (((endoPow ((complexScalar R t).app
          (restrictedLevel R B a P (m + n))) n).f (i + 1)).val.app U x)) hz
      change ((M.μ n).hom.f i).val.app U _ = 0
      erw [hx]
      exact map_zero _
    rw [← hg', hz, F.map_zero]
  apply (cancel_epi e.inv).1
  apply (cancel_mono ((M.ν n).hom.f i)).1
  simpa only [g, HomologicalComplex.comp_f, NatTrans.comp_app, HomologicalComplex.zero_f,
    NatTrans.app_zero, comp_zero, zero_comp, Category.assoc] using hg

end SheafOfModules.NormalizedQuotientError
