/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.RingTheory.Localization.Away.Basic
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
public import Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationIsIso
public import WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationComm
public import WeilConjectures.Algebra.Homology.HomComplexComponents
public import WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationNaturality
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.Algebra.Homology.DerivedInternalHom
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.Algebra.Category.Grp.FilteredColimits
import WeilConjectures.Algebra.Homology.RhomIntoKInjectiveLocal
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.RingTheory.Ideal.Span
import WeilConjectures.CategoryTheory.Ringed.RingedInternalHomExactRestrictionSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import Mathlib.CategoryTheory.Monoidal.Limits.Colimits
import Mathlib.CategoryTheory.Monoidal.Limits.Preserves
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim
import WeilConjectures.Algebra.Homology.HomTensorTotal
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Homology.HomComplex
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import WeilConjectures.Algebra.Homology.KInjectiveHomComplex
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
import WeilConjectures.Algebra.Homology.BoundedAboveFlatSheafKFlat
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Preadditive.Biproducts
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
import Mathlib.Algebra.Module.LocalizedModule.IsLocalization
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Algebra.Exact.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.Algebra.Category.ModuleCat.Presheaf.InternalHom
import WeilConjectures.ProperBaseChange.SliceAwayLocalizationFreeResolution
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import WeilConjectures.Algebra.Homology.HomTensorDegreewise
import WeilConjectures.Algebra.Homology.HomTensorDifferential
import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMap
import WeilConjectures.Algebra.Homology.HomTensorNaturality
import WeilConjectures.Algebra.Category.ModuleCat.Presheaf.SheafificationTensor
import WeilConjectures.Algebra.Category.ModuleCat.Presheaf.SheafificationFlat
import Mathlib.RingTheory.Flat.CategoryTheory
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Localization.BaseChange
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.CategoryTheory.Sites.Abelian
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafSections
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.CategoryTheory.Abelian.Exact
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Free

/-! The unit-to-complete direction of the extended Cech criterion.

Source: Stacks Project, algebraization.tex, Tags 099B and 099F.
(blueprint: lem-weil-pbc-extended-cech-unit-isIso-implies-complete).

Proof: on a finite-generator slice, tensoring the extended Cech complex with the
localization at a generator makes one two-term factor contractible. Tensor-Hom
adjunction and the invertible completion unit therefore force derived Hom from
each generator localization to vanish. The complete-element predicate is a sheaf
of ideals, so local generation and covering descent give the local completeness
predicate for every section of the ideal. The fraction and sequential models
agree by the localization comparison.
-/

@[expose] public section

set_option synthInstance.maxSize 2048

universe u w

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped BigOperators

namespace CategoryTheory

section LocalCalculation

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
  (O : Sheaf J CommRingCat.{u})

private theorem localization_isFlat (R : Sheaf J CommRingCat.{u})
    (g : (R.obj ⋙ forget CommRingCat.{u}).sections) :
    SheafOfModules.IsFlat (ringedSectionLocalization R g) := by
  let O := (sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R
  let F := ringedSectionLocalizationPresheaf R g
  have hflat (V : Cᵒᵖ) : Module.Flat (R.obj.obj V) (F.obj V) := by
    dsimp [F, ringedSectionLocalizationPresheaf, ringedSectionLocalizationCarrier]
    infer_instance
  have hF : PreservesFiniteLimits (tensorRight F) := by
    constructor
    intro K _ _
    have (V : Cᵒᵖ) : Module.Flat (R.obj.obj V) (F.obj V) := hflat V
    exact ⟨⟨fun hc ↦ ⟨PresheafOfModules.evaluationJointlyReflectsLimits _ _
      (fun V ↦ isLimitOfPreserves
        (tensorRight (show ModuleCat (R.obj.obj V) from F.obj V))
        (isLimitOfPreserves (PresheafOfModules.evaluation O.obj V) hc))⟩⟩⟩
  have : Presheaf.IsLocallyInjective J (𝟙 O.obj) :=
    Presheaf.isLocallyInjective_of_injective J _ (fun _ ↦ Function.injective_id)
  have : Presheaf.IsLocallySurjective J (𝟙 O.obj) :=
    Presheaf.isLocallySurjective_of_surjective J _ (fun _ ↦ Function.surjective_id)
  exact (PresheafOfModules.isFlat_sheafification_obj (R := R) (𝟙 O.obj) F hF).2

private theorem ringComplex_kflat :
    CochainComplex.IsAcyclicTensorKFlat (ringedSiteRingComplex O) := by
  let := SheafOfModules.monoidalCategory O
  let := SheafOfModules.symmetricCategory O
  let := (SheafOfModules.tensorClosed O).1.some
  apply CochainComplex.isKFlat_of_boundedAbove_flat
  · refine ⟨0, fun n hn ↦ ?_⟩
    exact HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 _ n (ne_of_gt hn)
  · intro n
    let := SheafOfModules.monoidalCategory O
    by_cases hn : n = 0
    · subst n
      have h := ObjectProperty.prop_unit
        (ObjectProperty.flat (A := SheafOfModules.{u}
          ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)))
      exact ((ObjectProperty.flat).prop_of_iso
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0 _).symm h).tensorRight
    · exact (ObjectProperty.flat_of_isZero
        (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 _ n hn)).tensorRight

private theorem localizationFactor_kflat
    (s : (O.obj ⋙ forget CommRingCat).sections) :
    CochainComplex.IsAcyclicTensorKFlat (ringedLocalizationTwoTerm O s) := by
  let := SheafOfModules.monoidalCategory O
  let := SheafOfModules.symmetricCategory O
  let := (SheafOfModules.tensorClosed O).1.some
  apply CochainComplex.isKFlat_of_boundedAbove_flat
  · refine ⟨1, fun n hn ↦ ?_⟩
    change IsZero (ringedLocalizationTwoTermX O s n)
    simp only [ringedLocalizationTwoTermX, if_neg (show n ≠ 0 by omega),
      if_neg (show n ≠ 1 by omega)]
    exact isZero_zero _
  · intro n
    change SheafOfModules.IsFlat (ringedLocalizationTwoTermX O s n)
    by_cases hn : n = 0
    · subst n
      rw [ringedLocalizationTwoTermX_zero]
      let := SheafOfModules.monoidalCategory O
      exact (ObjectProperty.prop_unit (ObjectProperty.flat)).tensorRight
    · by_cases hn' : n = 1
      · subst n
        rw [ringedLocalizationTwoTermX_one]
        exact localization_isFlat O s
      · simp only [ringedLocalizationTwoTermX, if_neg hn, if_neg hn']
        let := SheafOfModules.monoidalCategory O
        exact (ObjectProperty.flat_of_isZero (isZero_zero _)).tensorRight

private theorem cech_kflat (r : ℕ)
    (b : Fin r → (O.obj ⋙ forget CommRingCat).sections) :
    CochainComplex.IsAcyclicTensorKFlat (ringedExtendedCech O r b).1 := by
  induction r with
  | zero => exact ringComplex_kflat O
  | succ r ih =>
    let A := SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)
    let : IsGrothendieckAbelian.{u} A := SheafOfModules.isGrothendieckAbelian _
    let : HasColimitsOfSize.{0, 0} A := hasColimitsOfSizeShrink.{0, 0, u, u} _
    let := SheafOfModules.monoidalCategory O
    let := SheafOfModules.symmetricCategory O
    let := (SheafOfModules.tensorClosed O).1.some
    let := (SheafOfModules.tensorClosed O).2.1.some
    intro M hM i
    exact (ih (fun j ↦ b j.succ) _ (localizationFactor_kflat O (b 0) M hM) i).of_iso
      (HomologicalComplex.associator M (ringedLocalizationTwoTerm O (b 0))
        (ringedExtendedCech O r (fun j ↦ b j.succ)).1)

private theorem generatingList_section_value
    (I : ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))
    (ι : I ⟶ SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))
    (U : C) (r : ℕ) (f : Fin r → O.obj.obj (op U))
    (σ : (I.over U).GeneratingSections) (e : σ.I ≃ Fin r)
    (h : ∀ i, (SheafOfModules.sectionsMap (ι.over U) (σ.s i)).val
      (op (Over.mk (𝟙 U))) = f (e i))
    (W : C) (a : W ⟶ U) (i : σ.I) :
    ι.val.app (op W) ((σ.s i).val (op (Over.mk a))) = O.obj.map a.op (f (e i)) := by
  let k : Over.mk a ⟶ Over.mk (𝟙 U) := Over.homMk a (by simp)
  have hn := (SheafOfModules.sectionsMap (ι.over U) (σ.s i)).property k.op
  change O.obj.map a.op
    ((SheafOfModules.sectionsMap (ι.over U) (σ.s i)).val (op (Over.mk (𝟙 U)))) = _ at hn
  rw [h] at hn
  exact hn.symm

private theorem exists_cover_mem_span_generatingList
    (I : ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))
    (ι : I ⟶ SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))
    (U : C) (r : ℕ) (f : Fin r → O.obj.obj (op U))
    (hf : IsRingedIdealGeneratingList O I ι U r f)
    (W : C) (a : W ⟶ U) {T : Type u} [Finite T]
    (s : T → I.val.obj (op W)) :
    ∃ S ∈ J W, ∀ (V : C) (k : V ⟶ W), S k → ∀ j,
      ι.val.app (op V) (I.val.map k.op (s j)) ∈
        Ideal.span (Set.range (fun i ↦ O.obj.map (k ≫ a).op (f i))) := by
  classical
  obtain ⟨σ, e, he⟩ := hf
  let := Fintype.ofEquiv (Fin r) e.symm
  obtain ⟨S, hS, hs⟩ := SheafOfModules.exists_cover_linearCombination_generators
    (I.over U) σ (Over.mk a) s
  refine ⟨Sieve.overEquiv (Over.mk a) S, (J.mem_over_iff S).1 hS, ?_⟩
  intro V k hk j
  let l : Over.mk (k ≫ a) ⟶ Over.mk a := Over.homMk k rfl
  have hl : S l := by
    have hh : ((Sieve.overEquiv (Over.mk a)).symm
        (Sieve.overEquiv (Over.mk a) S)) l := hk
    simpa only [OrderIso.symm_apply_apply] using hh
  obtain ⟨c, hc⟩ := hs (Over.mk (k ≫ a)) l hl j
  change I.val.map k.op (s j) = ∑ i, c i •
    (show I.val.obj (op V) from (σ.s i).val (op (Over.mk (k ≫ a)))) at hc
  rw [hc, map_sum]
  change (∑ i, (show O.obj.obj (op V) from ι.val.app (op V)
    (c i • (show I.val.obj (op V) from (σ.s i).val (op (Over.mk (k ≫ a))))))) ∈ _
  apply Submodule.sum_mem
  intro i _
  have hi := (ι.val.app (op V)).hom.map_smul
    (show ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O).obj.obj (op V) from c i)
    (show I.val.obj (op V) from (σ.s i).val (op (Over.mk (k ≫ a))))
  change (show O.obj.obj (op V) from ι.val.app (op V)
      (c i • (show I.val.obj (op V) from (σ.s i).val (op (Over.mk (k ≫ a)))))) =
    (show O.obj.obj (op V) from c i) *
      (show O.obj.obj (op V) from ι.val.app (op V)
        ((σ.s i).val (op (Over.mk (k ≫ a))))) at hi
  rw [hi, generatingList_section_value O I ι U r f σ e he V (k ≫ a) i]
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨e i, rfl⟩)


end LocalCalculation

end CategoryTheory
