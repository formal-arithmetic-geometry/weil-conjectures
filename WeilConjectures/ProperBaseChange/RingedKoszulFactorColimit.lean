/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.RingTheory.Localization.Away.Basic
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
public import Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Homology.HomComplex
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationIsIso
public import WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationComm
public import WeilConjectures.Algebra.Homology.HomComplexComponents
public import WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationNaturality
public import WeilConjectures.ProEtaleCoefficients.RingedStrictTowerHomotopyLimit
public import WeilConjectures.CategoryTheory.Ringed.RingedInternalHomExactRestrictionSupplement
public import Mathlib.Algebra.Homology.Double
public import Mathlib.CategoryTheory.Endomorphism
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.Algebra.Homology.Functor
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
import Mathlib.Algebra.Module.LocalizedModule.IsLocalization
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits

/-! # The one-section Koszul localization colimit

Source: Stacks Project, More on Algebra, Tag 0913.
(blueprint: lem-weil-pbc-ringed-koszul-factor-colimit).
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory
private theorem scalar_localization_colimit {R : Type u} [CommRing R] (s : R) :
    let D := Functor.ofSequence (X := fun _ : ℕ ↦ ModuleCat.of R R)
      (fun _ ↦ ModuleCat.ofHom (LinearMap.lsmul R R s))
    ∃ e : colimit D ≅ ModuleCat.of R (Localization.Away s),
      ∀ (m : ℕ) (a : R), e.hom ((colimit.ι D m) a) =
        algebraMap R _ a * IsLocalization.Away.invSelf s ^ (m + 1) := by
  dsimp only
  obtain ⟨κ, hκ⟩ := ModuleCat.localization_away_colimit s R
  let e := IsLocalizedModule.iso (Submonoid.powers s)
    (Algebra.linearMap R (Localization.Away s))
  have he (a : R) (n : ℕ) :
      e (LocalizedModule.mk (S := Submonoid.powers s) a ⟨s ^ n, ⟨n, rfl⟩⟩) =
        algebraMap R _ a * IsLocalization.Away.invSelf s ^ n := by
    apply (IsLocalization.Away.algebraMap_pow_isUnit
      (S := Localization.Away s) s n).mul_left_cancel
    calc
      _ = e ((s ^ n) • LocalizedModule.mk (S := Submonoid.powers s)
          a ⟨s ^ n, ⟨n, rfl⟩⟩) := by rw [map_smul, Algebra.smul_def, map_pow]
      _ = algebraMap R _ a := by
        rw [LocalizedModule.smul'_mk, ← Submonoid.smul_def (⟨s ^ n, ⟨n, rfl⟩⟩ : Submonoid.powers s),
          LocalizedModule.mk_cancel]
        exact IsLocalizedModule.iso_mk_one _ _ a
      _ = _ := by rw [mul_left_comm, ← mul_pow,
        IsLocalization.Away.mul_invSelf, one_pow, mul_one]
  let v : Localization.Away s ≃ₗ[R] Localization.Away s :=
    { toFun := fun x ↦ x * IsLocalization.Away.invSelf s
      invFun := fun x ↦ x * algebraMap R _ s
      left_inv := by intro x; dsimp only; rw [mul_assoc, mul_comm _ (algebraMap R _ s),
        IsLocalization.Away.mul_invSelf, mul_one]
      right_inv := by intro x; dsimp only; rw [mul_assoc, IsLocalization.Away.mul_invSelf, mul_one]
      map_add' := by intros; exact add_mul _ _ _
      map_smul' := by intros; simp only [Algebra.smul_def, RingHom.id_apply, mul_assoc] }
  refine ⟨(κ.trans (e.trans v)).toModuleIso, ?_⟩
  intro m a
  change v (e (κ ((colimit.ι (Functor.ofSequence (X := fun _ : ℕ ↦
    ModuleCat.of R R) (fun _ ↦ ModuleCat.ofHom (LinearMap.lsmul R R s))) m) a))) = _
  rw [hκ, he]
  exact (mul_assoc _ _ _).trans (congrArg (algebraMap R _ a * ·) (pow_succ _ m).symm)

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
variable (O : Sheaf J CommRingCat.{u})

private abbrev sectionValue
    (s : (O.obj ⋙ forget CommRingCat).sections) (X : Cᵒᵖ) : O.obj.obj X := s.val X

private abbrev localizationInv
    (s : (O.obj ⋙ forget CommRingCat).sections) (X : Cᵒᵖ) :
    ringedSectionLocalizationCarrier O s X :=
  IsLocalization.Away.invSelf (R := O.obj.obj X) (sectionValue O s X)

private theorem localization_map_inv
    (s : (O.obj ⋙ forget CommRingCat).sections) {X Y : Cᵒᵖ} (g : X ⟶ Y) :
    ringedSectionLocalizationMap O s g
      (localizationInv O s X) =
        localizationInv O s Y := by
  apply (IsLocalization.Away.algebraMap_isUnit
    (R := O.obj.obj Y) (S := ringedSectionLocalizationCarrier O s Y)
      (sectionValue O s Y)).mul_left_cancel
  have hc (a : O.obj.obj X) :
      ringedSectionLocalizationMap O s g (algebraMap _ _ a) =
        algebraMap _ _ (O.obj.map g a) := by
    exact IsLocalization.Away.lift_eq _ _ a
  calc
    _ = ringedSectionLocalizationMap O s g
        (algebraMap _ _ (sectionValue O s X) * localizationInv O s X) := by
      rw [map_mul, hc, show O.obj.map g (sectionValue O s X) =
          sectionValue O s Y from s.property g]
    _ = 1 := by rw [IsLocalization.Away.mul_invSelf, map_one]
    _ = _ := (IsLocalization.Away.mul_invSelf (sectionValue O s Y)).symm

private def fractionMap
    (s : (O.obj ⋙ forget CommRingCat).sections) (n : ℕ) :
    PresheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O).obj ⟶
      ringedSectionLocalizationPresheaf O s :=
  (ringedSectionLocalizationPresheaf O s).unitHomEquiv.symm
    (PresheafOfModules.sectionsMk
      (fun X ↦ localizationInv O s X ^ n)
      (fun {_ _} g ↦ by
        change ringedSectionLocalizationMap O s g _ = _
        rw [map_pow, localization_map_inv]))

private theorem fractionMap_apply
    (s : (O.obj ⋙ forget CommRingCat).sections) (n : ℕ)
    (X : Cᵒᵖ) (a : O.obj.obj X) :
    (fractionMap O s n).app X a =
      algebraMap (O.obj.obj X) (ringedSectionLocalizationCarrier O s X) a *
        localizationInv O s X ^ n := by
  change a • localizationInv O s X ^ n = _
  exact Algebra.smul_def a _

private theorem scalar_apply
    (s : (O.obj ⋙ forget CommRingCat).sections) (X : Cᵒᵖ) (a : O.obj.obj X) :
    (ringedKoszulScalar O s).val.app X a = a * sectionValue O s X := by
  change a • sectionValue O s X = _
  rfl

private theorem fractionMap_step
    (s : (O.obj ⋙ forget CommRingCat).sections) (n : ℕ) :
    (ringedKoszulScalar O s).val ≫ fractionMap O s (n + 1) = fractionMap O s n := by
  apply PresheafOfModules.hom_ext
  intro X
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  change O.obj.obj X at a
  change (fractionMap O s (n + 1)).app X ((ringedKoszulScalar O s).val.app X a) =
    (fractionMap O s n).app X a
  rw [fractionMap_apply, scalar_apply, fractionMap_apply, map_mul, pow_succ]
  calc
    _ = (algebraMap _ _ a * localizationInv O s X ^ n) *
        (algebraMap _ _ (sectionValue O s X) * localizationInv O s X) := by ring
    _ = _ := by rw [IsLocalization.Away.mul_invSelf, mul_one]

private def localizationPresheafCocone
    (s : (O.obj ⋙ forget CommRingCat).sections) :
    Cocone (Functor.ofSequence (X := fun _ : ℕ ↦
      SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))
        (fun _ ↦ ringedKoszulScalar O s) ⋙ SheafOfModules.forget _) where
  pt := ringedSectionLocalizationPresheaf O s
  ι := NatTrans.ofSequence (fun n ↦ fractionMap O s (n + 1)) (by
    intro n
    change ((SheafOfModules.forget _).map
      ((Functor.ofSequence (fun _ ↦ ringedKoszulScalar O s)).map _)) ≫ _ = _ ≫ 𝟙 _
    rw [Functor.ofSequence_map_homOfLE_succ, Category.comp_id]
    exact fractionMap_step O s (n + 1))

private def localizationPresheafCoconeIsColimit
    (s : (O.obj ⋙ forget CommRingCat).sections) :
    IsColimit (localizationPresheafCocone O s) := by
  apply PresheafOfModules.evaluationJointlyReflectsColimits
  intro X
  let R := O.obj.obj X
  let D := Functor.ofSequence (X := fun _ : ℕ ↦ ModuleCat.of R R)
    (fun _ ↦ ModuleCat.ofHom (LinearMap.lsmul R R (sectionValue O s X)))
  let c := (PresheafOfModules.evaluation _ X).mapCocone
    (localizationPresheafCocone O s)
  let F := (Functor.ofSequence (fun _ ↦ ringedKoszulScalar O s) ⋙
    SheafOfModules.forget _) ⋙ PresheafOfModules.evaluation _ X
  let t : D ⟶ F := NatTrans.ofSequence (fun _ ↦ 𝟙 (ModuleCat.of R R)) (by
    intro n
    simp only [F, D, Functor.comp_map, Functor.ofSequence_map_homOfLE_succ]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    change O.obj.obj X at a
    change (sectionValue O s X) * a = (ringedKoszulScalar O s).val.app X a
    rw [scalar_apply, mul_comm])
  let et : D ≅ F := NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intro i j f; exact t.naturality f)
  let e := Classical.choose (scalar_localization_colimit (sectionValue O s X))
  have he := Classical.choose_spec (scalar_localization_colimit (sectionValue O s X))
  apply (IsColimit.precomposeHomEquiv et c).toFun
  apply IsColimit.ofIsoColimit (colimit.isColimit D)
  refine Cocone.ext e ?_
  intro m
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  dsimp only [et, c, Cocone.precompose, localizationPresheafCocone,
    Functor.mapCocone, NatIso.ofComponents, NatTrans.ofSequence] at *
  change e.hom ((colimit.ι D m) a) = (fractionMap O s (m + 1)).app X a
  rw [he, fractionMap_apply]

private def localizationSheafMap
    (s : (O.obj ⋙ forget CommRingCat).sections) (n : ℕ) :
    SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O) ⟶
      ringedSectionLocalization O s :=
  (SheafOfModules.fullyFaithfulForget _).preimage
    (fractionMap O s n ≫
      (PresheafOfModules.sheafificationAdjunction
        (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O).obj)).unit.app _)

private theorem localizationSheafMap_step
    (s : (O.obj ⋙ forget CommRingCat).sections) (n : ℕ) :
    ringedKoszulScalar O s ≫ localizationSheafMap O s (n + 1) =
      localizationSheafMap O s n := by
  apply SheafOfModules.hom_ext
  change (ringedKoszulScalar O s).val ≫ (fractionMap O s (n + 1) ≫ _) = _
  rw [← Category.assoc, fractionMap_step]
  rfl

private def localizationSheafCocone
    (s : (O.obj ⋙ forget CommRingCat).sections) :
    Cocone (Functor.ofSequence (X := fun _ : ℕ ↦
      SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))
        (fun _ ↦ ringedKoszulScalar O s)) where
  pt := ringedSectionLocalization O s
  ι := NatTrans.ofSequence (fun n ↦ localizationSheafMap O s (n + 1)) (by
    intro n
    rw [Functor.ofSequence_map_homOfLE_succ, Functor.const_obj_map]
    change ringedKoszulScalar O s ≫ _ = _ ≫ 𝟙 _
    rw [Category.comp_id]
    exact localizationSheafMap_step O s (n + 1))

private def localizationSheafCoconeIsColimit
    (s : (O.obj ⋙ forget CommRingCat).sections) :
    IsColimit (localizationSheafCocone O s) := by
  let adj := PresheafOfModules.sheafificationAdjunction
    (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O).obj)
  let hc := localizationPresheafCoconeIsColimit O s
  let U := SheafOfModules.forget ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)
  refine { desc := fun t ↦ (adj.homEquiv _ _).symm (hc.desc (U.mapCocone t))
           fac := ?_
           uniq := ?_ }
  · intro t n
    apply U.map_injective
    change (fractionMap O s (n + 1) ≫ adj.unit.app _) ≫
      U.map ((adj.homEquiv _ _).symm (hc.desc (U.mapCocone t))) = _
    rw [Category.assoc]
    erw [← Adjunction.homEquiv_unit, Equiv.apply_symm_apply]
    exact hc.fac (U.mapCocone t) n
  · intro t m hm
    apply (adj.homEquiv _ _).injective
    rw [Equiv.apply_symm_apply]
    apply hc.hom_ext
    intro n
    rw [hc.fac]
    change fractionMap O s (n + 1) ≫ (adj.homEquiv _ _ m) = _
    rw [Adjunction.homEquiv_unit, ← Category.assoc]
    exact congrArg (fun f ↦ U.map f) (hm n)

private theorem localizationSheafMap_zero
    (s : (O.obj ⋙ forget CommRingCat).sections) :
    localizationSheafMap O s 0 = ringedSectionLocalizationUnit O s := by
  unfold localizationSheafMap ringedSectionLocalizationUnit
  congr 2

end CategoryTheory
