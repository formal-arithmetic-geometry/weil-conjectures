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
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import WeilConjectures.FromJoel.Algebra.Homology.Bifunctor
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import Mathlib.Algebra.Homology.HomologySequenceLemmas
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Homology.HomotopyCategory.SingleFunctors
import Mathlib.Algebra.Homology.BifunctorShift
import WeilConjectures.Algebra.Category.ModuleCat.Presheaf.SheafificationTensor
import Mathlib.RingTheory.Localization.BaseChange

/-! # The tensor augmentation for one localization factor

Source: Stacks Project, algebraization.tex, Tag 099B.
(blueprint: lem-weil-pbc-ringed-localization-factor-tensor-augmentation).
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory Opposite
namespace CategoryTheory
variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}

open CategoryTheory.Limits CategoryTheory.MonoidalCategory

attribute [local irreducible] SheafOfModules.monoidalCategory

private theorem tensor_split_exact
    {A : Type*} [Category* A] [Abelian A] [MonoidalCategory A]
    [MonoidalPreadditive A]
    [∀ K L : CochainComplex A ℤ,
      HomologicalComplex.HasMapBifunctor K L (curriedTensor A) (.up ℤ)]
    (K : CochainComplex A ℤ) (S : ShortComplex (CochainComplex A ℤ))
    (hS : ∀ n : ℤ, (S.map (HomologicalComplex.eval A (.up ℤ) n)).Splitting) :
    (S.map (((curriedTensor A).map₂CochainComplex).obj K)).ShortExact := by
  classical
  let r₀ (q : ℤ) : S.X₂.X q ⟶ S.X₁.X q := (hS q).r
  let s₀ (q : ℤ) : S.X₃.X q ⟶ S.X₂.X q := (hS q).s
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  let r : (HomologicalComplex.mapBifunctor K S.X₂ (curriedTensor A) (.up ℤ)).X n ⟶
      (HomologicalComplex.mapBifunctor K S.X₁ (curriedTensor A) (.up ℤ)).X n :=
    HomologicalComplex.mapBifunctorDesc (fun p q hpq ↦ K.X p ◁ r₀ q ≫
      HomologicalComplex.ιMapBifunctor K S.X₁ (curriedTensor A) (.up ℤ) p q n hpq)
  let t : (HomologicalComplex.mapBifunctor K S.X₃ (curriedTensor A) (.up ℤ)).X n ⟶
      (HomologicalComplex.mapBifunctor K S.X₂ (curriedTensor A) (.up ℤ)).X n :=
    HomologicalComplex.mapBifunctorDesc (fun p q hpq ↦ K.X p ◁ s₀ q ≫
      HomologicalComplex.ιMapBifunctor K S.X₂ (curriedTensor A) (.up ℤ) p q n hpq)
  apply ShortComplex.Splitting.shortExact
  refine { r := r, s := t, f_r := ?_, s_g := ?_, id := ?_ }
  · change (HomologicalComplex.mapBifunctorMap (𝟙 K) S.f (curriedTensor A) (.up ℤ)).f n ≫
      r = 𝟙 _
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro p q hpq
    simp only [r, HomologicalComplex.ι_mapBifunctorMap_assoc,
      HomologicalComplex.ι_mapBifunctorDesc, HomologicalComplex.id_f,
      curriedTensor_map_app, curriedTensor_obj_map, id_whiskerRight,
      Category.comp_id]
    erw [Category.id_comp]
    rw [← Category.assoc, ← whiskerLeft_comp]
    have h := (hS q).f_r
    change S.f.f q ≫ r₀ q = 𝟙 _ at h
    rw [h, whiskerLeft_id]
    exact Category.id_comp _
  · change t ≫
      (HomologicalComplex.mapBifunctorMap (𝟙 K) S.g (curriedTensor A) (.up ℤ)).f n = 𝟙 _
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro p q hpq
    simp only [t, Category.assoc, HomologicalComplex.ι_mapBifunctorDesc_assoc,
      HomologicalComplex.ι_mapBifunctorMap, HomologicalComplex.id_f,
      curriedTensor_map_app, curriedTensor_obj_map, id_whiskerRight,
      Category.comp_id]
    erw [Category.id_comp]
    rw [← Category.assoc, ← whiskerLeft_comp]
    have h := (hS q).s_g
    change s₀ q ≫ S.g.f q = 𝟙 _ at h
    rw [h, whiskerLeft_id]
    exact Category.id_comp _
  · change r ≫
        (HomologicalComplex.mapBifunctorMap (𝟙 K) S.f (curriedTensor A) (.up ℤ)).f n +
      (HomologicalComplex.mapBifunctorMap (𝟙 K) S.g (curriedTensor A) (.up ℤ)).f n ≫ t = 𝟙 _
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro p q hpq
    simp only [r, t, Preadditive.comp_add, Category.assoc,
      HomologicalComplex.ι_mapBifunctorDesc_assoc, HomologicalComplex.ι_mapBifunctorMap,
      HomologicalComplex.ι_mapBifunctorMap_assoc, HomologicalComplex.ι_mapBifunctorDesc,
      HomologicalComplex.id_f, curriedTensor_map_app, curriedTensor_obj_map,
      id_whiskerRight, Category.comp_id]
    erw [Category.id_comp, Category.id_comp]
    rw [← Category.assoc, ← whiskerLeft_comp, ← Category.assoc, ← whiskerLeft_comp,
      ← Preadditive.add_comp, ← MonoidalPreadditive.whiskerLeft_add]
    have h := (hS q).id
    change r₀ q ≫ S.f.f q + S.g.f q ≫ s₀ q = 𝟙 _ at h
    rw [h, whiskerLeft_id]
    exact Category.id_comp _

private noncomputable def localization_inclusion
    (O : Sheaf J CommRingCat.{u})
    (s : (O.obj ⋙ forget CommRingCat).sections) :
    (HomologicalComplex.single _ (.up ℤ) 1).obj (ringedSectionLocalization O s) ⟶
      ringedLocalizationTwoTerm O s :=
  HomologicalComplex.mkHomFromSingle (K := ringedLocalizationTwoTerm O s) (j := 1)
    (eqToHom (ringedLocalizationTwoTermX_one O s).symm) (by
      intro k hk
      have hk' : k = 2 := by change (1 : ℤ) + 1 = k at hk; omega
      subst k
      change eqToHom (ringedLocalizationTwoTermX_one O s).symm ≫
        CochainComplex.of.d (ringedLocalizationTwoTermX O s)
          (ringedLocalizationTwoTermD O s) 1 2 = 0
      erw [CochainComplex.of_d]
      simp [ringedLocalizationTwoTermD])

private theorem localization_inclusion_augmentation
    (O : Sheaf J CommRingCat.{u})
    (s : (O.obj ⋙ forget CommRingCat).sections) :
    localization_inclusion O s ≫ ringedLocalizationTwoTermAugmentation O s = 0 := by
  apply HomologicalComplex.from_single_hom_ext
  simp [HomologicalComplex.comp_f, ringedLocalizationTwoTermAugmentation,
    ringedLocalizationTwoTermAugmentationF]

private noncomputable def localization_split
    (O : Sheaf J CommRingCat.{u})
    (s : (O.obj ⋙ forget CommRingCat).sections) (n : ℤ) :
    ((ShortComplex.mk (localization_inclusion O s)
      (ringedLocalizationTwoTermAugmentation O s)
      (localization_inclusion_augmentation O s)).map
        (HomologicalComplex.eval _ (.up ℤ) n)).Splitting := by
  by_cases hn : n = 0
  · subst n
    apply ShortComplex.Splitting.ofIsZeroOfIsIso
    · exact HomologicalComplex.isZero_single_obj_X (.up ℤ) 1
        (ringedSectionLocalization O s) 0 (by omega)
    · change IsIso (ringedLocalizationTwoTermAugmentationF O s 0)
      dsimp only [ringedLocalizationTwoTermAugmentationF]
      split_ifs with h
      · infer_instance
      · exact (h rfl).elim
  · apply ShortComplex.Splitting.ofIsIsoOfIsZero
    · by_cases hn' : n = 1
      · subst n
        change IsIso ((localization_inclusion O s).f 1)
        dsimp only [localization_inclusion]
        rw [HomologicalComplex.mkHomFromSingle_f]
        infer_instance
      · have hz₁ := HomologicalComplex.isZero_single_obj_X (.up ℤ) 1
          (ringedSectionLocalization O s) n hn'
        have hz₂ : IsZero ((ringedLocalizationTwoTerm O s).X n) := by
          change IsZero (ringedLocalizationTwoTermX O s n)
          simp only [ringedLocalizationTwoTermX, if_neg hn, if_neg hn']
          exact isZero_zero _
        exact ⟨⟨0, hz₁.eq_of_src _ _, hz₂.eq_of_src _ _⟩⟩
    · exact HomologicalComplex.isZero_single_obj_X (.up ℤ) 0
        (SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)) n hn

end CategoryTheory
