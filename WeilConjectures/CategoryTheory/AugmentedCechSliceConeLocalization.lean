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
public import WeilConjectures.CategoryTheory.AugmentedCechLocalOrthogonality
import all WeilConjectures.ProperBaseChange.RingedGeneratingListsLocalEquality
import all WeilConjectures.ProperBaseChange.RingedAugmentedCechRestriction
import WeilConjectures.ProperBaseChange.RingedLocalizationFactorRestriction
import all WeilConjectures.ProperBaseChange.RingedLocalizationFactorTensorAugmentation
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Triangulated.Subcategory
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits

/-! # Finite localization filtration of the actual Cech augmentation

Source: Stacks Project, dualizing.tex, Tag 0A6R, and algebraization.tex, Tag 099E.
(blueprint: lem-weil-pbc-augmented-cech-slice-cone-localization).
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u w

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.Pretriangulated Opposite

namespace CategoryTheory

private theorem sliceCalculation
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u})
    [∀ U : C, HasDerivedCategory.{w} (SheafOfModules.{u}
      ((sheafCompose (J.over U) (forget₂ CommRingCat RingCat)).obj (O.over U)))]
    (U V : C) (f : V ⟶ U) (r : ℕ)
    (b : Fin r → ((O.over U).obj ⋙ forget CommRingCat).sections) :
    Nonempty
      (Arrow.mk ((ringedKoszulDerivedOverMap O f).map
          (DerivedCategory.Q.map (ringedExtendedCech (O.over U) r b).2)) ≅
        Arrow.mk (DerivedCategory.Q.map
          (ringedExtendedCech (O.over V) r
            (fun i ↦ LocalizationRHom.restrictedSection (K := J.over V)
              (L := J.over U) (Over.map f) (O.over U) (b i))).2)) := by
  let R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj O
  let (X : C) : HasDerivedCategory.{w} (SheafOfModules.{u}
      (((sheafCompose J (forget₂ CommRingCat RingCat)).obj O).over X)) :=
    inferInstanceAs (HasDerivedCategory.{w} (SheafOfModules.{u}
      ((sheafCompose (J.over X) (forget₂ CommRingCat RingCat)).obj (O.over X))))
  let : HasDerivedCategory.{w} (SheafOfModules.{u}
      ((sheafCompose (J.over V) (forget₂ CommRingCat RingCat)).obj
        (((Over.map f).sheafPushforwardContinuous CommRingCat
          (J.over V) (J.over U)).obj (O.over U)))) :=
    inferInstanceAs (HasDerivedCategory.{w} (SheafOfModules.{u}
      ((sheafCompose (J.over V) (forget₂ CommRingCat RingCat)).obj (O.over V))))
  let F := SheafOfModules.overMap.{u} R f
  have h := augmentedCechRestriction_of_factors
    (J := J.over V) (K := J.over U) (Over.map f) (O.over U)
      ((exists_ringed_localization_factor_restriction O).2 U V f) r b
  exact ⟨derivedArrowRestriction F (ringedExtendedCech (O.over U) r b).2 ≪≫
    DerivedCategory.Q.mapArrow.mapIso h.some⟩

private theorem sliceSection_restrict
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u}) (U V : C) (a : V ⟶ U)
    (x : O.obj.obj (op U)) :
    LocalizationRHom.restrictedSection (K := J.over V) (L := J.over U)
        (Over.map a) (O.over U) (ringedSliceSection O U x) =
      ringedSliceSection O V (O.obj.map a.op x) := by
  apply Subtype.ext
  funext W
  change O.obj.map (W.unop.hom ≫ a).op x =
    O.obj.map W.unop.hom.op (O.obj.map a.op x)
  rw [op_comp, Functor.map_comp]
  rfl

private theorem sliceListCalculation
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u})
    [∀ U : C, HasDerivedCategory.{w} (SheafOfModules.{u}
      ((sheafCompose (J.over U) (forget₂ CommRingCat RingCat)).obj (O.over U)))]
    (U V : C) (a : V ⟶ U) (r : ℕ) (f : Fin r → O.obj.obj (op U)) :
    Nonempty
      (Arrow.mk ((ringedKoszulDerivedOverMap O a).map
          (DerivedCategory.Q.map (ringedExtendedCech (O.over U) r
            (fun i ↦ ringedSliceSection O U (f i))).2)) ≅
        Arrow.mk (DerivedCategory.Q.map (ringedExtendedCech (O.over V) r
          (fun i ↦ ringedSliceSection O V (O.obj.map a.op (f i)))).2)) := by
  have h := sliceCalculation O U V a r (fun i ↦ ringedSliceSection O U (f i))
  have hs : (fun i : Fin r ↦ LocalizationRHom.restrictedSection
      (K := J.over V) (L := J.over U) (Over.map a) (O.over U)
        (ringedSliceSection O U (f i))) =
      (fun i ↦ ringedSliceSection O V (O.obj.map a.op (f i))) := by
    funext i
    exact sliceSection_restrict O U V a (f i)
  rw [hs] at h
  exact h

end CategoryTheory

namespace CategoryTheory

private theorem overMap_preserves_colimits
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) {U V : C} (f : V ⟶ U) :
    PreservesColimitsOfSize.{u, u} (SheafOfModules.overMap.{u} R f) := by
  let F := SheafOfModules.overMap.{u} R f
  let H := (Over.map f).sheafPushforwardContinuous AddCommGrpCat.{u} (J.over V) (J.over U)
  have : PreservesColimitsOfSize.{u, u} H :=
    ((Over.map f).sheafAdjunctionCocontinuous AddCommGrpCat.{u}
      (J.over V) (J.over U)).leftAdjoint_preservesColimits
  let T := SheafOfModules.toSheaf.{u} (R.over V)
  have : PreservesColimitsOfSize.{u, u} (SheafOfModules.toSheaf.{u} (R.over U)) :=
    { preservesColimitsOfShape := inferInstance }
  have : PreservesColimitsOfSize.{u, u} T :=
    { preservesColimitsOfShape := inferInstance }
  have : PreservesColimitsOfSize.{u, u} (F ⋙ T) := by
    change PreservesColimitsOfSize.{u, u} (SheafOfModules.toSheaf.{u} (R.over U) ⋙ H)
    infer_instance
  have : ReflectsColimitsOfSize.{u, u} T := reflectsColimits_of_reflectsIsomorphisms
  exact preservesColimits_of_reflects_of_preserves F T

private theorem mapped_generator
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) {U V : C} (f : V ⟶ U)
    (M : SheafOfModules.{u} (R.over U)) (σ : M.GeneratingSections) (i : σ.I) :
    let := overMap_preserves_colimits R f
    let F := SheafOfModules.overMap.{u} R f
    (σ.map F (SheafOfModules.overMapUnitIso (R := R) f).symm).s i =
      (F.obj M).unitHomEquiv
        ((SheafOfModules.overMapUnitIso (R := R) f).inv ≫
          F.map (M.unitHomEquiv.symm (σ.s i))) := by
  dsimp only
  apply (SheafOfModules.unitHomEquiv _).symm.injective
  rw [Equiv.symm_apply_apply]
  change (SheafOfModules.unitHomEquiv _).symm
    (SheafOfModules.freeHomEquiv _ _ i) = _
  rw [SheafOfModules.unitHomEquiv_symm_freeHomEquiv_apply]
  dsimp only [SheafOfModules.GeneratingSections.mapFreeHom]
  rw [← Category.assoc, SheafOfModules.ιFree_mapFreeIso_hom, Category.assoc,
    ← Functor.map_comp, ← SheafOfModules.unitHomEquiv_symm_freeHomEquiv_apply]
  congr 2
  exact congrArg M.unitHomEquiv.symm
    (congrFun (M.freeHomEquiv.apply_symm_apply σ.s) i)


private theorem mapped_generator_eval
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) {U V : C} (f : V ⟶ U)
    (M : SheafOfModules.{u} (R.over U)) (σ : M.GeneratingSections) (i : σ.I)
    (W : Over V) :
    let := overMap_preserves_colimits R f
    let F := SheafOfModules.overMap.{u} R f
    ((σ.map F (SheafOfModules.overMapUnitIso (R := R) f).symm).s i).val (op W) =
      (σ.s i).val (op ((Over.map f).obj W)) := by
  dsimp only
  rw [mapped_generator, SheafOfModules.unitHomEquiv_apply_coe]
  change (M.unitHomEquiv.symm (σ.s i)).val.app
    (op ((Over.map f).obj W)) (1 : R.obj.obj (op W.left)) = _
  exact congrArg (fun s ↦ s.val (op ((Over.map f).obj W)))
    (M.unitHomEquiv.apply_symm_apply (σ.s i))


private theorem generatingList_restrict
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u})
    (I : ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))
    (ι : I ⟶ SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))
    (U V : C) (f : V ⟶ U) (r : ℕ) (b : Fin r → O.obj.obj (op U))
    (hb : IsRingedIdealGeneratingList O I ι U r b) :
    IsRingedIdealGeneratingList O I ι V r (fun i ↦ O.obj.map f.op (b i)) := by
  obtain ⟨σ, e, he⟩ := hb
  let R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj O
  let F := SheafOfModules.overMap.{u} R f
  let := overMap_preserves_colimits R f
  let τ := (σ.map F (SheafOfModules.overMapUnitIso (R := R) f).symm).ofEpi
    ((SheafOfModules.overFunctorMap R f).hom.app I)
  refine ⟨τ, e, ?_⟩
  intro i
  change ι.val.app (op V)
    (((σ.map F (SheafOfModules.overMapUnitIso (R := R) f).symm).s i).val
      (op (Over.mk (𝟙 V)))) = O.obj.map f.op (b (e i))
  rw [mapped_generator_eval]
  change ι.val.app (op V) ((σ.s i).val (op (Over.mk (𝟙 V ≫ f)))) = _
  trans ι.val.app (op V) ((σ.s i).val (op (Over.mk f)))
  · exact congrArg (fun t : V ⟶ U ↦
      ι.val.app (op V) ((σ.s i).val (op (Over.mk t)))) (Category.id_comp f)
  · exact generatingList_section_value O I ι U r b σ e he V f i

end CategoryTheory

namespace CategoryTheory

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
variable (O : Sheaf J CommRingCat.{u})

private def scalarPresheaf
    (s : (O.obj ⋙ forget CommRingCat).sections)
    (M : PresheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O).obj) : M ⟶ M where
  app X := ModuleCat.ofHom (LinearMap.lsmul (O.obj.obj X) (M.obj X) (s.val X))
  naturality := by
    intro X Y a
    ext m
    change (s.val Y : O.obj.obj Y) • M.map a m =
      M.map a ((s.val X : O.obj.obj X) • m)
    rw [M.map_smul]
    have hs : O.obj.map a (s.val X) = s.val Y := s.property a
    change (s.val Y : O.obj.obj Y) • _ = O.obj.map a (s.val X) • _
    rw [hs]

private def scalarSheaf
    (s : (O.obj ⋙ forget CommRingCat).sections)
    (M : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)) :
    M ⟶ M := ⟨scalarPresheaf O s M.val⟩

private theorem localizationPresheaf_scalar_isIso
    (s : (O.obj ⋙ forget CommRingCat).sections) :
    IsIso (scalarPresheaf O s (ringedSectionLocalizationPresheaf O s)) := by
  have hi (X : Cᵒᵖ) :
      IsIso ((scalarPresheaf O s (ringedSectionLocalizationPresheaf O s)).app X) := by
    apply (ConcreteCategory.isIso_iff_bijective _).2
    let x : O.obj.obj X := s.val X
    change Function.Bijective
      (fun m : ringedSectionLocalizationCarrier O s X ↦ x • m)
    simpa only [Algebra.smul_def] using
      (IsUnit.isUnit_iff_mulLeft_bijective.mp
        (IsLocalization.Away.algebraMap_isUnit (R := O.obj.obj X) x
          (S := ringedSectionLocalizationCarrier O s X)))
  let e := PresheafOfModules.isoMk
    (fun X ↦ asIso ((scalarPresheaf O s (ringedSectionLocalizationPresheaf O s)).app X))
  have he : e.hom = scalarPresheaf O s (ringedSectionLocalizationPresheaf O s) := rfl
  rw [← he]
  infer_instance

private theorem sheafification_scalar
    (s : (O.obj ⋙ forget CommRingCat).sections)
    (M : PresheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O).obj) :
    (PresheafOfModules.sheafification
        (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O).obj)).map
        (scalarPresheaf O s M) =
      scalarSheaf O s ((PresheafOfModules.sheafification
        (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O).obj)).obj M) := by
  let R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj O
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)
  apply (adj.homEquiv M _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  trans scalarPresheaf O s M ≫ adj.unit.app M
  · exact (adj.unit.naturality (scalarPresheaf O s M)).symm
  ext X m
  change (adj.unit.app M).app X ((s.val X : O.obj.obj X) • m) =
    (s.val X : O.obj.obj X) • (adj.unit.app M).app X m
  exact ((adj.unit.app M).app X).hom.map_smul (s.val X) m

private theorem scalarSheaf_naturality
    (s : (O.obj ⋙ forget CommRingCat).sections)
    {M N : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)}
    (f : M ⟶ N) : scalarSheaf O s M ≫ f = f ≫ scalarSheaf O s N := by
  ext X m
  exact (f.val.app X).hom.map_smul (s.val X) m

private theorem scalar_tensor_isIso
    (s : (O.obj ⋙ forget CommRingCat).sections)
    (M N : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))
    [IsIso (scalarSheaf O s M)] :
    let := SheafOfModules.monoidalCategory O
    IsIso (scalarSheaf O s (M ⊗ N)) := by
  let := SheafOfModules.monoidalCategory O
  let R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj O
  let a := PresheafOfModules.sheafification (𝟙 R.obj)
  let T : PresheafOfModules.{u} R.obj := M.val ⊗ N.val
  have : IsIso (scalarPresheaf O s M.val) :=
    inferInstanceAs (IsIso ((SheafOfModules.forget R).map (scalarSheaf O s M)))
  have hs : scalarPresheaf O s T = scalarPresheaf O s M.val ⊗ₘ 𝟙 N.val := by
    ext X : 1
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro m n
    let x : O.obj.obj X := s.val X
    change x • (m ⊗ₜ[O.obj.obj X] n) = (x • m) ⊗ₜ[O.obj.obj X] n
    exact (TensorProduct.smul_tmul' x m n).symm
  have : IsIso (scalarPresheaf O s T) := by rw [hs]; infer_instance
  have : IsIso (scalarSheaf O s (a.obj T)) := by
    rw [← sheafification_scalar]
    infer_instance
  let e := SheafOfModules.tensorObjIsoSheafification (R := O) M N
  have h := scalarSheaf_naturality O s e.hom
  have : IsIso (scalarSheaf O s (M ⊗ N) ≫ e.hom) := by
    rw [h]
    infer_instance
  exact IsIso.of_isIso_comp_right (scalarSheaf O s (M ⊗ N)) e.hom

private theorem scalar_colimit_isIso
    (s : (O.obj ⋙ forget CommRingCat).sections)
    {A : Type*} [Category* A]
    (F : A ⥤ SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)) [HasColimit F]
    (h : ∀ a, IsIso (scalarSheaf O s (F.obj a))) :
    IsIso (scalarSheaf O s (colimit F)) := by
  let t : F ⟶ F :=
    { app := fun a ↦ scalarSheaf O s (F.obj a)
      naturality := fun a b f ↦ (scalarSheaf_naturality O s (F.map f)).symm }
  let : ∀ a, IsIso (t.app a) := h
  let : IsIso t := NatIso.isIso_of_isIso_app _
  let e := HasColimit.isoOfNatIso (asIso t)
  have he : scalarSheaf O s (colimit F) = e.hom := by
    apply colimit.hom_ext
    intro a
    rw [HasColimit.isoOfNatIso_ι_hom]
    exact (scalarSheaf_naturality O s (colimit.ι F a)).symm
  rw [he]
  infer_instance

end CategoryTheory

namespace CategoryTheory

private theorem mapBifunctor_bounds
    {D₁ D₂ E : Type*} [Category* D₁] [Category* D₂] [Category* E]
    [HasZeroMorphisms D₁] [HasZeroMorphisms D₂] [Preadditive E]
    (F : D₁ ⥤ D₂ ⥤ E) [F.PreservesZeroMorphisms]
    [∀ X, (F.obj X).PreservesZeroMorphisms]
    (K : CochainComplex D₁ ℤ) (L : CochainComplex D₂ ℤ)
    [HomologicalComplex.HasMapBifunctor K L F (.up ℤ)]
    (a b c d : ℤ)
    (hK : ∀ n : ℤ, n < a ∨ b < n → IsZero (K.X n))
    (hL : ∀ n : ℤ, n < c ∨ d < n → IsZero (L.X n))
    (n : ℤ) (hn : n < a + c ∨ b + d < n) :
    IsZero ((HomologicalComplex.mapBifunctor K L F (.up ℤ)).X n) := by
  rw [IsZero.iff_id_eq_zero]
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro i j hij
  have hij' : i + j = n := hij
  have hz : IsZero ((F.obj (K.X i)).obj (L.X j)) := by
    by_cases hi : i < a ∨ b < i
    · exact ((CategoryTheory.evaluation D₂ E).obj (L.X j)).map_isZero
        (F.map_isZero (hK i hi))
    · exact (F.obj (K.X i)).map_isZero (hL j (by omega))
  simp only [Category.comp_id, comp_zero]
  exact hz.eq_of_src _ _

private theorem cech_bounds
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u}) (r : ℕ)
    (b : Fin r → (O.obj ⋙ forget CommRingCat).sections)
    (n : ℤ) (hn : n < 0 ∨ (r : ℤ) < n) :
    IsZero ((ringedExtendedCech O r b).1.X n) := by
  let : IsGrothendieckAbelian.{u} (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)) :=
    SheafOfModules.isGrothendieckAbelian _
  let := SheafOfModules.monoidalCategory O
  let := SheafOfModules.symmetricCategory O
  let := (SheafOfModules.tensorClosed O).1.some
  let := (SheafOfModules.tensorClosed O).2.1.some
  induction r generalizing n with
  | zero =>
    exact HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 _ n (by omega)
  | succ r ih =>
    change IsZero ((HomologicalComplex.tensorObj (ringedLocalizationTwoTerm O (b 0))
      (ringedExtendedCech O r (fun i ↦ b i.succ)).1).X n)
    apply mapBifunctor_bounds (curriedTensor _) _ _ 0 1 0 r
    · intro k hk
      change IsZero (ringedLocalizationTwoTermX O (b 0) k)
      have hk0 : k ≠ 0 := by omega
      have hk1 : k ≠ 1 := by omega
      simp only [ringedLocalizationTwoTermX, if_neg hk0, if_neg hk1]
      exact isZero_zero _
    · intro k hk
      exact ih _ _ hk
    · omega

end CategoryTheory

namespace CategoryTheory
private theorem scalar_tensor_term_isIso
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u}) (s : (O.obj ⋙ forget CommRingCat).sections)
    (L K : ringedSiteComplex O)
    (hL : ∀ i, IsIso (scalarSheaf O s (L.X i))) :
    let : IsGrothendieckAbelian.{u} (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)) :=
      SheafOfModules.isGrothendieckAbelian _
    let := SheafOfModules.monoidalCategory O
    let := SheafOfModules.symmetricCategory O
    let := (SheafOfModules.tensorClosed O).1.some
    let := (SheafOfModules.tensorClosed O).2.1.some
    ∀ n : ℤ, IsIso (scalarSheaf O s ((HomologicalComplex.tensorObj L K).X n)) := by
  let : IsGrothendieckAbelian.{u} (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)) :=
      SheafOfModules.isGrothendieckAbelian _
  let := SheafOfModules.monoidalCategory O
  let := SheafOfModules.symmetricCategory O
  let := (SheafOfModules.tensorClosed O).1.some
  let := (SheafOfModules.tensorClosed O).2.1.some
  dsimp only
  intro n
  change IsIso (scalarSheaf O s
    (∐ (fun ij : {p : ℤ × ℤ // p.1 + p.2 = n} ↦ L.X ij.val.1 ⊗ K.X ij.val.2)))
  apply scalar_colimit_isIso
  intro ij
  let : IsIso (scalarSheaf O s (L.X ij.as.val.1)) := hL _
  exact scalar_tensor_isIso O s _ _

end CategoryTheory

namespace CategoryTheory
private theorem tensor_split_exact_right
    {A : Type*} [Category* A] [Abelian A] [MonoidalCategory A]
    [MonoidalPreadditive A]
    [∀ K L : CochainComplex A ℤ,
      HomologicalComplex.HasMapBifunctor K L (curriedTensor A) (.up ℤ)]
    (K : CochainComplex A ℤ) (S : ShortComplex (CochainComplex A ℤ))
    (hS : ∀ n : ℤ, (S.map (HomologicalComplex.eval A (.up ℤ) n)).Splitting) :
    (S.map (((curriedTensor A).map₂CochainComplex).flip.obj K)).ShortExact := by
  classical
  let r₀ (q : ℤ) : S.X₂.X q ⟶ S.X₁.X q := (hS q).r
  let s₀ (q : ℤ) : S.X₃.X q ⟶ S.X₂.X q := (hS q).s
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  let r : (HomologicalComplex.mapBifunctor S.X₂ K (curriedTensor A) (.up ℤ)).X n ⟶
      (HomologicalComplex.mapBifunctor S.X₁ K (curriedTensor A) (.up ℤ)).X n :=
    HomologicalComplex.mapBifunctorDesc (fun p q hpq ↦ r₀ p ▷ K.X q ≫
      HomologicalComplex.ιMapBifunctor S.X₁ K (curriedTensor A) (.up ℤ) p q n hpq)
  let t : (HomologicalComplex.mapBifunctor S.X₃ K (curriedTensor A) (.up ℤ)).X n ⟶
      (HomologicalComplex.mapBifunctor S.X₂ K (curriedTensor A) (.up ℤ)).X n :=
    HomologicalComplex.mapBifunctorDesc (fun p q hpq ↦ s₀ p ▷ K.X q ≫
      HomologicalComplex.ιMapBifunctor S.X₂ K (curriedTensor A) (.up ℤ) p q n hpq)
  apply ShortComplex.Splitting.shortExact
  refine { r := r, s := t, f_r := ?_, s_g := ?_, id := ?_ }
  · change (HomologicalComplex.mapBifunctorMap S.f (𝟙 K) (curriedTensor A) (.up ℤ)).f n ≫
      r = 𝟙 _
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro p q hpq
    simp only [r, HomologicalComplex.ι_mapBifunctorMap_assoc,
      HomologicalComplex.ι_mapBifunctorDesc, HomologicalComplex.id_f,
      curriedTensor_map_app, curriedTensor_obj_map, whiskerLeft_id]
    repeat' first | erw [Category.comp_id] | erw [Category.id_comp]
    try simp only [Category.assoc]
    rw [← Category.assoc, ← comp_whiskerRight]
    have h := (hS p).f_r
    change S.f.f p ≫ r₀ p = 𝟙 _ at h
    rw [h, id_whiskerRight]
    exact Category.id_comp _
  · change t ≫
      (HomologicalComplex.mapBifunctorMap S.g (𝟙 K) (curriedTensor A) (.up ℤ)).f n = 𝟙 _
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro p q hpq
    simp only [t, Category.assoc, HomologicalComplex.ι_mapBifunctorDesc_assoc,
      HomologicalComplex.ι_mapBifunctorMap, HomologicalComplex.id_f,
      curriedTensor_map_app, curriedTensor_obj_map, whiskerLeft_id]
    repeat' first | erw [Category.comp_id] | erw [Category.id_comp]
    try simp only [Category.assoc]
    rw [← Category.assoc, ← comp_whiskerRight]
    have h := (hS p).s_g
    change s₀ p ≫ S.g.f p = 𝟙 _ at h
    rw [h, id_whiskerRight]
    exact Category.id_comp _
  · change r ≫
        (HomologicalComplex.mapBifunctorMap S.f (𝟙 K) (curriedTensor A) (.up ℤ)).f n +
      (HomologicalComplex.mapBifunctorMap S.g (𝟙 K) (curriedTensor A) (.up ℤ)).f n ≫ t = 𝟙 _
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro p q hpq
    simp only [r, t, Preadditive.comp_add, Category.assoc,
      HomologicalComplex.ι_mapBifunctorDesc_assoc, HomologicalComplex.ι_mapBifunctorMap,
      HomologicalComplex.ι_mapBifunctorMap_assoc, HomologicalComplex.ι_mapBifunctorDesc,
      HomologicalComplex.id_f, curriedTensor_map_app, curriedTensor_obj_map,
      whiskerLeft_id]
    repeat' first | erw [Category.comp_id] | erw [Category.id_comp]
    try simp only [Category.assoc]
    rw [← Category.assoc, ← comp_whiskerRight, ← Category.assoc, ← comp_whiskerRight,
      ← Preadditive.add_comp, ← MonoidalPreadditive.add_whiskerRight]
    have h := (hS p).id
    change r₀ p ≫ S.f.f p + S.g.f p ≫ s₀ p = 𝟙 _ at h
    rw [h, id_whiskerRight]
    exact Category.id_comp _


private theorem complex_leftUnitor_inv_naturality
    {A : Type*} [Category* A] [Abelian A] [MonoidalCategory A]
    [MonoidalPreadditive A]
    [∀ X, PreservesColimit (Functor.empty.{0} A) ((curriedTensor A).flip.obj X)]
    {K L : CochainComplex A ℤ} (f : K ⟶ L) :
    (HomologicalComplex.leftUnitor K).inv ≫
        HomologicalComplex.tensorHom (𝟙 (HomologicalComplex.tensorUnit A (.up ℤ))) f =
      f ≫ (HomologicalComplex.leftUnitor L).inv := by
  ext n
  change (HomologicalComplex.leftUnitor' K).inv n ≫ _ =
    f.f n ≫ (HomologicalComplex.leftUnitor' L).inv n
  rw [HomologicalComplex.leftUnitor'_inv, HomologicalComplex.leftUnitor'_inv]
  simp only [Category.assoc, HomologicalComplex.ι_mapBifunctorMap,
    HomologicalComplex.id_f, curriedTensor_map_app, curriedTensor_obj_map,
    id_whiskerRight]
  erw [Category.id_comp]
  rw [← whisker_exchange_assoc, leftUnitor_inv_naturality_assoc]

private theorem complex_leftUnitor_naturality
    {A : Type*} [Category* A] [Abelian A] [MonoidalCategory A]
    [MonoidalPreadditive A]
    [∀ X, PreservesColimit (Functor.empty.{0} A) ((curriedTensor A).flip.obj X)]
    {K L : CochainComplex A ℤ} (f : K ⟶ L) :
    HomologicalComplex.tensorHom (𝟙 (HomologicalComplex.tensorUnit A (.up ℤ))) f ≫
        (HomologicalComplex.leftUnitor L).hom =
      (HomologicalComplex.leftUnitor K).hom ≫ f := by
  apply (cancel_epi (HomologicalComplex.leftUnitor K).inv).1
  rw [← Category.assoc, complex_leftUnitor_inv_naturality]
  simp

private theorem tensorHom_factor
    {A : Type*} [Category* A] [Abelian A] [MonoidalCategory A]
    [MonoidalPreadditive A]
    [∀ K L : CochainComplex A ℤ,
      HomologicalComplex.HasMapBifunctor K L (curriedTensor A) (.up ℤ)]
    {K L M N : CochainComplex A ℤ} (f : K ⟶ L) (g : M ⟶ N) :
    HomologicalComplex.tensorHom f g =
      HomologicalComplex.tensorHom f (𝟙 M) ≫
        HomologicalComplex.tensorHom (𝟙 L) g := by
  ext n : 1
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro i j hij
  simp only [HomologicalComplex.comp_f,
    HomologicalComplex.ι_mapBifunctorMap, HomologicalComplex.ι_mapBifunctorMap_assoc,
    HomologicalComplex.id_f, Functor.map_id, NatTrans.id_app,
    Category.id_comp]

end CategoryTheory

namespace CategoryTheory

private theorem cech_augmentation_trW
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))]
    (P : ObjectProperty (DerivedCategory (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))))
    [P.IsTriangulated] [P.IsClosedUnderIsomorphisms]
    (r : ℕ) (b : Fin r → (O.obj ⋙ forget CommRingCat).sections)
    (hP : ∀ i (N : SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)),
      IsIso (scalarSheaf O (b i) N) →
        P ((DerivedCategory.singleFunctor _ 0).obj N)) :
    P.trW (DerivedCategory.Q.map (ringedExtendedCech O r b).2) := by
  let : IsGrothendieckAbelian.{u} (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)) :=
      SheafOfModules.isGrothendieckAbelian _
  let : HasColimitsOfSize.{0, 0} (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)) :=
      hasColimitsOfSizeShrink.{0, 0, u, u} _
  let := SheafOfModules.monoidalCategory O
  let := SheafOfModules.symmetricCategory O
  let := (SheafOfModules.tensorClosed O).1.some
  let := (SheafOfModules.tensorClosed O).2.1.some
  let A := SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)
  let : ∀ K L : CochainComplex A ℤ,
      HomologicalComplex.HasMapBifunctor K L (curriedTensor A) (.up ℤ) :=
    fun _ _ _ ↦ HasColimitsOfShape.has_colimit _
  induction r with
  | zero =>
    change P.trW (DerivedCategory.Q.map (𝟙 (ringedSiteRingComplex O)))
    exact P.trW_of_isIso _
  | succ r ih =>
    let s := b 0
    let tail := fun i : Fin r ↦ b i.succ
    let K := (ringedExtendedCech O r tail).1
    let ε := (ringedExtendedCech O r tail).2
    let L := (HomologicalComplex.single A (.up ℤ) 1).obj (ringedSectionLocalization O s)
    let E := ShortComplex.mk (localization_inclusion O s)
      (ringedLocalizationTwoTermAugmentation O s) (localization_inclusion_augmentation O s)
    let T := ((curriedTensor A).map₂CochainComplex).flip.obj K
    have hE : (E.map T).ShortExact := tensor_split_exact_right K E (localization_split O s)
    have hL (n : ℤ) : IsIso (scalarSheaf O s (L.X n)) := by
      by_cases hn : n = 1
      · subst n
        have := localizationPresheaf_scalar_isIso O s
        let e := HomologicalComplex.singleObjXSelf (.up ℤ) 1
          (ringedSectionLocalization O s)
        have he := scalarSheaf_naturality O s e.hom
        have : IsIso (scalarSheaf O s (ringedSectionLocalization O s)) := by
          unfold ringedSectionLocalization
          rw [← sheafification_scalar]
          infer_instance
        have : IsIso (scalarSheaf O s (L.X 1) ≫ e.hom) := by
          rw [he]
          infer_instance
        exact IsIso.of_isIso_comp_right _ e.hom
      · have hz := HomologicalComplex.isZero_single_obj_X (.up ℤ) 1
          (ringedSectionLocalization O s) n hn
        exact hz.isIso hz _
    have hmem : P (DerivedCategory.Q.obj (E.map T).X₁) := by
      apply bounded_complex_mem_triangulated P _ 1 (r + 1)
      · intro n hn
        apply mapBifunctor_bounds (curriedTensor A) L K 1 1 0 r
        · intro m hm
          exact HomologicalComplex.isZero_single_obj_X (.up ℤ) 1
            (ringedSectionLocalization O s) m (by omega)
        · exact cech_bounds O r tail
        · omega
      · intro n hn hnr
        exact hP 0 _ (scalar_tensor_term_isIso O s L K hL n)
    have hproj := ObjectProperty.trW.mk' P
      (DerivedCategory.triangleOfSES_distinguished hE) hmem
    let p := HomologicalComplex.tensorHom (ringedLocalizationTwoTermAugmentation O s)
      (𝟙 K) ≫ (HomologicalComplex.leftUnitor K).hom
    have hp : P.trW (DerivedCategory.Q.map p) := by
      rw [Functor.map_comp]
      exact P.trW.comp_mem _ _ hproj (P.trW_of_isIso _)
    have ht := ih tail (fun i N hN ↦ hP i.succ N hN)
    have hε : (ringedExtendedCech O (r + 1) b).2 = p ≫ ε := by
      change HomologicalComplex.tensorHom
        (ringedLocalizationTwoTermAugmentation O s) ε ≫
          (HomologicalComplex.leftUnitor (ringedSiteRingComplex O)).hom = _
      have hnat : HomologicalComplex.tensorHom (𝟙 (ringedSiteRingComplex O)) ε ≫
          (HomologicalComplex.leftUnitor (ringedSiteRingComplex O)).hom =
            (HomologicalComplex.leftUnitor K).hom ≫ ε :=
        complex_leftUnitor_naturality (A := A) ε
      rw [tensorHom_factor, Category.assoc, hnat]
      simp only [p, K, Category.assoc]
    rw [hε, Functor.map_comp]
    exact P.trW.comp_mem _ _ hp ht

end CategoryTheory

namespace CategoryTheory

/-- The restricted cone of a generating-list Cech augmentation is in the finite
triangulated localization class. This statement concerns only one concrete Cech
complex, with no cover, arbitrary augmented complex or supplied model isomorphisms.

Source: Stacks Project, dualizing.tex, Tag 0A6R, the finite localization complex;
algebraization.tex, Tag 099E, its sheafified ringed-site version.
(blueprint: lem-weil-pbc-augmented-cech-slice-cone-localization).

Proof: first restrict the slice-global list along f, using the localization-factor
restriction comparisons and the generating-section free epimorphism. These give an
isomorphism of augmented arrows to the concrete transported list on V. It suffices
to put the cone of this concrete augmentation in every defining triangulated P.
For a list of length r+1, tensor the degreewise split short exact sequence
L → [O → O[1/b_0]] → O[0], with L equal to O[1/b_0] in degree one, on the right
by the tail Cech complex.
The left term is bounded in degrees 1 through r+1. Multiplication by b_0 is an
isomorphism on each localization sheaf, remains one after tensoring and
sheafification, and hence on each coproduct giving a total-complex term.
The generating-section witness supplies x in I(V) mapping to b_0, so every term
in degree zero belongs to P. Bounded complex devissage puts the left complex
in P. The short exact sequence therefore puts its projection in P.trW, the class
of maps with cone in P. Composing with the tensor unitor and the tail augmentation
preserves P.trW. Naturality of the unitor identifies this composite with the actual
recursively defined augmentation. The empty list has identity augmentation.
Finally, the isomorphism of restricted augmented arrows extends to their
distinguished cone triangles, giving the required membership under restriction.
-/
theorem augmented_cech_slice_cone_localization
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u})
    [∀ U : C, HasDerivedCategory.{w} (ringedSiteModules.{u}
      ((sheafCompose (J.over U) (forget₂ CommRingCat RingCat)).obj (O.over U)))]
    (I : ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))
    (ι : I ⟶ SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))
    [Mono ι] [I.IsFiniteType]
    (U : C) (r : ℕ) (b : Fin r → O.obj.obj (op U))
    (hgen : IsRingedIdealGeneratingList O I ι U r b)
    (V : C) (f : V ⟶ U) :
    ringedIdealLocalizationTriangulated O I ι V
      ((ringedKoszulDerivedOverMap O f).obj
        (DerivedCategory.Q.obj (CochainComplex.mappingCone
          (ringedExtendedCech (O.over U) r
            (fun i ↦ ringedSliceSection O U (b i))).2))) := by
  intro P hPi hPt hP
  let := hPi
  let := hPt
  let bv : Fin r → O.obj.obj (op V) := fun i ↦ O.obj.map f.op (b i)
  have hgenV := generatingList_restrict O I ι U V f r b hgen
  obtain ⟨σ, e, he⟩ := hgenV
  let εv := (ringedExtendedCech (O.over V) r
    (fun i ↦ ringedSliceSection O V (bv i))).2
  have hv : P (DerivedCategory.Q.obj (CochainComplex.mappingCone εv)) := by
    apply (P.trW_iff_of_distinguished _
      (DerivedCategory.mappingCone_triangle_distinguished εv)).1
    apply cech_augmentation_trW (O.over V) P r
      (fun i ↦ ringedSliceSection O V (bv i))
    intro i M hM
    let x : I.val.obj (op V) := (σ.s (e.symm i)).val (op (Over.mk (𝟙 V)))
    have hx : ι.val.app (op V) x = bv i := by
      have h := he (e.symm i)
      change ι.val.app (op V) x = bv (e (e.symm i)) at h
      simpa only [Equiv.apply_symm_apply] using h
    apply hP M x
    intro W a
    let := hM
    have hi : IsIso ((SheafOfModules.evaluation
      ((sheafCompose (J.over V) (forget₂ CommRingCat RingCat)).obj (O.over V))
      (op (Over.mk a))).map
        (scalarSheaf (O.over V) (ringedSliceSection O V (bv i)) M)) := inferInstance
    rw [hx]
    exact ConcreteCategory.bijective_of_isIso
      ((SheafOfModules.evaluation
        ((sheafCompose (J.over V) (forget₂ CommRingCat RingCat)).obj (O.over V))
        (op (Over.mk a))).map
          (scalarSheaf (O.over V) (ringedSliceSection O V (bv i)) M))
  let F := ringedKoszulDerivedOverMap O f
  let : F.CommShift ℤ := by dsimp [F, ringedKoszulDerivedOverMap]; infer_instance
  let : F.IsTriangulated := by dsimp [F, ringedKoszulDerivedOverMap]; infer_instance
  let εu := (ringedExtendedCech (O.over U) r
    (fun i ↦ ringedSliceSection O U (b i))).2
  let T := F.mapTriangle.obj
    (DerivedCategory.Q.mapTriangle.obj (CochainComplex.mappingCone.triangle εu))
  let S := DerivedCategory.Q.mapTriangle.obj (CochainComplex.mappingCone.triangle εv)
  have hT : T ∈ distTriang _ := F.map_distinguished _
    (DerivedCategory.mappingCone_triangle_distinguished εu)
  have hS : S ∈ distTriang _ := DerivedCategory.mappingCone_triangle_distinguished εv
  have h : Nonempty (Arrow.mk T.mor₁ ≅ Arrow.mk S.mor₁) := by
    exact sliceListCalculation O U V f r b
  obtain ⟨γ, hγ⟩ := exists_iso_of_arrow_iso T S hT hS h.some
  exact P.prop_of_iso (Triangle.π₃.mapIso γ).symm hv

end CategoryTheory
