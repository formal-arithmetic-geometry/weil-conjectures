/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Category.Ring.Sheaf.PrincipalPowerQuotients
public import WeilConjectures.Algebra.Homology.NormalizedQuotientErrorBasic
import WeilConjectures.Algebra.Homology.NormalizedQuotientErrorAugmentation
import WeilConjectures.CategoryTheory.SystemScalarGenerators
import WeilConjectures.Algebra.Homology.ExtensionTensorComparisonIndependent
import Mathlib.CategoryTheory.Adjunction.FullyFaithful
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Ring.Colimits
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-! # Ordinary models for the normalized quotient error triangle

Source: blueprint sk-lem-sp-tower proof, paragraph 2; Stacks 03CZ and 03EK.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option linter.unusedSectionVars false
universe u v r
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open SheafOfModules.RegularQuotientCone
open SheafOfModules.IndependentExtensionTensor
open scoped ChangeOfRings
open CategoryTheory.MonoidalCategory
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

private theorem restriction_faithful {R T : Sheaf J CommRingCat.{r}} (a : R ⟶ T) :
    (restriction a).Faithful := by
  let F := restriction a
  have : (F ⋙ toSheaf (derivedChangeRingIndependentCoefficients J R)).Faithful := by
    change (toSheaf (derivedChangeRingIndependentCoefficients J T)).Faithful
    infer_instance
  exact Functor.Faithful.of_comp F (toSheaf _)

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

private def balancedScalarIso {R T U : Sheaf J CommRingCat.{r}}
    {a : R ⟶ T} {b : T ⟶ U} {c : R ⟶ U} (h : c = a ≫ b)
    (A : SystemScalarModel a) (B : SystemScalarModel b) (D : SystemScalarModel c)
    [(restriction a).Full] [(restriction a).Faithful] :
    restriction a ⋙ D.model.E ≅ B.model.E :=
  Functor.isoWhiskerLeft (restriction a) (systemScalarModelComposition h A B D).symm ≪≫
    (Functor.associator (restriction a) A.model.E B.model.E).symm ≪≫
    Functor.isoWhiskerRight (asIso A.ordinaryAdj.counit) B.model.E ≪≫ B.model.E.leftUnitor

private theorem balancedScalarIso_unit {R T U : Sheaf J CommRingCat.{r}}
    {a : R ⟶ T} {b : T ⟶ U} {c : R ⟶ U} (h : c = a ≫ b)
    (A : SystemScalarModel a) (B : SystemScalarModel b) (D : SystemScalarModel c)
    [(restriction a).Full] [(restriction a).Faithful]
    (M : Modules T) (V : Sᵒᵖ) (x : M.val.obj V) :
    ((balancedScalarIso h A B D).hom.app M).val.app V
      (systemModelTmul D.model ((restriction a).obj M) V 1 x) =
      systemModelTmul B.model M V 1 x := by
  let e := (systemScalarModelComposition h A B D).app ((restriction a).obj M)
  have he : e.inv.val.app V
      (systemModelTmul D.model ((restriction a).obj M) V 1 x) =
      systemModelTmul B.model (A.model.E.obj ((restriction a).obj M)) V 1
        (systemModelTmul A.model ((restriction a).obj M) V 1 x) := by
    have hh := systemScalarModelComposition_tmul h A B D ((restriction a).obj M) V 1 1 x
    simp only [map_one, mul_one] at hh
    refine (congrArg (fun z ↦ e.inv.val.app V z) hh).symm.trans ?_
    exact congrArg (fun k ↦ k.val.app V
      (systemModelTmul B.model (A.model.E.obj ((restriction a).obj M)) V 1
        (systemModelTmul A.model ((restriction a).obj M) V 1 x))) e.hom_inv_id
  change (B.model.E.map (A.ordinaryAdj.counit.app M)).val.app V
    (e.inv.val.app V
      (systemModelTmul D.model ((restriction a).obj M) V 1 x)) = _
  rw [he]
  erw [systemScalarModel_map_tmul]
  congr 1
  have hc := systemScalarModel_transpose_tmul A ((restriction a).obj M) M
    (A.ordinaryAdj.counit.app M) V 1 x
  have hec : (A.ordinaryAdj.homEquiv _ _) (A.ordinaryAdj.counit.app M) = 𝟙 _ := by
    rw [Adjunction.homEquiv_unit]
    exact A.ordinaryAdj.right_triangle_components M
  erw [hec] at hc
  exact hc.trans (by simp)

attribute [local instance] isMonoidal_W_independentCoefficients monoidalCategory
  preservesZeroMorphisms_curriedTensor_independentCoefficients
  preservesZeroMorphisms_curriedTensor_obj_independentCoefficients
  tensorLeft_additive_independent

private theorem tensorUnit_eq (R : Sheaf J CommRingCat.{r}) :
    @MonoidalCategory.tensorUnit _ _ (monoidalCategory R).toMonoidalCategoryStruct =
      unit (derivedChangeRingIndependentCoefficients J R) := rfl

attribute [local irreducible] SheafOfModules.monoidalCategory

private theorem tensor_hom_ext (R : Sheaf J CommRingCat.{r})
    (M N H : Modules R) {f g : (monoidalCategory R).tensorObj M N ⟶ H}
    (h : ∀ V x y, f.val.app V ((tensorPresheafUnit M N).app V
        (x ⊗ₜ[R.obj.obj V] y)) =
      g.val.app V ((tensorPresheafUnit M N).app V (x ⊗ₜ[R.obj.obj V] y))) : f = g := by
  let adj := PresheafOfModules.sheafificationAdjunction
    (𝟙 (derivedChangeRingIndependentCoefficients J R).obj)
  apply (cancel_epi (tensorObjIsoSheafification M N).inv).mp
  apply (adj.homEquiv (M.val ⊗ N.val) H).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  apply PresheafOfModules.hom_ext
  intro V
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro x y
  exact h V x y

private def pure (R : Sheaf J CommRingCat.{r}) (M N : Modules R)
    (V : Sᵒᵖ) (x : M.val.obj V) (y : N.val.obj V) :=
  (tensorPresheafUnit M N).app V (x ⊗ₜ[R.obj.obj V] y)

private theorem tensor_map_tmul (A : Sheaf J CommRingCat.{r})
    {M M' N N' : Modules A} (f : M ⟶ M') (g : N ⟶ N')
    (V : Sᵒᵖ) (x : M.val.obj V) (y : N.val.obj V) :
    ((monoidalCategory A).tensorHom f g).val.app V (pure A M N V x y) =
      pure A M' N' V (f.val.app V x) (g.val.app V y) := by
  let := monoidalCategory A
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙
    ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj A).obj)
  have ht : (f ⊗ₘ g) ≫ (tensorObjIsoSheafification M' N').hom =
      (tensorObjIsoSheafification M N).hom ≫
        (PresheafOfModules.sheafification (𝟙 _)).map (f.val ⊗ₘ g.val) := by
    let sh := PresheafOfModules.sheafification (𝟙
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj A).obj)
    let ε := asIso adj.counit
    have hf : f ≫ (ε.app M').inv = (ε.app M).inv ≫ sh.map f.val :=
      ε.inv.naturality f
    have hg : g ≫ (ε.app N').inv = (ε.app N).inv ≫ sh.map g.val :=
      ε.inv.naturality g
    change (f ⊗ₘ g) ≫ ((ε.app M').inv ⊗ₘ (ε.app N').inv) ≫
        Functor.LaxMonoidal.μ sh M'.val N'.val =
      ((ε.app M).inv ⊗ₘ (ε.app N).inv) ≫
        Functor.LaxMonoidal.μ sh M.val N.val ≫ sh.map (f.val ⊗ₘ g.val)
    rw [← Functor.LaxMonoidal.μ_natural]
    simp only [← Category.assoc, tensorHom_comp_tensorHom, hf, hg]
  have hi : (tensorObjIsoSheafification M N).inv ≫ (f ⊗ₘ g) =
      (PresheafOfModules.sheafification (𝟙 _)).map (f.val ⊗ₘ g.val) ≫
        (tensorObjIsoSheafification M' N').inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, ← ht, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]
  have hh := congrArg (fun h ↦ h.val.app V
    ((adj.unit.app (M.val ⊗ N.val)).app V (x ⊗ₜ[A.obj.obj V] y))) hi
  have hη := congrArg (fun h ↦ h.app V (x ⊗ₜ[A.obj.obj V] y))
    (adj.unit.naturality (f.val ⊗ₘ g.val))
  exact hh.trans (congrArg ((tensorObjIsoSheafification M' N').inv.val.app V) hη.symm)

private theorem systemModelTmul_eq {R T : Sheaf J CommRingCat.{r}}
    {a : R ⟶ T} (D : SystemScalarModel a) (M : Modules R)
    (V : Sᵒᵖ) (c : T.obj.obj V) (x : M.val.obj V) :
    systemModelTmul D.model M V c x =
      (eqToHom (D.model.obj_eq M).symm).val.app V
        ((toSheafify J (changeOfRingsPresheaf a M).presheaf).app V
          (c ⊗ₜ[R.obj.obj V, (a.hom.app V).hom] x)) := by
  let η := (PresheafOfModules.sheafificationAdjunction
    (𝟙 (derivedChangeRingIndependentCoefficients J T).obj)).unit.app
      (changeOfRingsPresheaf a M)
  change c • (eqToHom (D.model.obj_eq M).symm).val.app V
      (η.app V ((1 : T.obj.obj V) ⊗ₜ[R.obj.obj V, (a.hom.app V).hom] x)) =
    (eqToHom (D.model.obj_eq M).symm).val.app V
      (η.app V (c ⊗ₜ[R.obj.obj V, (a.hom.app V).hom] x))
  erw [← map_smul, ← map_smul]
  congr 2
  change (c * (1 : T.obj.obj V)) ⊗ₜ[R.obj.obj V, (a.hom.app V).hom] x = _
  rw [mul_one]

private def tensorModelIso {R T : Sheaf J CommRingCat.{r}}
    {a : R ⟶ T} (D : SystemScalarModel a) (M : Modules R) :
    (monoidalCategory R).tensorObj
      ((restriction a).obj (unit (derivedChangeRingIndependentCoefficients J T))) M ≅
      (restriction a).obj (D.model.E.obj M) :=
  (exists_extensionTensorComparison a M).choose ≪≫
    (restriction a).mapIso (eqToIso (D.model.obj_eq M).symm)

private theorem tensorModelIso_tmul {R T : Sheaf J CommRingCat.{r}}
    {a : R ⟶ T} (D : SystemScalarModel a) (M : Modules R)
    (V : Sᵒᵖ) (c : T.obj.obj V) (x : M.val.obj V) :
    (tensorModelIso D M).hom.val.app V
      ((tensorPresheafUnit
        ((restriction a).obj (unit (derivedChangeRingIndependentCoefficients J T)))
        M).app V (c ⊗ₜ[R.obj.obj V] x)) = systemModelTmul D.model M V c x := by
  change (eqToHom (D.model.obj_eq M).symm).val.app V
      (((exists_extensionTensorComparison a M).choose).hom.val.app V _) = _
  rw [(exists_extensionTensorComparison a M).choose_spec]
  exact (systemModelTmul_eq D M V c x).symm

private def tensorModelNatIso {R T : Sheaf J CommRingCat.{r}}
    {a : R ⟶ T} (D : SystemScalarModel a) :
    (MonoidalCategory.curriedTensor (Modules R)).obj
        ((restriction a).obj (unit (derivedChangeRingIndependentCoefficients J T))) ≅
      D.model.E ⋙ restriction a :=
  NatIso.ofComponents (tensorModelIso D) (by
    intro M N f
    change (((restriction a).obj (unit (derivedChangeRingIndependentCoefficients J T))) ◁ f) ≫
      (tensorModelIso D N).hom = (tensorModelIso D M).hom ≫ (restriction a).map
        (D.model.E.map f)
    rw [← id_tensorHom]
    apply tensor_hom_ext R
    intro V c x
    have hf := tensor_map_tmul R
      (𝟙 ((restriction a).obj (unit (derivedChangeRingIndependentCoefficients J T))))
      f V c x
    change (tensorModelIso D N).hom.val.app V
        (((𝟙 _ ⊗ₘ f)).val.app V (pure R _ M V c x)) =
      (D.model.E.map f).val.app V ((tensorModelIso D M).hom.val.app V (pure R _ M V c x))
    rw [hf]
    change (tensorModelIso D N).hom.val.app V
      ((tensorPresheafUnit _ N).app V
        ((@id (T.obj.obj V) c) ⊗ₜ[R.obj.obj V] (f.val.app V x))) =
      (D.model.E.map f).val.app V ((tensorModelIso D M).hom.val.app V
        ((tensorPresheafUnit _ M).app V ((@id (T.obj.obj V) c) ⊗ₜ[R.obj.obj V] x)))
    erw [tensorModelIso_tmul, tensorModelIso_tmul, systemScalarModel_map_tmul])

private def balancedTensorNatIso {R T U : Sheaf J CommRingCat.{r}}
    {a : R ⟶ T} {b : T ⟶ U} {c : R ⟶ U} (h : c = a ≫ b)
    (A : SystemScalarModel a) (B : SystemScalarModel b) (D : SystemScalarModel c)
    [(restriction a).Full] [(restriction a).Faithful] :
    restriction a ⋙ (curriedTensor (Modules R)).obj
        ((restriction c).obj (unit (derivedChangeRingIndependentCoefficients J U))) ≅
      B.model.E ⋙ restriction c :=
  Functor.isoWhiskerLeft (restriction a) (tensorModelNatIso D) ≪≫
    (Functor.associator (restriction a) D.model.E (restriction c)).symm ≪≫
    Functor.isoWhiskerRight (balancedScalarIso h A B D) (restriction c)

private theorem balancedTensorNatIso_unit {R T U : Sheaf J CommRingCat.{r}}
    {a : R ⟶ T} {b : T ⟶ U} {c : R ⟶ U} (h : c = a ≫ b)
    (A : SystemScalarModel a) (B : SystemScalarModel b) (D : SystemScalarModel c)
    [(restriction a).Full] [(restriction a).Faithful]
    (M : Modules T) (V : Sᵒᵖ) (x : M.val.obj V) :
    ((balancedTensorNatIso h A B D).hom.app M).val.app V
      ((tensorPresheafUnit
        ((restriction c).obj (unit (derivedChangeRingIndependentCoefficients J U)))
        ((restriction a).obj M)).app V ((1 : U.obj.obj V) ⊗ₜ[R.obj.obj V] x)) =
      systemModelTmul B.model M V 1 x := by
  change ((balancedScalarIso h A B D).hom.app M).val.app V
    ((tensorModelIso D ((restriction a).obj M)).hom.val.app V
      ((tensorPresheafUnit _ ((restriction a).obj M)).app V
        ((1 : U.obj.obj V) ⊗ₜ[R.obj.obj V] x))) = _
  rw [tensorModelIso_tmul, balancedScalarIso_unit]

private def balancedTensorComplexIso {R T U : Sheaf J CommRingCat.{r}}
    {a : R ⟶ T} {b : T ⟶ U} {c : R ⟶ U} (h : c = a ≫ b)
    (A : SystemScalarModel a) (B : SystemScalarModel b) (D : SystemScalarModel c)
    [(restriction a).Full] [(restriction a).Faithful]
    (P : CochainComplex (Modules T) ℤ) :
    (koszulTensorFunctor R (((restriction a).mapHomologicalComplex (.up ℤ)).obj P)).obj
      ((CochainComplex.singleFunctor (Modules R) 0).obj
        ((restriction c).obj (unit (derivedChangeRingIndependentCoefficients J U)))) ≅
      ((restriction c).mapHomologicalComplex (.up ℤ)).obj
        ((B.model.E.mapHomologicalComplex (.up ℤ)).obj P) :=
  CochainComplex.mapBifunctorSingle₁Iso (curriedTensor (Modules R)) _ _ ≪≫
    (Functor.mapHomologicalComplexCompIso
      (balancedTensorNatIso h A B D) (.up ℤ)).app P ≪≫
    ((Functor.mapHomologicalComplexCompIso
      (Iso.refl (B.model.E ⋙ restriction c)) (.up ℤ)).app P).symm

attribute [local semireducible] SheafOfModules.monoidalCategory in
private theorem regularTensorIso_eq
    {A : Type*} [Category A] [EssentiallySmall.{u} A]
    {J : GrothendieckTopology A}
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}]
    (R : Sheaf J CommRingCat.{u})
    (M : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :
    SheafOfModules.IndependentExtensionTensor.regularTensorIso M = (λ_ M) := by
  apply Iso.ext
  dsimp only [SheafOfModules.IndependentExtensionTensor.regularTensorIso,
    SheafOfModules.tensorObjIsoSheafification, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, tensorIso_inv, Iso.app_inv, asIso_inv]
  simp only [Functor.Monoidal.μIso_hom, Functor.Monoidal.map_leftUnitor,
    Category.assoc]
  let F := PresheafOfModules.sheafification
    (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj)
  let e := asIso (PresheafOfModules.sheafificationAdjunction
    (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj)).counit
  change (e.app (SheafOfModules.unit _) ⊗ᵢ e.app M).inv ≫
    Functor.LaxMonoidal.μ F (𝟙_ _) M.val ≫
    Functor.OplaxMonoidal.δ F (𝟙_ _) M.val ≫
    (SheafOfModules.sheafificationObjUnitIso R).hom ▷ F.obj M.val ≫
    (λ_ (F.obj M.val)).hom ≫ (e.app M).hom = _
  rw [Functor.Monoidal.μ_δ_assoc]
  simp only [SheafOfModules.sheafificationObjUnitIso, tensorIso_inv, tensorHom_def',
    Category.assoc, ← leftUnitor_naturality]
  change (𝟙_ _) ◁ (e.app M).inv ≫
    (e.app (SheafOfModules.unit _)).inv ▷ F.obj M.val ≫
    (e.app (SheafOfModules.unit _)).hom ▷ F.obj M.val ≫
    (𝟙_ _) ◁ (e.app M).hom ≫ (λ_ M).hom = _
  simp only [← comp_whiskerRight_assoc, Iso.inv_hom_id, id_whiskerRight,
    Category.id_comp, ← whiskerLeft_comp_assoc, whiskerLeft_id]

attribute [local semireducible] SheafOfModules.monoidalCategory in
attribute [local implicit_reducible] SheafOfModules.monoidalCategory
  SheafOfModules.unit CategoryTheory.sheafCompose in
private theorem tensorUnit_collapse (R : Sheaf J CommRingCat.{r})
    {T : Sheaf J CommRingCat.{r}} (a : R ⟶ T)
    (P : CochainComplex (Modules R) ℤ) (i : ℤ) :
    ((tensorQuotientUnit a P ≫
      (CochainComplex.mapBifunctorSingle₁Iso (curriedTensor (Modules R))
        ((restriction a).obj (unit (derivedChangeRingIndependentCoefficients J T))) P).hom).f i) =
      (λ_ (P.X i)).inv ≫ ringMap a ▷ P.X i := by
  apply (cancel_mono
    ((CochainComplex.mapBifunctorSingle₁Iso (curriedTensor (Modules R))
      ((restriction a).obj (unit (derivedChangeRingIndependentCoefficients J T))) P).inv.f
        i)).1
  simp only [Category.assoc, ← HomologicalComplex.comp_f, Iso.hom_inv_id, Category.comp_id]
  have hc : koszulTensorUnitComponent R P i =
      (λ_ (P.X i)).inv ≫
        (eqToHom (tensorUnit_eq R) ≫
          (HomologicalComplex.singleObjXSelf (.up ℤ) 0
            (unit (derivedChangeRingIndependentCoefficients J R))).inv) ▷ P.X i ≫
        HomologicalComplex.ιMapBifunctor
          ((CochainComplex.singleFunctor (Modules R) 0).obj
            (unit (derivedChangeRingIndependentCoefficients J R))) P
          (curriedTensor (Modules R)) (.up ℤ) 0 i i (zero_add i) := rfl
  simp only [tensorQuotientUnit, HomologicalComplex.comp_f, koszulTensorUnitInclusion,
    koszulTensorFunctor, Functor.flip_obj_map, Functor.map₂HomologicalComplex_map_app,
    CochainComplex.mapBifunctorSingle₁Iso_inv_f]
  rw [hc]
  simp only [Category.assoc]
  erw [HomologicalComplex.ι_mapBifunctorMap]
  simp only [CochainComplex.singleFunctor, CochainComplex.singleFunctors,
    HomologicalComplex.single_map_f_self, HomologicalComplex.id_f,
    curriedTensor_map_app, ← comp_whiskerRight_assoc]
  dsimp only [curriedTensor_obj_map]
  simp only [whiskerLeft_id]
  rfl

attribute [local semireducible] SheafOfModules.monoidalCategory in
attribute [local implicit_reducible] SheafOfModules.monoidalCategory
  SheafOfModules.unit CategoryTheory.sheafCompose in
private theorem tensorUnit_collapse_apply (R : Sheaf J CommRingCat.{r})
    {T : Sheaf J CommRingCat.{r}} (a : R ⟶ T)
    (P : CochainComplex (Modules R) ℤ) (i : ℤ) (V : Sᵒᵖ)
    (x : (P.X i).val.obj V) :
    (((tensorQuotientUnit a P ≫
      (CochainComplex.mapBifunctorSingle₁Iso (curriedTensor (Modules R))
        ((restriction a).obj (unit (derivedChangeRingIndependentCoefficients J T)))
        P).hom).f i).val.app V x) =
      (tensorPresheafUnit
        ((restriction a).obj (unit (derivedChangeRingIndependentCoefficients J T)))
        (P.X i)).app V ((1 : T.obj.obj V) ⊗ₜ[R.obj.obj V] x) := by
  rw [tensorUnit_collapse]
  change (ringMap a ▷ P.X i).val.app V ((λ_ (P.X i)).inv.val.app V x) = _
  erw [← regularTensorIso_eq R, regularTensorIso_inv_apply]
  have h := tensor_map_tmul R (ringMap a) (𝟙 (P.X i)) V (1 : R.obj.obj V) x
  rw [tensorHom_id] at h
  have hg : (ringMap a).val.app V (1 : R.obj.obj V) = (1 : T.obj.obj V) := by
    change (a.hom.app V).hom (1 : R.obj.obj V) * (1 : T.obj.obj V) = _
    rw [map_one, one_mul]
  simpa only [pure, hg, SheafOfModules.id_val, PresheafOfModules.id_app,
    ModuleCat.id_apply] using h

set_option maxHeartbeats 3200000 in
-- The total-complex objects retain both coefficient restrictions.
private theorem balancedTensorComplexIso_unit {R T U : Sheaf J CommRingCat.{r}}
    {a : R ⟶ T} {b : T ⟶ U} {c : R ⟶ U} (h : c = a ≫ b)
    (A : SystemScalarModel a) (B : SystemScalarModel b) (D : SystemScalarModel c)
    [(restriction a).Full] [(restriction a).Faithful]
    (P : CochainComplex (Modules T) ℤ) (i : ℤ) (V : Sᵒᵖ) (x : (P.X i).val.obj V) :
    (((tensorQuotientUnit c (((restriction a).mapHomologicalComplex (.up ℤ)).obj P) ≫
        (balancedTensorComplexIso h A B D P).hom).f i).val.app V x) =
      systemModelTmul B.model (P.X i) V 1 x := by
  let Q := ((restriction a).mapHomologicalComplex (.up ℤ)).obj P
  let L := (restriction c).obj (unit (derivedChangeRingIndependentCoefficients J U))
  have he : (balancedTensorComplexIso h A B D P).hom.f i =
      (CochainComplex.mapBifunctorSingle₁Iso (curriedTensor (Modules R)) L Q).hom.f i ≫
        (balancedTensorNatIso h A B D).hom.app (P.X i) := rfl
  simp only [HomologicalComplex.comp_f, he]
  change ((balancedTensorNatIso h A B D).hom.app (P.X i)).val.app V
    (((tensorQuotientUnit c Q ≫
      (CochainComplex.mapBifunctorSingle₁Iso (curriedTensor (Modules R)) L Q).hom).f i).val.app
        V x) = _
  rw [tensorUnit_collapse_apply]
  exact balancedTensorNatIso_unit h A B D (P.X i) V x

private theorem quotient_map_full (R : Sheaf J CommRingCat.{r})
    [HasSheafify J CommRingCat.{r}]
    (t : (unit (derivedChangeRingIndependentCoefficients J R)).sections)
    (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{r})
    (a : (Functor.const ℕᵒᵖ).obj R ⟶ B)
    (q : ∀ n : ℕ, B.obj (op n) ≅
      principalPowerRingQuotient R (ringSection R t) (n + 1))
    (hq : ∀ n : ℕ, a.app (op n) ≫ (q n).hom =
      principalPowerRingProjection R (ringSection R t) (n + 1)) (n : ℕ) :
    (restriction (a.app (op n))).Full := by
  have ha : a.app (op n) =
      principalPowerRingProjection R (ringSection R t) (n + 1) ≫ (q n).inv := by
    rw [← hq n, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have : Presheaf.IsLocallySurjective J
      (((sheafCompose J (forget₂ CommRingCat RingCat)).map (a.app (op n))).hom) := by
    rw [ha, Functor.map_comp]
    have := quotientProjection_locallySurjective R (ringSection R t) (n + 1)
    infer_instance
  exact restriction_full _

private def coefficientModelTower (R : Sheaf J CommRingCat.{r})
    (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{r})
    (a : (Functor.const ℕᵒᵖ).obj R ⟶ B)
    (P : CochainComplex (StrictRingSystem B) ℤ) (m : ℕ) :
    ℕᵒᵖ ⥤ CochainComplex (Modules R) ℤ :=
  tail m ⋙ towerView R (representative R B a P) ⋙
    coefficientTensor R ((CochainComplex.singleFunctor (Modules R) 0).obj
      ((restriction (a.app (op m))).obj
        (unit (derivedChangeRingIndependentCoefficients J (B.obj (op m))))))

private def coefficientModelMu (R : Sheaf J CommRingCat.{r})
    (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{r})
    (a : (Functor.const ℕᵒᵖ).obj R ⟶ B) (A : SystemScalarAssignment (J := J))
    (P : CochainComplex (StrictRingSystem B) ℤ) (m n : ℕ)
    [(restriction (a.app (op (m + n)))).Full] :
    (coefficientModelTower R B a P m).obj (op n) ≅
      ((restriction (a.app (op m))).mapHomologicalComplex (.up ℤ)).obj
        (((systemTensor A B (Nat.le_add_right m n)).mapHomologicalComplex (.up ℤ)).obj
          (level B P (m + n))) := by
  let := restriction_faithful (a.app (op (m + n)))
  exact balancedTensorComplexIso
    ((Category.id_comp _).symm.trans (a.naturality
      (homOfLE (Nat.le_add_right m n)).op))
    (A (a.app (op (m + n)))) (A (B.map (homOfLE (Nat.le_add_right m n)).op))
    (A (a.app (op m))) (level B P (m + n))

private theorem coefficientModelMu_unit (R : Sheaf J CommRingCat.{r})
    (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{r})
    (a : (Functor.const ℕᵒᵖ).obj R ⟶ B) (A : SystemScalarAssignment (J := J))
    (P : CochainComplex (StrictRingSystem B) ℤ) (m n : ℕ)
    [(restriction (a.app (op (m + n)))).Full]
    (i : ℤ) (U : Sᵒᵖ) (x : ((restrictedLevel R B a P (m + n)).X i).val.obj U) :
    (((tensorQuotientUnit (a.app (op m)) (restrictedLevel R B a P (m + n)) ≫
      (coefficientModelMu R B a A P m n).hom).f i).val.app U x) =
    systemModelTmul (A (B.map (homOfLE (Nat.le_add_right m n)).op)).model
      ((level B P (m + n)).X i) U 1 x := by
  let := restriction_faithful (a.app (op (m + n)))
  exact balancedTensorComplexIso_unit _ _ _ _ _ _ _ _

private def coefficientModelAugmentation (R : Sheaf J CommRingCat.{r})
    (t : (unit (derivedChangeRingIndependentCoefficients J R)).sections)
    (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{r})
    (a : (Functor.const ℕᵒᵖ).obj R ⟶ B)
    (P : CochainComplex (StrictRingSystem B) ℤ) (m : ℕ)
    (g : principalKoszul R t m ⟶
      (CochainComplex.singleFunctor (Modules R) 0).obj
        ((restriction (a.app (op m))).obj
          (unit (derivedChangeRingIndependentCoefficients J (B.obj (op m)))))) :
    middle R t m (representative R B a P) ⟶
      koszulTowerComplex R (coefficientModelTower R B a P m) :=
  koszulTowerComplexMap R (Functor.whiskerLeft
    (tail m ⋙ towerView R (representative R B a P))
    ((curriedTensor (Modules R)).map₂CochainComplex.map g))

private theorem closedUnit_component_natural
    {D₀ : Type*} [Category D₀] [Preadditive D₀] [HasZeroObject D₀] [MonoidalCategory D₀]
    [(curriedTensor D₀).PreservesZeroMorphisms]
    [∀ M, ((curriedTensor D₀).obj M).PreservesZeroMorphisms]
    (D : CochainComplex D₀ ℤ) (u : 𝟙_ D₀ ⟶ D.X 0)
    {P P' : CochainComplex D₀ ℤ} (f : P ⟶ P')
    [HomologicalComplex.HasMapBifunctor D P (curriedTensor D₀) (.up ℤ)]
    [HomologicalComplex.HasMapBifunctor D P' (curriedTensor D₀) (.up ℤ)]
    (i : ℤ) :
    f.f i ≫ (λ_ (P'.X i)).inv ≫ u ▷ P'.X i ≫
        HomologicalComplex.ιMapBifunctor D P' (curriedTensor D₀) (.up ℤ) 0 i i
          (zero_add i) =
      ((λ_ (P.X i)).inv ≫ u ▷ P.X i ≫
        HomologicalComplex.ιMapBifunctor D P (curriedTensor D₀) (.up ℤ) 0 i i
          (zero_add i)) ≫
        (HomologicalComplex.mapBifunctorMap (𝟙 D) f (curriedTensor D₀) (.up ℤ)).f i := by
  simp only [Category.assoc, HomologicalComplex.ι_mapBifunctorMap,
    HomologicalComplex.id_f, curriedTensor_obj_map, curriedTensor_map_app, id_whiskerRight]
  erw [Category.id_comp]
  rw [← whisker_exchange_assoc, ← leftUnitor_inv_naturality_assoc]

set_option maxHeartbeats 3200000 in
-- The total-complex objects retain both coefficient restrictions.
private theorem tensorUnitInclusion_natural (R : Sheaf J CommRingCat.{r})
    {P P' : CochainComplex (Modules R) ℤ} (f : P ⟶ P') :
    f ≫ koszulTensorUnitInclusion R P' = koszulTensorUnitInclusion R P ≫
      (((curriedTensor _).map₂CochainComplex).obj
        ((CochainComplex.singleFunctor _ 0).obj (unit
          (derivedChangeRingIndependentCoefficients J R)))).map f := by
  apply HomologicalComplex.hom_ext
  intro i
  change f.f i ≫ koszulTensorUnitComponent R P' i =
    koszulTensorUnitComponent R P i ≫
      (HomologicalComplex.mapBifunctorMap (𝟙 _) f (curriedTensor _) (.up ℤ)).f i
  let D := (CochainComplex.singleFunctor _ 0).obj (unit
    (derivedChangeRingIndependentCoefficients J R))
  have hu : MonoidalCategory.tensorUnit _ = unit
      (derivedChangeRingIndependentCoefficients J R) := tensorUnit_eq R
  let u : MonoidalCategory.tensorUnit _ ⟶ D.X 0 := eqToHom hu ≫
    (HomologicalComplex.singleObjXSelf (.up ℤ) 0
      (unit (derivedChangeRingIndependentCoefficients J R))).inv
  have hh := closedUnit_component_natural D u f i
  dsimp only [u, D] at hh
  simp only [tensorUnit_eq] at hh
  exact hh

private theorem tensorQuotientUnit_natural {R T : Sheaf J CommRingCat.{r}}
    (a : R ⟶ T) {P P' : CochainComplex (Modules R) ℤ} (f : P ⟶ P') :
    f ≫ tensorQuotientUnit a P' = tensorQuotientUnit a P ≫
      (coefficientTensor R ((CochainComplex.singleFunctor (Modules R) 0).obj
        ((restriction a).obj (unit (derivedChangeRingIndependentCoefficients J T))))).map f := by
  let B := (curriedTensor (Modules R)).map₂CochainComplex
  let q := (CochainComplex.singleFunctor (Modules R) 0).map (ringMap a)
  change f ≫ (koszulTensorUnitInclusion R P' ≫ (B.map q).app P') =
    (koszulTensorUnitInclusion R P ≫ (B.map q).app P) ≫ (B.obj _).map f
  rw [← Category.assoc, tensorUnitInclusion_natural, Category.assoc,
    (B.map q).naturality, Category.assoc]

private theorem coefficientModelMu_inv_unit (R : Sheaf J CommRingCat.{r})
    (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{r})
    (a : (Functor.const ℕᵒᵖ).obj R ⟶ B) (A : SystemScalarAssignment (J := J))
    (P : CochainComplex (StrictRingSystem B) ℤ) (m n : ℕ)
    [(restriction (a.app (op (m + n)))).Full]
    (i : ℤ) (U : Sᵒᵖ) (x : ((level B P (m + n)).X i).val.obj U) :
    ((coefficientModelMu R B a A P m n).inv.f i).val.app U
      (systemModelTmul (A (B.map (homOfLE (Nat.le_add_right m n)).op)).model
        ((level B P (m + n)).X i) U 1 x) =
      ((tensorQuotientUnit (a.app (op m)) (restrictedLevel R B a P (m + n))).f i).val.app U x := by
  rw [← coefficientModelMu_unit R B a A P m n i U x]
  have he := congrArg (fun f ↦ (f.f i).val.app U
    (((tensorQuotientUnit (a.app (op m))
      (restrictedLevel R B a P (m + n))).f i).val.app U x))
    (coefficientModelMu R B a A P m n).hom_inv_id
  exact he

private theorem coefficientModel_hom_ext (R : Sheaf J CommRingCat.{r})
    (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{r})
    (a : (Functor.const ℕᵒᵖ).obj R ⟶ B) (A : SystemScalarAssignment (J := J))
    (P : CochainComplex (StrictRingSystem B) ℤ) (m n : ℕ)
    [(restriction (a.app (op (m + n)))).Full] [(restriction (a.app (op m))).Full]
    (f g : (coefficientModelTower R B a P m).obj (op n) ⟶ restrictedLevel R B a P m)
    (h : tensorQuotientUnit (a.app (op m)) (restrictedLevel R B a P (m + n)) ≫ f =
      tensorQuotientUnit (a.app (op m)) (restrictedLevel R B a P (m + n)) ≫ g) : f = g := by
  apply HomologicalComplex.hom_ext
  intro i
  let μ := coefficientModelMu R B a A P m n
  let F := restriction (a.app (op m))
  let f' := F.preimage (μ.inv.f i ≫ f.f i)
  let g' := F.preimage (μ.inv.f i ≫ g.f i)
  have he : f' = g' := by
    apply systemScalarModel_hom_ext (A (B.map (homOfLE (Nat.le_add_right m n)).op))
    intro U x
    have hf := F.map_preimage (μ.inv.f i ≫ f.f i)
    have hg := F.map_preimage (μ.inv.f i ≫ g.f i)
    have hh := congrArg (fun k ↦ (k.f i).val.app U x) h
    change (F.map f').val.app U _ = (F.map g').val.app U _
    rw [hf, hg]
    change (f.f i).val.app U ((μ.inv.f i).val.app U _) =
      (g.f i).val.app U ((μ.inv.f i).val.app U _)
    rw [coefficientModelMu_inv_unit]
    exact hh
  apply (cancel_epi (μ.inv.f i)).1
  exact (F.map_preimage _).symm.trans ((congrArg F.map he).trans (F.map_preimage _))

private theorem ordinaryNormalization_unit
    (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{r}) (A : SystemScalarAssignment (J := J))
    (P : CochainComplex (StrictRingSystem B) ℤ) {m n : ℕ} (h : m ≤ n)
    (i : ℤ) (U : Sᵒᵖ) (x : ((level B P n).X i).val.obj U) :
    ((ordinaryNormalization A B P h).f i).val.app U
      (systemModelTmul (A (B.map (homOfLE h).op)).model
        ((level B P n).X i) U 1 x) =
      ((P.X i).transition h).val.app U x := by
  let adj := (systemTensorAdj A B h).mapHomologicalComplex (.up ℤ)
  have hh := (adj.homEquiv _ _).apply_symm_apply
    (transition B P h ≫
      (Functor.mapHomologicalComplexCompIso
        (Iso.refl (systemEvaluation B m ⋙ systemRestriction B h)) (.up ℤ)).inv.app P)
  rw [Adjunction.homEquiv_unit] at hh
  have he := congrArg (fun k ↦ (k.f i).val.app U x) hh
  change ((ordinaryNormalization A B P h).f i).val.app U
    (((A (B.map (homOfLE h).op)).ordinaryAdj.unit.app
      ((level B P n).X i)).val.app U x) = _ at he
  rw [(A (B.map (homOfLE h).op)).unit_normalized] at he
  exact he


set_option maxHeartbeats 3200000 in
-- The total tensor and nested scalar restrictions require a larger elaboration limit.
private theorem coefficientModelNormalization_unit (R : Sheaf J CommRingCat.{r})
    (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{r})
    (a : (Functor.const ℕᵒᵖ).obj R ⟶ B) (A : SystemScalarAssignment (J := J))
    (P : CochainComplex (StrictRingSystem B) ℤ) (m n : ℕ)
    [(restriction (a.app (op (m + n)))).Full]
    (i : ℤ) (U : Sᵒᵖ) (x : ((level B P (m + n)).X i).val.obj U) :
    (((tensorQuotientUnit (a.app (op m)) (restrictedLevel R B a P (m + n)) ≫
      (coefficientModelMu R B a A P m n).hom ≫
      ((restriction (a.app (op m))).mapHomologicalComplex (.up ℤ)).map
        (ordinaryNormalization A B P (Nat.le_add_right m n))).f i).val.app U x) =
      ((P.X i).transition (Nat.le_add_right m n)).val.app U x := by
  have hμ := coefficientModelMu_unit R B a A P m n i U x
  have hN := ordinaryNormalization_unit B A P (Nat.le_add_right m n) i U x
  change ((ordinaryNormalization A B P (Nat.le_add_right m n)).f i).val.app U
    (((tensorQuotientUnit (a.app (op m)) (restrictedLevel R B a P (m + n)) ≫
      (coefficientModelMu R B a A P m n).hom).f i).val.app U x) = _
  rw [hμ]
  exact hN

set_option maxHeartbeats 3200000 in
-- The total tensor and nested scalar restrictions require a larger elaboration limit.
private def coefficientModelNormalization (R : Sheaf J CommRingCat.{r})
    (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{r})
    (a : (Functor.const ℕᵒᵖ).obj R ⟶ B) (A : SystemScalarAssignment (J := J))
    (P : CochainComplex (StrictRingSystem B) ℤ) (m : ℕ)
    [∀ n : ℕ, (restriction (a.app (op n))).Full] :
    coefficientModelTower R B a P m ⟶
      (Functor.const ℕᵒᵖ).obj (restrictedLevel R B a P m) :=
  NatTrans.ofOpSequence
    (fun n ↦ (coefficientModelMu R B a A P m n).hom ≫
      ((restriction (a.app (op m))).mapHomologicalComplex (.up ℤ)).map
        (ordinaryNormalization A B P (Nat.le_add_right m n))) (by
    intro n
    simp only [Functor.const_obj_map]
    apply coefficientModel_hom_ext R B a A P m (n + 1)
    change tensorQuotientUnit (a.app (op m)) _ ≫
      ((coefficientModelTower R B a P m).map _ ≫ _) = _
    let h : m + n ≤ m + (n + 1) := Nat.add_le_add_left (Nat.le_succ n) m
    have hn : (tail m).map (homOfLE (Nat.le_succ n)).op = (homOfLE h).op :=
      Subsingleton.elim _ _
    change tensorQuotientUnit (a.app (op m)) _ ≫
      ((coefficientTensor R _).map
        ((towerView R (representative R B a P)).map
          ((tail m).map (homOfLE (Nat.le_succ n)).op)) ≫ _) = _
    rw [hn, ← Category.assoc]
    erw [← tensorQuotientUnit_natural (a.app (op m))
      ((towerView R (representative R B a P)).map (homOfLE h).op)]
    rw [Category.assoc]
    apply HomologicalComplex.hom_ext
    intro i
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change (((tensorQuotientUnit (a.app (op m)) _ ≫
      (coefficientModelMu R B a A P m n).hom ≫
      ((restriction (a.app (op m))).mapHomologicalComplex (.up ℤ)).map
        (ordinaryNormalization A B P (Nat.le_add_right m n))).f i).val.app U
      (((P.X i).transition h).val.app U x)) =
      (((tensorQuotientUnit (a.app (op m)) _ ≫
      (coefficientModelMu R B a A P m (n + 1)).hom ≫
      ((restriction (a.app (op m))).mapHomologicalComplex (.up ℤ)).map
        (ordinaryNormalization A B P (Nat.le_add_right m (n + 1)))).f i).val.app U x)
    exact (coefficientModelNormalization_unit R B a A P m n i U
      (((P.X i).transition h).val.app U x)).trans
      (((P.X i).compose (Nat.le_add_right m n) h U x).symm.trans
        (coefficientModelNormalization_unit R B a A P m (n + 1) i U x).symm))

set_option maxHeartbeats 3200000 in
-- The total tensor and nested scalar restrictions require a larger elaboration limit.
/-- The balanced ordinary quotient tensor tower and its actual normalization.
Source: blueprint sk-lem-sp-tower proof, paragraph 2; Stacks 03CZ and 03EK
(blueprint: lem-sp-normalized-quotient-error-models).

Proof: quotient projections are locally surjective, so their scalar restriction
functors are fully faithful. The normalized scalar-extension composition and the
counit isomorphism identify the quotient tensor over R with extension over B_n;
the identification sends every unit tensor to the normalized extension unit.
Tensor the original strict tail tower with the fixed degree-zero B_m module and
use the canonical Koszul augmentation to define epsilon. The componentwise
normalization maps assemble: test the naturality square on unit tensors, where
it is exactly composition of the original semilinear transitions. All maps are
then rearranged into complexes of towers degree by degree. -/
theorem exists_quotientModel (R : Sheaf J CommRingCat.{r})
    [HasSheafify J CommRingCat.{r}]
    (t : (unit (derivedChangeRingIndependentCoefficients J R)).sections)
    (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{r})
    (a : (Functor.const ℕᵒᵖ).obj R ⟶ B)
    (q : ∀ n : ℕ, B.obj (op n) ≅
      principalPowerRingQuotient R (ringSection R t) (n + 1))
    (hq : ∀ n : ℕ, a.app (op n) ≫ (q n).hom =
      principalPowerRingProjection R (ringSection R t) (n + 1))
    (A : SystemScalarAssignment (J := J))
    (P : CochainComplex (StrictRingSystem B) ℤ) (m : ℕ) :
    Nonempty (QuotientModel R t B a A P m) := by
  let : ∀ n : ℕ, (restriction (a.app (op n))).Full := quotient_map_full R t B a q hq
  obtain ⟨g, hgr, hgl⟩ := exists_quotientAugmentation R t (B.obj (op m))
    (a.app (op m)) m (q m) (hq m)
  exact ⟨{
    V := koszulTowerComplex R (coefficientModelTower R B a P m)
    ν := fun n ↦ coefficientModelMu R B a A P m n
    μ := fun n ↦ coefficientModelMu R B a A P m n
    μ_unit := fun n ↦ coefficientModelMu_unit R B a A P m n
    augmentation := g
    augmentation_inr := hgr
    augmentation_inl := hgl
    ε := coefficientModelAugmentation R t B a P m g
    ε_eq := fun n ↦ rfl
    N := koszulTowerComplexMap R (coefficientModelNormalization R B a A P m)
    N_eq := fun n ↦ rfl }⟩

end SheafOfModules.NormalizedQuotientError
