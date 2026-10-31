/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedLisseEvaluationModel
public import WeilConjectures.CategoryTheory.Sites.ContractibleDerivedSectionsTensor
import WeilConjectures.CategoryTheory.InternalSectionTensorComparison
import WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.CategoryTheory.Monoidal.Internal.FunctorCategory
import WeilConjectures.CategoryTheory.RingObjects.Ab
import WeilConjectures.CategoryTheory.Sites.MonObj
import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
import WeilConjectures.CategoryTheory.SheafTensor
import WeilConjectures.CategoryTheory.SheafTensorStructure
import Mathlib.CategoryTheory.Sites.Monoidal
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.CategoryTheory.Monoidal.Preadditive
import WeilConjectures.CategoryTheory.PresheafTensorInternalHom
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Preadditive
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import WeilConjectures.CategoryTheory.SheafificationTensorLocalIso
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Monoidal.Braided.Reflection
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctorialitySupplement
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.ModuleObjects.Symmetric
import WeilConjectures.CategoryTheory.ModuleObjects.Abelian
import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap
import WeilConjectures.CategoryTheory.InternalSectionModuleFlat
import WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import WeilConjectures.CategoryTheory.Monoidal.KFlatEquivalence
import Mathlib.CategoryTheory.Localization.Monoidal.Functor
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.Algebra.Homology.RingedKFlatNativeModelIdentification
import WeilConjectures.Algebra.Homology.RingedDerivedTensorNativeSupplement
import WeilConjectures.Algebra.Homology.Monoidal.MapHomologicalComplex

/-! Monoidal structure on derived sections for contractible evaluation.

Source: Hemo--Richarz--Scholbach, Lemma 4.1(1), equation (3.2), Remark 3.2.
(blueprint: lem-zl-contractible-sections-monoidal).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option linter.style.haveILetI false

universe u vA vB
open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale.CondensedRing.Evaluation

open CategoryTheory.MonoidalCategory
open CategoryTheory.InternalAbelianSheafModule SheafOfModules

private theorem ordinaryCore
    {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
    (J : GrothendieckTopology C) [(J.W (A := Ab.{u + 1})).IsMonoidal]
    (O : Sheaf J Ab.{u + 1}) [MonObj O] [IsCommMonObj O] :
    Nonempty (sectionModuleEquivalence J O).functor.CoreMonoidal := by
  obtain ⟨_, t, z, _, _, hn, ha, hl, hr, _⟩ := internal_section_tensor_comparison J O
  refine ⟨Functor.CoreMonoidal.mk' z.symm (fun M N ↦ (t M N).symm) ?_ ?_ ha ?_ ?_⟩
  · intro M N f P
    simpa only [Iso.symm_inv, CategoryTheory.Functor.map_id, tensorHom_id] using
      (hn M N P P f (𝟙 P)).symm
  · intro M N P f
    simpa only [Iso.symm_inv, CategoryTheory.Functor.map_id, id_tensorHom] using
      (hn P P M N (𝟙 P) f).symm
  · intro M
    apply (cancel_mono (λ_ _).hom).mp
    simp only [Iso.symm_inv, Category.assoc, Iso.inv_hom_id]
    rw [hl, ← CategoryTheory.Functor.map_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id]
  · intro M
    apply (cancel_mono (ρ_ _).hom).mp
    simp only [Iso.symm_inv, Category.assoc, Iso.inv_hom_id]
    rw [hr, ← CategoryTheory.Functor.map_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id]

private def identityCore {B : Type*} [Category B]
    (a r : MonoidalCategory B) (I : B) (ua : a.tensorUnit ≅ I) (ur : r.tensorUnit ≅ I)
    (e : @tensor B _ a ≅ @tensor B _ r)
    (h : RingedKFlatModel.Constraints a r I ua ur e) :
    @Functor.CoreMonoidal B _ a B _ r (𝟭 B) := by
  refine @Functor.CoreMonoidal.mk' B _ a B _ r (𝟭 B)
    (ur ≪≫ ua.symm) (fun X Y ↦ (e.app (X, Y)).symm) ?_ ?_ ?_ ?_ ?_
  · intro X Y f Z
    simpa only [Iso.symm_inv, Iso.app_hom, Functor.id_map, Functor.id_obj,
      tensor_map, @tensorHom_id B _ a, @tensorHom_id B _ r] using
      (e.hom.naturality (X := (X, Z)) (Y := (Y, Z)) (f, 𝟙 Z)).symm
  · intro X Y Z f
    simpa only [Iso.symm_inv, Iso.app_hom, Functor.id_map, Functor.id_obj,
      tensor_map, @id_tensorHom B _ a, @id_tensorHom B _ r] using
      (e.hom.naturality (X := (Z, X)) (Y := (Z, Y)) (𝟙 Z, f)).symm
  · intro X Y Z
    simpa only [Iso.symm_inv, Iso.app_hom, Functor.id_map, Functor.id_obj,
      tensor_map, @tensorHom_id B _ a, @tensorHom_id B _ r,
      @id_tensorHom B _ a, @id_tensorHom B _ r] using h.1 X Y Z
  · intro X
    apply (cancel_mono (r.leftUnitor X).hom).mp
    simp only [Functor.id_map, Functor.id_obj, Iso.app_hom, Iso.trans_inv, Iso.symm_inv,
      Category.assoc]
    apply (cancel_epi (a.leftUnitor X).hom).mp
    simp only [Iso.hom_inv_id_assoc]
    have hn := e.hom.naturality
      (X := (a.tensorUnit, X)) (Y := (I, X)) (ua.hom, 𝟙 X)
    change (@tensor B _ a).map (X := (a.tensorUnit, X)) (Y := (I, X))
        (ua.hom, 𝟙 X) ≫ e.hom.app (I, X) =
      e.hom.app (a.tensorUnit, X) ≫ (@tensor B _ r).map
        (X := (a.tensorUnit, X)) (Y := (I, X)) (ua.hom, 𝟙 X) at hn
    have hh := congrArg (fun f ↦ (@tensor B _ a).map
      (X := (a.tensorUnit, X)) (Y := (I, X)) (ua.hom, 𝟙 X) ≫ f) (h.2.1 X)
    rw [← Category.assoc, hn] at hh
    simp only [tensor_map, @tensorHom_id B _ a, @tensorHom_id B _ r,
      Category.assoc, @hom_inv_whiskerRight_assoc B _ a] at hh
    simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id,
      comp_whiskerRight] using hh.symm
  · intro X
    apply (cancel_mono (r.rightUnitor X).hom).mp
    simp only [Functor.id_map, Functor.id_obj, Iso.app_hom, Iso.trans_inv, Iso.symm_inv,
      Category.assoc]
    apply (cancel_epi (a.rightUnitor X).hom).mp
    simp only [Iso.hom_inv_id_assoc]
    have hn := e.hom.naturality
      (X := (X, a.tensorUnit)) (Y := (X, I)) (𝟙 X, ua.hom)
    change (@tensor B _ a).map (X := (X, a.tensorUnit)) (Y := (X, I))
        (𝟙 X, ua.hom) ≫ e.hom.app (X, I) =
      e.hom.app (X, a.tensorUnit) ≫ (@tensor B _ r).map
        (X := (X, a.tensorUnit)) (Y := (X, I)) (𝟙 X, ua.hom) at hn
    have hh := congrArg (fun f ↦ (@tensor B _ a).map
      (X := (X, a.tensorUnit)) (Y := (X, I)) (𝟙 X, ua.hom) ≫ f) (h.2.2 X)
    rw [← Category.assoc, hn] at hh
    simp only [tensor_map, @id_tensorHom B _ a, @id_tensorHom B _ r,
      Category.assoc, @whiskerLeft_hom_inv_assoc B _ a] at hh
    simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id,
      whiskerLeft_comp] using hh.symm

private theorem exactEquivalenceMonoidal
    {A B : Type*} [Category.{u + 1} A] [Category.{u + 1} B]
    [Abelian A] [Abelian B]
    [IsGrothendieckAbelian.{u + 1} A] [IsGrothendieckAbelian.{u + 1} B]
    [MonoidalCategory A] [MonoidalCategory B] [MonoidalPreadditive A]
    [MonoidalPreadditive B] [MonoidalClosed A] [MonoidalClosed B]
    [SymmetricCategory A] [SymmetricCategory B]
    [Abelian.HasFunctorialFlatResolution A] [Abelian.HasFunctorialFlatResolution B]
    [HasDerivedCategory.{vA} A] [HasDerivedCategory.{vB} B]
    (F : A ⥤ B) [F.Additive] [F.Monoidal] [F.IsEquivalence] :
    Nonempty F.mapDerivedCategory.Monoidal := by
  letI : HasColimitsOfSize.{0, 0} A := hasColimitsOfSizeShrink A
  letI : HasColimitsOfSize.{0, 0} B := hasColimitsOfSizeShrink B
  let W := HomologicalComplex.quasiIso A (.up ℤ)
  let I := W.ιKFlat
  let L := I ⋙ (DerivedCategory.Q (C := A))
  let G := (I ⋙ F.mapHomologicalComplex (.up ℤ)) ⋙ (DerivedCategory.Q (C := B))
  let Λ := (inferInstance : Abelian.HasFunctorialFlatResolution A).some.reduced
  have : W.localizerMorphismKFlat.IsLocalizedEquivalence :=
    W.localizerMorphismKFlat.isLocalizedEquivalence_of_functorial_left_resolutions
      (Λ.kFlatResolutionNatTrans ObjectProperty.flat.essImage_ι_le)
      (fun K ↦ by
        dsimp only [W]
        rw [HomologicalComplex.mem_quasiIso_iff]
        infer_instance) rfl
  have : L.IsLocalization W.WKFlat :=
    LocalizerMorphism.IsLocalizedEquivalence.isLocalization W.localizerMorphismKFlat
      DerivedCategory.Q
  letI : IsIso (Functor.LaxMonoidal.ε (DerivedCategory.Q (C := A))) :=
    RingedDerivedNative.localization_isIso_ε
  letI : IsIso (Functor.LaxMonoidal.ε (DerivedCategory.Q (C := B))) :=
    RingedDerivedNative.localization_isIso_ε
  have (P Q : W.KFlat) : IsIso (Functor.LaxMonoidal.μ L P Q) := by
    have hh := RingedDerivedNative.localization_isIso_mu P.obj Q.obj
      (Or.inl ((HomotopyCategory.kFlat_quotient_obj_iff P.obj).2 P.property))
    change IsIso (Functor.LaxMonoidal.μ DerivedCategory.Q P.obj Q.obj ≫
      DerivedCategory.Q.map (Functor.LaxMonoidal.μ I P Q))
    infer_instance
  have : IsIso (Functor.LaxMonoidal.ε L) := by
    dsimp only [L, Functor.LaxMonoidal.comp_ε]
    infer_instance
  letI : L.Monoidal := Functor.Monoidal.ofLaxMonoidal L
  have (P Q : W.KFlat) : IsIso (Functor.LaxMonoidal.μ G P Q) := by
    have hP := F.kFlat_mapHomologicalComplex_obj_of_isEquivalence P.property
    have hh := RingedDerivedNative.localization_isIso_mu
      ((F.mapHomologicalComplex (.up ℤ)).obj P.obj)
      ((F.mapHomologicalComplex (.up ℤ)).obj Q.obj)
      (Or.inl ((HomotopyCategory.kFlat_quotient_obj_iff _).2 hP))
    change IsIso (Functor.LaxMonoidal.μ DerivedCategory.Q
      ((F.mapHomologicalComplex (.up ℤ)).obj P.obj)
      ((F.mapHomologicalComplex (.up ℤ)).obj Q.obj) ≫ _)
    infer_instance
  have : IsIso (Functor.LaxMonoidal.ε G) := by
    dsimp only [G, Functor.LaxMonoidal.comp_ε]
    infer_instance
  letI : G.Monoidal := Functor.Monoidal.ofLaxMonoidal G
  letI : Localization.Lifting L W.WKFlat G F.mapDerivedCategory :=
    ⟨Functor.associator I DerivedCategory.Q F.mapDerivedCategory ≪≫
      Functor.isoWhiskerLeft I F.mapDerivedCategoryFactors ≪≫
        (Functor.associator I (F.mapHomologicalComplex (.up ℤ)) DerivedCategory.Q).symm⟩
  exact ⟨(Localization.Monoidal.functorCoreMonoidalOfComp
    L W.WKFlat F.mapDerivedCategory G).toMonoidal⟩

@[instance_reducible]
private def composeMonoidal
    {A : Type*} [Category A] [MonoidalCategory A]
    {B : Type*} [Category B] [MonoidalCategory B]
    {D : Type*} [Category D] [MonoidalCategory D]
    (F : A ⥤ B) (G : B ⥤ D) (mF : F.Monoidal) (mG : G.Monoidal) :
    (F ⋙ G).Monoidal := by
  letI := mF
  letI := mG
  infer_instance

private theorem evaluationNative
    {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
    (J : GrothendieckTopology C) [(J.W (A := Ab.{u + 1})).IsMonoidal]
    (O : Sheaf J Ab.{u + 1}) [MonObj O] [IsCommMonObj O]
    (U : C)
    [HasDerivedCategory.{u + 1} (RingedTensorModules.{u + 1, u, 0} J (ringSheaf J O))]
    [PreservesFiniteLimits (contractibleModuleEvaluation.{u + 1, u, 0}
      J (ringSheaf J O) (op U))]
    [PreservesFiniteColimits (contractibleModuleEvaluation.{u + 1, u, 0}
      J (ringSheaf J O) (op U))]
    (S : WeilConjectures.CoefficientClosedStructure
      (derivedInternalHomOfUniverses.{u + 1, u, 0, u + 1} J (ringSheaf J O)))
    (T : WeilConjectures.CoefficientTensorModels.{0, u + 1, u, u + 1} J (ringSheaf J O) S)
    (β : @SymmetricCategory (DerivedCategory
      (RingedTensorModules.{u + 1, u, 0} J (ringSheaf J O))) _ S.monoidal)
    (H : RingedDerivedTensorCoherence.{u + 1, u, 0, u + 1} J (ringSheaf J O) S T β)
    (d : ContractibleDerivedSectionsTensorData.{u + 1, u, 0}
      J (ringSheaf J O) (op U) S T β H) :
    letI := RingedDerivedNative.monoidal.{u + 1, u, 0, u + 1} J (ringSheaf J O)
    Nonempty (contractibleModuleEvaluation.{u + 1, u, 0}
      J (ringSheaf J O) (op U)).mapDerivedCategory.Monoidal := by
  letI : Abelian.HasFunctorialFlatResolution
      (RingedTensorModules.{u + 1, u, 0} J (ringSheaf J O)) :=
    SheafOfModules.hasFunctorialFlatResolution_kfi (ringSheaf J O)
  let Λ : Abelian.LeftResolution
      (ObjectProperty.flat.ι : _ ⥤ RingedTensorModules.{u + 1, u, 0} J (ringSheaf J O)) :=
    Classical.arbitrary _
  have hn := RingedKFlatModel.ringed_kFlat_native_model_identification
    J (ringSheaf J O) S T Λ β H
  obtain ⟨ε, hε, _⟩ := hn.2.1
  obtain ⟨e, _, _, _, _, _, hc⟩ := hn.2.2 ε hε
  let c := identityCore
    (RingedDerivedNative.monoidal.{u + 1, u, 0, u + 1} J (ringSheaf J O)) S.monoidal
    (DerivedCategory.Q.obj (ringedTensorUnitComplex.{u + 1, u, 0} J (ringSheaf J O)))
    (RingedDerivedNative.unitIso.{u + 1, u, 0, u + 1} J (ringSheaf J O)) H.unitIso e hc
  letI := RingedDerivedNative.monoidal.{u + 1, u, 0, u + 1} J (ringSheaf J O)
  exact ⟨@composeMonoidal _ _
    (RingedDerivedNative.monoidal.{u + 1, u, 0, u + 1} J (ringSheaf J O))
    _ _ S.monoidal _ _ _
    (𝟭 (DerivedCategory (RingedTensorModules.{u + 1, u, 0} J (ringSheaf J O))))
    (contractibleModuleEvaluation.{u + 1, u, 0} J (ringSheaf J O) (op U)).mapDerivedCategory
    (@Functor.CoreMonoidal.toMonoidal _ _
      (RingedDerivedNative.monoidal.{u + 1, u, 0, u + 1} J (ringSheaf J O))
      _ _ S.monoidal _ c) d.monoidal⟩


/-- Termwise derived internal-module sections inherit the normalized contractible tensor data.
Source: Hemo--Richarz--Scholbach, Lemma 4.1(1), equation (3.2), Remark 3.2.

Proof: the section-module equivalence identifies the internal module tensor with the
sheafified sectionwise tensor: both represent balanced bilinear maps of the same
underlying sheaves. Its unit comparison identifies O with its reconstructed ring module.
Apply these comparisons termwise and then localize. If the two chosen localization
sizes differ, descend the identity of cochain complexes in each direction; full
faithfulness of restriction along localization supplies inverse natural comparisons.
On flat-term K-flat representatives the tensor comparisons are the normalized total
pairings of heval; the unit is its scalar-normalized unitComplex. The identities
pairing_tmul, tensor_model, unit_scalar and unit_model identify the two representative
maps. Consequently their associativity and unit diagrams agree before localization,
and locality of equality along Q proves those diagrams after localization. The
monoidal comparisons in heval and the tensor equivalence are invertible. Compose
them to obtain the strong monoidal structure on termwise derived sections.
Source: Hemo--Richarz--Scholbach, Lemma 4.1(1), equation (3.2), Remark 3.2.
(blueprint: lem-zl-contractible-sections-monoidal). -/
theorem contractible_sections_monoidal
    {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
    (J : GrothendieckTopology C) [(J.W (A := Ab.{u + 1})).IsMonoidal]
    (O : Sheaf J Ab.{u + 1}) [MonObj O] [IsCommMonObj O]
    (U : C)
    [HasDerivedCategory.{u + 1} (SheafOfModules.{u + 1}
      ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (ringSheaf J O)))]
    (heval : ContractibleDerivedSectionsTensor.{u + 1, u, 0} J (ringSheaf J O) (op U)) :
    ∀ (hlim : PreservesFiniteLimits (sections J O U))
      (hfin : PreservesFiniteColimits (sections J O U)),
      letI := hlim
      letI := hfin
      Nonempty (sections J O U).mapDerivedCategory.Monoidal := by
  intro hlim hfin
  letI := hlim
  letI := hfin
  obtain ⟨hl, hf, _, S, T, β, H, ⟨d⟩⟩ := heval
  letI := hl
  letI := hf
  let E := sectionModuleEquivalence.{u + 1, u + 1, u} J O
  obtain ⟨oc⟩ := ordinaryCore J O
  letI := oc.toMonoidal
  letI : E.functor.Additive := Functor.additive_of_preserves_binary_products _
  letI : MonoidalClosed (RingedTensorModules.{u + 1, u, 0} J (ringSheaf J O)) :=
    (SheafOfModules.nonempty_monoidalClosed_independentCoefficients
      (R := ringSheaf J O)).some
  letI : IsGrothendieckAbelian.{u + 1}
      (RingedTensorModules.{u + 1, u, 0} J (ringSheaf J O)) :=
    (grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{u + 1, u, 0}
      J (ringSheaf J O)).1
  letI : Abelian.HasFunctorialFlatResolution
      (RingedTensorModules.{u + 1, u, 0} J (ringSheaf J O)) :=
    SheafOfModules.hasFunctorialFlatResolution_kfi (ringSheaf J O)
  obtain ⟨mE⟩ := exactEquivalenceMonoidal E.functor
  letI := mE
  obtain ⟨mU⟩ := evaluationNative J O U S T β H d
  letI := mU
  exact ⟨Functor.Monoidal.transport
    (Functor.mapDerivedCategoryCompIso E.functor
      (contractibleModuleEvaluation.{u + 1, u, 0} J (ringSheaf J O) (op U))).symm⟩

end AlgebraicGeometry.ProEtale.CondensedRing.Evaluation
