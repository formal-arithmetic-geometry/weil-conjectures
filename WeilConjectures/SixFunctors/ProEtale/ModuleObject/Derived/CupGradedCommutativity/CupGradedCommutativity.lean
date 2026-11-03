/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.ExactSectionsDerivedCup
public import WeilConjectures.CategoryTheory.RingedSignedTensor.RingedTensorSignedCancellation
public import WeilConjectures.CategoryTheory.Site.SitePerfectScalarHomComparison
public import WeilConjectures.Algebra.Homology.ModuleHomComplex
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
public import WeilConjectures.Algebra.Homology.SixFunctors.OrdinaryDerivedChangeOfRings
public import WeilConjectures.Algebra.Homology.ProjectiveHomEvaluationModel
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategorySymmetric
public import Mathlib.CategoryTheory.Triangulated.Generators
public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.LinearAlgebra.Contraction
public import WeilConjectures.Algebra.Homology.BoundedFlatKFlat
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import WeilConjectures.Mathlib.CategoryTheory.Triangulated.Generators
public import Mathlib.CategoryTheory.Limits.FunctorCategory.BinaryBiproducts
public import Mathlib.CategoryTheory.Preadditive.FunctorCategory
public import Mathlib.Algebra.DualNumber
public import Mathlib.Data.ZMod.Basic
public import WeilConjectures.CategoryTheory.DerivedCategory.Perfect.PerfectRingClassicalGenerator
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.Algebra.Homology.DerivedCategory.KProjective
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.Ideal.Span
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import WeilConjectures.CategoryTheory.Ringed.RingedDerivedClosedSymmetricMonoidal
public import Mathlib.CategoryTheory.Adjunction.Basic
public import WeilConjectures.CategoryTheory.SmoothPurity.CanonicalRightDerivedAdjunctionShift
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.RingTheory.Flat.Basic
public import WeilConjectures.Algebra.Homology.RingedTensorCorner.ProjectionMateExact
public import WeilConjectures.Algebra.Homology.Ringed.RingedTopoiDerivedPullbackIndependentSupplement
public import WeilConjectures.CategoryTheory.DerivedCategory.ZetaWeil.RingDerivedDualizablePerfect
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ModuleObjectProjectionMap
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ExchangeProjection
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedFiniteTorConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.TraceCupPoint.CondensedPointTensor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedProperExchangeComparison
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProperCompactificationCoincidence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.AdmissibleCondensedCoefficientFamily
public import WeilConjectures.CategoryTheory.DerivedCategory.AdjunctionIdIso
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.BraidingShift
public import WeilConjectures.Mathlib.CategoryTheory.Shift.Basic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.MonoidalBraided

/-!
# The native scalar cup product

Source: current `sk-cor-trace.proof.md`, Complement (iii), ordinary cup and removal
of the degree-zero Tate line (blueprint: lem-pd-cup-graded-commutativity).

All maps below are built from the recorded ordinary module adjunction, its K-flat
tensorator, terminal sections, and the compactification projection. No new tensor,
sections functor, constructibility predicate, or proper comparison is chosen.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory CategoryTheory.MonObj
open AlgebraicGeometry
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing.CupGradedCommutativity

open CompactificationReindexing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- Use the published small derived category for scalar modules.
Source: ordinary scalar module derived category in Complement (iii)
(blueprint: lem-pd-cup-graded-commutativity). -/
local instance scalarHasDerivedCategory :
    HasDerivedCategory.{u + 1} (ModuleCat.{u + 1} (Γ Λ)) :=
  HasDerivedCategory.ofIsGrothendieckAbelian _

private theorem q_braiding (K L : CochainComplex B ℤ) :
    Functor.LaxMonoidal.μ DerivedCategory.Q K L ≫ DerivedCategory.Q.map (β_ K L).hom =
      (β_ (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj L)).hom ≫
        Functor.LaxMonoidal.μ DerivedCategory.Q L K := by
  have h := DerivedMonoidal.braiding_hom_μ DerivedCategory.Qh
    (HomotopyCategory.quasiIso B (.up ℤ))
    ((HomotopyCategory.quotient B (.up ℤ)).obj K)
    ((HomotopyCategory.quotient B (.up ℤ)).obj L)
  change (β_ (DerivedCategory.Qh.obj ((HomotopyCategory.quotient B (.up ℤ)).obj K))
      (DerivedCategory.Qh.obj ((HomotopyCategory.quotient B (.up ℤ)).obj L))).hom ≫
        Functor.LaxMonoidal.μ DerivedCategory.Qh ((HomotopyCategory.quotient B (.up ℤ)).obj L)
          ((HomotopyCategory.quotient B (.up ℤ)).obj K) =
      Functor.LaxMonoidal.μ DerivedCategory.Qh ((HomotopyCategory.quotient B (.up ℤ)).obj K)
        ((HomotopyCategory.quotient B (.up ℤ)).obj L) ≫
          DerivedCategory.Qh.map
            (β_ ((HomotopyCategory.quotient B (.up ℤ)).obj K)
              ((HomotopyCategory.quotient B (.up ℤ)).obj L)).hom at h
  have hq : Functor.LaxMonoidal.μ (HomotopyCategory.quotient B (.up ℤ)) K L ≫
        (HomotopyCategory.quotient B (.up ℤ)).map (β_ K L).hom =
      (β_ ((HomotopyCategory.quotient B (.up ℤ)).obj K)
        ((HomotopyCategory.quotient B (.up ℤ)).obj L)).hom ≫
          Functor.LaxMonoidal.μ (HomotopyCategory.quotient B (.up ℤ)) L K := by
    change (𝟙 _) ≫ _ = _ ≫ (𝟙 _)
    simp only [Category.id_comp, Category.comp_id]
    rfl
  change ((_ ⊗ₘ _) ≫
    (Functor.LaxMonoidal.μ DerivedCategory.Qh _ _ ≫ DerivedCategory.Qh.map _) ≫ _) ≫ _ =
    _ ≫ ((_ ⊗ₘ _) ≫ (Functor.LaxMonoidal.μ DerivedCategory.Qh _ _ ≫ DerivedCategory.Qh.map _) ≫ _)
  simp only [Category.assoc, ← NatTrans.naturality]
  simp only [Functor.comp_map]
  rw [← DerivedCategory.Qh.map_comp_assoc, hq, DerivedCategory.Qh.map_comp_assoc]
  rw [← reassoc_of% h]
  rw [BraidedCategory.braiding_naturality_assoc]

private theorem chain_braiding (d : ExactSectionsDerivedCup G)
    (h : ∀ M N, d.ordinary.μ M N ≫ G.map (β_ M N).hom =
      (β_ (G.obj M) (G.obj N)).hom ≫ d.ordinary.μ N M)
    (K L : CochainComplex B ℤ) :
    d.chain K L ≫ (G.mapHomologicalComplex (.up ℤ)).map (β_ K L).hom =
      (β_ ((G.mapHomologicalComplex (.up ℤ)).obj K)
        ((G.mapHomologicalComplex (.up ℤ)).obj L)).hom ≫ d.chain L K := by
  apply HomologicalComplex.hom_ext
  intro n
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q hpq
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f]
  rw [← Category.assoc, d.chain_summand]
  change _ = HomologicalComplex.ιTensorObj _ _ p q n hpq ≫ _
  rw [Category.assoc, ← G.map_comp]
  change _ ≫ G.map (_ ≫ (CochainComplex.Monoidal.braiding K L).hom.f n) = _
  rw [CochainComplex.Monoidal.ι_braiding_hom,
    G.map_zsmul, G.map_comp, Preadditive.comp_zsmul]
  erw [CochainComplex.Monoidal.ι_braiding_hom_assoc]
  rw [Preadditive.zsmul_comp, Category.assoc, d.chain_summand]
  rw [← Category.assoc, h]
  simp only [Category.assoc]
  rfl

private theorem derived_braiding_Q (d : ExactSectionsDerivedCup G)
    (h : ∀ M N, d.ordinary.μ M N ≫ G.map (β_ M N).hom =
      (β_ (G.obj M) (G.obj N)).hom ≫ d.ordinary.μ N M)
    (K L : CochainComplex B ℤ)
    [IsIso (Functor.LaxMonoidal.μ DerivedCategory.Q L K)] :
    d.derived.μ (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj L) ≫
        G.mapDerivedCategory.map (β_ (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj L)).hom =
      (β_ (G.mapDerivedCategory.obj (DerivedCategory.Q.obj K))
        (G.mapDerivedCategory.obj (DerivedCategory.Q.obj L))).hom ≫
          d.derived.μ (DerivedCategory.Q.obj L) (DerivedCategory.Q.obj K) := by
  apply (cancel_mono (G.mapDerivedCategory.map (Functor.LaxMonoidal.μ DerivedCategory.Q L K) ≫
    G.mapDerivedCategoryFactors.hom.app (L ⊗ K))).mp
  simp only [Category.assoc]
  rw [← G.mapDerivedCategory.map_comp_assoc, ← q_braiding,
    G.mapDerivedCategory.map_comp_assoc]
  erw [G.mapDerivedCategoryFactors.hom.naturality]
  rw [reassoc_of% d.tensor_normalization]
  simp only [Functor.comp_map]
  rw [← DerivedCategory.Q.map_comp, chain_braiding G d h,
    DerivedCategory.Q.map_comp]
  rw [reassoc_of% q_braiding]
  rw [BraidedCategory.braiding_naturality_assoc,
    ← d.tensor_normalization]

private theorem derived_braiding (d : ExactSectionsDerivedCup G)
    (h : ∀ M N, d.ordinary.μ M N ≫ G.map (β_ M N).hom =
      (β_ (G.obj M) (G.obj N)).hom ≫ d.ordinary.μ N M)
    (M N : DerivedCategory B) :
    d.derived.μ M N ≫ G.mapDerivedCategory.map (β_ M N).hom =
      (β_ (G.mapDerivedCategory.obj M) (G.mapDerivedCategory.obj N)).hom ≫
        d.derived.μ N M := by
  obtain ⟨P, hP, ⟨eP⟩⟩ := DerivedCategory.exists_kFlat_iso M
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective P
  let eK : DerivedCategory.Q.obj K ≅ M :=
    ((DerivedCategory.quotientCompQhIso B).app K).symm ≪≫ eP
  let L := DerivedCategory.Q.objPreimage N
  let eL := DerivedCategory.Q.objObjPreimageIso N
  have hμ : IsIso (Functor.LaxMonoidal.μ DerivedCategory.Q L K) := by
    have : IsIso (Functor.LaxMonoidal.μ DerivedCategory.Qh
        ((HomotopyCategory.quotient B (.up ℤ)).obj L)
        ((HomotopyCategory.quotient B (.up ℤ)).obj K)) :=
      DerivedMonoidal.isIso_counit_app_app_of_kFlat_right DerivedCategory.Qh
        (HomotopyCategory.quasiIso B (.up ℤ)) _ _ hP
    change IsIso ((_ ⊗ₘ _) ≫
      (Functor.LaxMonoidal.μ DerivedCategory.Qh _ _ ≫ DerivedCategory.Qh.map _) ≫ _)
    infer_instance
  let := d.derived
  apply (cancel_epi
    (G.mapDerivedCategory.map eK.hom ⊗ₘ G.mapDerivedCategory.map eL.hom)).mp
  rw [Functor.LaxMonoidal.μ_natural_assoc, ← G.mapDerivedCategory.map_comp,
    BraidedCategory.braiding_naturality, G.mapDerivedCategory.map_comp,
    reassoc_of% derived_braiding_Q G d h,
    ← Functor.LaxMonoidal.μ_natural,
    BraidedCategory.braiding_naturality_assoc]

private theorem identity_projection {C : Type*} [Category C] [MonoidalCategory C]
    {J P : C ⥤ C} [P.Monoidal] (a : J ⊣ P) (e : J ≅ 𝟭 C) (t : P ≅ 𝟭 C)
    (hu : ∀ K, a.unit.app K ≫ t.hom.app (J.obj K) = e.inv.app K)
    (ht : ∀ K N, Functor.LaxMonoidal.μ P K N ≫ t.hom.app (K ⊗ N) = t.hom.app K ⊗ₘ t.hom.app N)
    (K N : C) :
    a.projectionComparison K N ≫ (e.hom.app K ▷ N) =
      J.map (K ◁ t.hom.app N) ≫ e.hom.app (K ⊗ N) := by
  apply (a.homEquiv _ _).injective
  apply (cancel_mono (t.hom.app (K ⊗ N))).mp
  rw [a.homEquiv_naturality_right, a.homEquiv_naturality_left]
  rw [Adjunction.projectionComparison, Equiv.apply_symm_apply, a.homEquiv_unit]
  simp only [Category.assoc]
  erw [t.hom.naturality, t.hom.naturality]
  dsimp only [Functor.id_map, Functor.id_obj]
  rw [reassoc_of% ht, ← Category.assoc]
  have hten : a.unit.app K ▷ P.obj N ≫
      (t.hom.app (J.obj K) ⊗ₘ t.hom.app N) ≫ (e.hom.app K ▷ N) =
      K ◁ t.hom.app N := by
    simp only [← tensorHom_id, ← id_tensorHom]
    rw [← Category.assoc, tensorHom_comp_tensorHom,
      tensorHom_comp_tensorHom]
    simp only [hu, Category.id_comp, Iso.inv_hom_id_app]
    dsimp only [Functor.id_obj]
    simp only [Category.comp_id]
  rw [Category.assoc, hten]
  rw [← Category.assoc (a.unit.app (K ⊗ N)), hu]
  simp only [Iso.inv_hom_id_app]
  dsimp only [Functor.id_obj]
  simp only [Category.comp_id]

private theorem left_shift_braiding (X Y : DerivedCategory C) (i : ℤ) :
    (β_ (X⟦i⟧) Y).hom ≫
        (((curriedTensor (DerivedCategory C)).obj Y).commShiftIso i).hom.app X =
      (((curriedTensor (DerivedCategory C)).flip.obj Y).commShiftIso i).hom.app X ≫
        (β_ X Y).hom⟦i⟧' := by
  apply (cancel_epi (β_ Y (X⟦i⟧)).hom).mp
  simp only [← assoc, SymmetricCategory.symmetry, id_comp]
  rw [DerivedCategory.braiding_hom_commShiftIso_hom_app]
  rw [assoc, ← CategoryTheory.Functor.map_comp, SymmetricCategory.symmetry]
  rw [(shiftFunctor (DerivedCategory C) i).map_id (Y ⊗ X)]
  exact (Category.comp_id _).symm

private theorem tensor_shifts_flip (X Y : DerivedCategory C) (i j : ℤ) :
    (DerivedCategory.shiftTensorShiftIso C X Y i j).hom ≫ (β_ X Y).hom⟦i + j⟧' =
      (i * j).negOnePow • ((β_ (X⟦i⟧) (Y⟦j⟧)).hom ≫
        (DerivedCategory.shiftTensorShiftIso C Y X j i).hom ≫ eqToHom (by rw [add_comm])) := by
  have hc := (curriedTensor (DerivedCategory C)).commShift₂_comm .int X Y i j
  have hc' :
      (((curriedTensor (DerivedCategory C)).flip.obj (Y⟦j⟧)).commShiftIso i).hom.app X ≫
        ((((curriedTensor (DerivedCategory C)).obj X).commShiftIso j).hom.app Y)⟦i⟧' =
      (i * j).negOnePow •
        ((((curriedTensor (DerivedCategory C)).obj (X⟦i⟧)).commShiftIso j).hom.app Y ≫
          ((((curriedTensor (DerivedCategory C)).flip.obj Y).commShiftIso i).hom.app X)⟦j⟧' ≫
            (shiftComm (X ⊗ Y) i j).hom) := by
    rw [reassoc_of% hc]
    simp only [CommShift₂Setup.int_ε, CatCenter.app_neg_one_zpow, Preadditive.comp_zsmul,
      Preadditive.zsmul_comp, Units.smul_def, id_comp, smul_smul, ← Units.val_mul,
      ← Int.negOnePow_add, ← two_mul, Int.negOnePow_two_mul, Units.val_one, one_smul]
    simp only [curriedTensor_obj_obj, Iso.inv_hom_id, comp_id]
  simp only [DerivedCategory.shiftTensorShiftIso, Iso.trans_hom, Functor.mapIso_hom,
    Iso.app_hom, Iso.symm_hom, assoc]
  rw [reassoc_of% hc']
  simp only [Preadditive.zsmul_comp, Units.smul_def]
  congr 1
  rw [reassoc_of% DerivedCategory.braiding_hom_commShiftIso_hom_app]
  rw [← Functor.map_comp_assoc, left_shift_braiding, Functor.map_comp_assoc]
  simp only [assoc]
  rw [shiftComm]
  simp only [shiftFunctorComm, Iso.trans_hom, Iso.symm_hom, Iso.app_hom,
    NatTrans.comp_app, assoc]
  simp only [curriedTensor_obj_obj, Iso.hom_inv_id_app_assoc]
  rw [← CategoryTheory.Functor.comp_map,
    shiftFunctorAdd'_inv_app_comp_eqToHom i j (j + i) (i + j) (add_comm i j) rfl (Y ⊗ X)]
  rw [(shiftFunctorAdd' (DerivedCategory C) i j (i + j) rfl).inv.naturality]
  simp only [shiftFunctorAdd'_eq_shiftFunctorAdd]
  rfl

private theorem class_product_comm (M : DerivedCategory C) (m : M ⊗ M ⟶ M)
    (hm : (β_ M M).hom ≫ m = m) (i j : ℤ)
    (x : (𝟙_ _) ⟶ M⟦i⟧) (y : (𝟙_ _) ⟶ M⟦j⟧) :
    (λ_ _).inv ≫ (x ⊗ₘ y) ≫
        (DerivedCategory.shiftTensorShiftIso C M M i j).hom ≫ m⟦i + j⟧' =
      (i * j).negOnePow •
        ((λ_ _).inv ≫ (y ⊗ₘ x) ≫
          (DerivedCategory.shiftTensorShiftIso C M M j i).hom ≫ m⟦j + i⟧' ≫
            eqToHom (by rw [add_comm])) := by
  conv_lhs => rw [← hm]
  rw [Functor.map_comp]
  try simp only [assoc]
  rw [reassoc_of% tensor_shifts_flip]
  try simp only [Units.smul_def, Preadditive.comp_zsmul, Preadditive.zsmul_comp, assoc]
  congr 1
  rw [BraidedCategory.braiding_naturality_assoc]
  simp only [braiding_tensorUnit_left,
    Iso.inv_hom_id_assoc, ← unitors_inv_equal, assoc]
  rw [← eqToHom_naturality (fun n ↦ m⟦n⟧') (add_comm j i)]

private def pointScalarHasDerivedCategory
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] :
    HasDerivedCategory.{u + 1} (ModuleCat.{u + 1} (Γ Λ)) :=
  HasDerivedCategory.ofIsGrothendieckAbelian _

private theorem ordinary_braiding
    (M N : Mod (Sheaf (ProEt.topology (Spec (.of k))) Ab.{u + 1})
      (condensedRingObj Λ (Spec (.of k)))) :
    (tensorData Λ k).ordinary.μ M N ≫
        (condensedRingCoefficientSections Λ (Spec (.of k))).map (β_ M N).hom =
      (β_ ((condensedRingCoefficientSections Λ (Spec (.of k))).obj M)
        ((condensedRingCoefficientSections Λ (Spec (.of k))).obj N)).hom ≫
          (tensorData Λ k).ordinary.μ N M := by
  have hn (P Q : Mod (Sheaf (ProEt.topology (Spec (.of k))) Ab.{u + 1})
      (condensedRingObj Λ (Spec (.of k))))
      (x : (condensedRingCoefficientSections Λ (Spec (.of k))).obj P)
      (y : (condensedRingCoefficientSections Λ (Spec (.of k))).obj Q) :
      ((tensorData Λ k).ordinary.μ P Q).hom (x ⊗ₜ[Γ Λ] y) =
        (λ_ _).inv ≫ (x ⊗ₘ y) := by
    unfold tensorData
    exact (tensorData_existsUnique Λ k).choose_spec.1 P Q x y
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro x y
  change (((tensorData Λ k).ordinary.μ M N).hom (x ⊗ₜ[Γ Λ] y)) ≫
      (β_ M N).hom =
    ((tensorData Λ k).ordinary.μ N M).hom (y ⊗ₜ[Γ Λ] x)
  rw [hn, hn, Category.assoc, BraidedCategory.braiding_naturality]
  rw [← Category.assoc]
  congr 1
  simp only [braiding_tensorUnit_left, Iso.inv_hom_id_assoc]
  exact unitors_inv_equal.symm

private theorem identity_mu (X : Scheme.{u}) (K N : D Λ X) :
    Functor.LaxMonoidal.μ (P Λ (𝟙 X)) K N ≫ (leftDerivedUpperStarId Λ X).hom.app (K ⊗ N) =
      (leftDerivedUpperStarId Λ X).hom.app K ⊗ₘ
        (leftDerivedUpperStarId Λ X).hom.app N := by
  apply (cancel_epi (((leftDerivedUpperStarTensor Λ (𝟙 X)).app K).app N)).mp
  change Functor.OplaxMonoidal.δ (P Λ (𝟙 X)) K N ≫
      Functor.LaxMonoidal.μ (P Λ (𝟙 X)) K N ≫ _ = _
  rw [Functor.Monoidal.δ_μ_assoc]
  exact (leftDerivedUpperStarTensor_id Λ X K N).symm

private theorem identity_open_projection (X : Scheme.{u}) (K N : D Λ X) :
    inv (openImmersionProjectionComparison Λ (𝟙 X) K N) ≫
        (J Λ (𝟙 X)).map (K ◁ (leftDerivedUpperStarId Λ X).hom.app N) ≫
        (derivedOpenImmersionLowerShriekId Λ X).hom.app (K ⊗ N) =
      (derivedOpenImmersionLowerShriekId Λ X).hom.app K ▷ N := by
  apply (cancel_epi (openImmersionProjectionComparison Λ (𝟙 X) K N)).mp
  simp only [← Category.assoc, IsIso.hom_inv_id, Category.id_comp]
  exact (identity_projection (oa Λ (𝟙 X)) (derivedOpenImmersionLowerShriekId Λ X)
    (leftDerivedUpperStarId Λ X)
    (identity_unit_of_counit _ _ _ (identity_derived_counit Λ X))
    (identity_mu Λ X) K N).symm

private theorem identity_compactification_pullback {X Y : Scheme.{u}} (a : X ⟶ Y)
    [IsProper a] (N : D Λ Y) :
    (leftDerivedUpperStarCompactificationIso Λ (Compactification.ofIsProper a)).inv.app N =
      (leftDerivedUpperStarId Λ X).hom.app ((P Λ a).obj N) := by
  apply (cancel_epi
    ((leftDerivedUpperStarCompactificationIso Λ (Compactification.ofIsProper a)).hom.app N)).mp
  rw [Iso.hom_inv_id_app]
  unfold leftDerivedUpperStarCompactificationIso
  dsimp only [Compactification.ofIsProper]
  simp only [Iso.trans_hom, NatTrans.comp_app, eqToIso.hom, Category.assoc]
  erw [leftDerivedUpperStarComp_id_left_app Λ a N]
  dsimp only [Functor.id_obj]
  erw [eqToHom_app]
  rw [eqToHom_trans]
  exact (eqToHom_refl _ _).symm

private theorem identity_compactification_projection {X Y : Scheme.{u}} (a : X ⟶ Y)
    [IsProper a] (K : D Λ X) (N : D Λ Y) :
    pf Λ (Compactification.ofIsProper a) K N ≫
        (properIdentityComparison Λ a).hom.app (K ⊗ (P Λ a).obj N) =
      ((properIdentityComparison Λ a).hom.app K ▷ N) ≫ moduleObjectProjectionMap Λ a K N := by
  rw [pf_factorization]
  simp only [properIdentityComparison, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, Functor.leftUnitor_hom_app]
  change (moduleObjectProjectionMap Λ a ((J Λ (𝟙 X)).obj K) N ≫
      (R Λ a).map (inv (openImmersionProjectionComparison Λ (𝟙 X) K ((P Λ a).obj N)) ≫
        (J Λ (𝟙 X)).map (𝟙 K ⊗ₘ
          (leftDerivedUpperStarCompactificationIso Λ (Compactification.ofIsProper a)).inv.app N))) ≫
          (R Λ a).map ((derivedOpenImmersionLowerShriekId Λ X).hom.app _) ≫ 𝟙 _ =
      ((R Λ a).map ((derivedOpenImmersionLowerShriekId Λ X).hom.app K) ≫ 𝟙 _) ▷ N ≫ _
  simp only [Category.comp_id]
  unfold moduleObjectProjectionMap moduleObjectProjectionData
  simp only [Category.assoc]
  rw [← (R Λ a).map_comp, identity_compactification_pullback,
    id_tensorHom,
    Category.assoc, identity_open_projection]
  exact (derivedUpperStarLowerStarAdjunction Λ a).rightAdjointProjectionMap_naturality_left
    (leftDerivedUpperStarTensor Λ a) ((derivedOpenImmersionLowerShriekId Λ X).hom.app K) N |>.symm

private theorem proper_projection {X Y : Scheme.{u}} (a : X ⟶ Y)
    [IsProper a] (c : Compactification a) (K : D Λ X) (N : D Λ Y) :
    pf Λ c K N ≫
        (refinement Λ (properIdentityRefinement c) ≫
          (properIdentityComparison Λ a).hom).app (K ⊗ (P Λ a).obj N) =
      ((refinement Λ (properIdentityRefinement c) ≫
          (properIdentityComparison Λ a).hom).app K ▷ N) ≫
        moduleObjectProjectionMap Λ a K N := by
  simp only [NatTrans.comp_app, ← Category.assoc]
  rw [refinement_projection]
  rw [Category.assoc, identity_compactification_projection]
  unfold moduleObjectProjectionMap moduleObjectProjectionData
  simp only [MonoidalCategory.comp_whiskerRight, Category.assoc, tensorHom_id]

/-- The native ordinary cup is the adjunct of the K-flat pullback tensorator followed
by the tensor of the two specified counits.
Source: current sk-cor-trace Complement (iii), ordinary cup construction
(blueprint: lem-pd-cup-graded-commutativity). -/
def siteCup {X Y : Scheme.{u}} (a : X ⟶ Y) (K L : D Λ X) :
    (R Λ a).obj K ⊗ (R Λ a).obj L ⟶ (R Λ a).obj (K ⊗ L) :=
  (derivedUpperStarLowerStarAdjunction Λ a).homEquiv _ _
    (((leftDerivedUpperStarTensor Λ a).app ((R Λ a).obj K)).app ((R Λ a).obj L) ≫
      ((derivedUpperStarLowerStarAdjunction Λ a).counit.app K ⊗ₘ
        (derivedUpperStarLowerStarAdjunction Λ a).counit.app L))

private theorem siteCup_projection {X Y : Scheme.{u}} (a : X ⟶ Y) (K L : D Λ X) :
    siteCup Λ a K L =
      (moduleObjectProjectionMap Λ a K ((R Λ a).obj L) :
        (R Λ a).obj K ⊗ (R Λ a).obj L ⟶
          (R Λ a).obj (K ⊗ (P Λ a).obj ((R Λ a).obj L))) ≫
        (R Λ a).map (K ◁ (derivedUpperStarLowerStarAdjunction Λ a).counit.app L) := by
  change _ = (((derivedUpperStarLowerStarAdjunction Λ a).rightAdjointProjectionMap
    (leftDerivedUpperStarTensor Λ a)).app K).app ((R Λ a).obj L) ≫ _
  unfold siteCup
  rw [Adjunction.rightAdjointProjectionMap_app_app]
  erw [← Adjunction.homEquiv_naturality_right]
  congr 1
  simp only [curriedTensor_map_app, MonoidalCategory.tensorHom_def, Category.assoc]

private theorem siteCup_symmetry {X Y : Scheme.{u}} (a : X ⟶ Y) (K L : D Λ X) :
    siteCup Λ a K L ≫ (R Λ a).map
        ((TraceCupPoint.siteBraiding Λ X).braiding K L).hom =
      ((TraceCupPoint.siteBraiding Λ Y).braiding
        ((R Λ a).obj K) ((R Λ a).obj L)).hom ≫ siteCup Λ a L K := by
  letI := DerivedCategory.braidedCategory'
    (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
  letI := DerivedCategory.braidedCategory'
    (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))
  unfold TraceCupPoint.siteBraiding
  change siteCup Λ a K L ≫ (R Λ a).map (β_ K L).hom =
    (β_ ((R Λ a).obj K) ((R Λ a).obj L)).hom ≫ siteCup Λ a L K
  unfold siteCup
  erw [← Adjunction.homEquiv_naturality_right, ← Adjunction.homEquiv_naturality_left]
  congr 1
  rw [Category.assoc, BraidedCategory.braiding_naturality,
    ← reassoc_of% leftDerivedUpperStarTensor_braiding Λ a ((R Λ a).obj K) ((R Λ a).obj L)]

private theorem siteCup_natural_left {X Y : Scheme.{u}} (a : X ⟶ Y)
    {K K' : D Λ X} (f : K ⟶ K') (L : D Λ X) :
    (R Λ a).map f ▷ (R Λ a).obj L ≫ siteCup Λ a K' L =
      siteCup Λ a K L ≫ (R Λ a).map (f ▷ L) := by
  simp only [siteCup_projection]
  exact (derivedUpperStarLowerStarAdjunction Λ a).cupProductOfProjection_naturality_left
    (P := R Λ a)
    (pm := fun K N ↦ ((
      (derivedUpperStarLowerStarAdjunction Λ a).rightAdjointProjectionMap
        (leftDerivedUpperStarTensor Λ a)).app K).app N)
    (fun x N ↦ (derivedUpperStarLowerStarAdjunction Λ a).rightAdjointProjectionMap_naturality_left
      (leftDerivedUpperStarTensor Λ a) x N) f L

private theorem siteCup_natural_right {X Y : Scheme.{u}} (a : X ⟶ Y)
    (K : D Λ X) {L L' : D Λ X} (g : L ⟶ L') :
    (R Λ a).obj K ◁ (R Λ a).map g ≫ siteCup Λ a K L' =
      siteCup Λ a K L ≫ (R Λ a).map (K ◁ g) := by
  simp only [siteCup_projection]
  exact (derivedUpperStarLowerStarAdjunction Λ a).cupProductOfProjection_naturality_right
    (P := R Λ a)
    (pm := fun K N ↦ ((
      (derivedUpperStarLowerStarAdjunction Λ a).rightAdjointProjectionMap
        (leftDerivedUpperStarTensor Λ a)).app K).app N)
    (fun M _ _ y ↦
      (derivedUpperStarLowerStarAdjunction Λ a).rightAdjointProjectionMap_naturality_right
        (leftDerivedUpperStarTensor Λ a) M y) K g

private theorem transported_tensor_natural
    {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D]
    (F G : C ⥤ D) [F.LaxMonoidal] (e : F ≅ G)
    {X X' Y Y' : C} (f : X ⟶ X') (g : Y ⟶ Y') :
    (G.map f ⊗ₘ G.map g) ≫
        (e.inv.app X' ⊗ₘ e.inv.app Y') ≫ Functor.LaxMonoidal.μ F X' Y' ≫
          e.hom.app (X' ⊗ Y') =
      ((e.inv.app X ⊗ₘ e.inv.app Y) ≫ Functor.LaxMonoidal.μ F X Y ≫
        e.hom.app (X ⊗ Y)) ≫ G.map (f ⊗ₘ g) := by
  let := Functor.LaxMonoidal.ofIso e
  exact Functor.LaxMonoidal.μ_natural G f g

private theorem fiber_tensor_natural (k : Type u) [Field k] [IsAlgClosed k]
    {M M' N N' : D Λ (Spec (.of k))} (f : M ⟶ M') (g : N ⟶ N') :
    ((TraceCupPoint.fiber Λ k).map f ⊗ₘ (TraceCupPoint.fiber Λ k).map g) ≫
        TraceCupPoint.tensor Λ k M' N' =
      TraceCupPoint.tensor Λ k M N ≫ (TraceCupPoint.fiber Λ k).map (f ⊗ₘ g) := by
  let := (TraceCupPoint.tensorData Λ k).derived
  unfold TraceCupPoint.tensor TraceCupPoint.exactTensor
  exact transported_tensor_natural _ _ (TraceCupPoint.exactComparison Λ k).symm f g

/-- Terminal sections of the tensor-of-counits cup, preceded by the normalized point
section tensor comparison. Only the comparison map is used, not an ambient equivalence.
Source: current sk-cor-trace Complement (iii), scalar realization
(blueprint: lem-pd-cup-graded-commutativity). -/
def scalarCup (k : Type u) [Field k] [IsAlgClosed k] {X : Scheme.{u}}
    (a : X ⟶ Spec (.of k)) (K L : D Λ X) :
    (condensedRingOrdinaryCoefficientComplex Λ a).obj K ⊗
        (condensedRingOrdinaryCoefficientComplex Λ a).obj L ⟶
      (condensedRingOrdinaryCoefficientComplex Λ a).obj (K ⊗ L) :=
  TraceCupPoint.tensor Λ k ((R Λ a).obj K) ((R Λ a).obj L) ≫
    (TraceCupPoint.fiber Λ k).map (siteCup Λ a K L)

private theorem scalarCup_natural_left (k : Type u) [Field k] [IsAlgClosed k]
    {X : Scheme.{u}} (a : X ⟶ Spec (.of k)) {K K' : D Λ X}
    (f : K ⟶ K') (L : D Λ X) :
    (condensedRingOrdinaryCoefficientComplex Λ a).map f ▷
        (condensedRingOrdinaryCoefficientComplex Λ a).obj L ≫ scalarCup Λ k a K' L =
      scalarCup Λ k a K L ≫
        (condensedRingOrdinaryCoefficientComplex Λ a).map (f ▷ L) := by
  unfold scalarCup condensedRingOrdinaryCoefficientComplex
  dsimp only [Functor.comp_map, Functor.comp_obj]
  have hn := fiber_tensor_natural Λ k ((R Λ a).map f) (𝟙 ((R Λ a).obj L))
  erw [(TraceCupPoint.fiber Λ k).map_id] at hn
  simp only [tensorHom_id] at hn
  rw [reassoc_of% hn]
  rw [← Functor.map_comp, siteCup_natural_left, Functor.map_comp, Category.assoc]

private theorem scalarCup_natural_right (k : Type u) [Field k] [IsAlgClosed k]
    {X : Scheme.{u}} (a : X ⟶ Spec (.of k)) (K : D Λ X)
    {L L' : D Λ X} (g : L ⟶ L') :
    (condensedRingOrdinaryCoefficientComplex Λ a).obj K ◁
        (condensedRingOrdinaryCoefficientComplex Λ a).map g ≫ scalarCup Λ k a K L' =
      scalarCup Λ k a K L ≫
        (condensedRingOrdinaryCoefficientComplex Λ a).map (K ◁ g) := by
  unfold scalarCup condensedRingOrdinaryCoefficientComplex
  dsimp only [Functor.comp_map, Functor.comp_obj]
  have hn := fiber_tensor_natural Λ k (𝟙 ((R Λ a).obj K)) ((R Λ a).map g)
  erw [(TraceCupPoint.fiber Λ k).map_id] at hn
  simp only [id_tensorHom] at hn
  rw [reassoc_of% hn]
  rw [← Functor.map_comp, siteCup_natural_right, Functor.map_comp, Category.assoc]

/-- The site cup is the module projection/counit product, and both the site and scalar
equations express agreement with the compact projection/counit product. The module
projection is the recorded `moduleObjectProjectionMap`; the scalar equation uses exactly
the same point tensor.
Source: current sk-cor-trace Complement (iii), mixed-support product
(blueprint: lem-pd-cup-graded-commutativity). -/
def ProperProductComparison (k : Type u) [Field k] [IsAlgClosed k] {X : Scheme.{u}}
    (a : X ⟶ Spec (.of k)) [IsProper a] (K L : D Λ X) : Prop :=
  siteCup Λ a K L =
      (moduleObjectProjectionMap Λ a K ((R Λ a).obj L) :
        (R Λ a).obj K ⊗ (R Λ a).obj L ⟶ (R Λ a).obj (K ⊗ (P Λ a).obj ((R Λ a).obj L))) ≫
        (R Λ a).map (K ◁ (derivedUpperStarLowerStarAdjunction Λ a).counit.app L) ∧
  ∀ c : Compactification a,
    let κ := properComparison Λ c
    let mixed := (derivedUpperStarLowerStarAdjunction Λ a).cupProductOfProjection
      (F Λ c) (exceptionalProjectionMorphismOfCompactification Λ c) K L
    (κ.app K ▷ (R Λ a).obj L ≫ siteCup Λ a K L = mixed ≫ κ.app (K ⊗ L)) ∧
    (TraceCupPoint.tensor Λ k ((F Λ c).obj K) ((R Λ a).obj L) ≫
        (TraceCupPoint.fiber Λ k).map mixed ≫
        (TraceCupPoint.fiber Λ k).map (κ.app (K ⊗ L)) =
      ((TraceCupPoint.fiber Λ k).map (κ.app K) ⊗ₘ 𝟙 _) ≫ scalarCup Λ k a K L)

/-- Multiplication of the coefficient unit after the ordinary scalar lax tensor map.
Source: current sk-cor-trace Complement (iii), ordinary cup on B_X
(blueprint: lem-pd-cup-graded-commutativity). -/
def multiplication (k : Type u) [Field k] [IsAlgClosed k] {X : Scheme.{u}}
    (a : X ⟶ Spec (.of k)) :
    (condensedRingOrdinaryCoefficientComplex Λ a).obj (𝟙_ (D Λ X)) ⊗
        (condensedRingOrdinaryCoefficientComplex Λ a).obj (𝟙_ (D Λ X)) ⟶
      (condensedRingOrdinaryCoefficientComplex Λ a).obj (𝟙_ (D Λ X)) :=
  scalarCup Λ k a (𝟙_ _) (𝟙_ _) ≫
    (condensedRingOrdinaryCoefficientComplex Λ a).map (λ_ (𝟙_ (D Λ X))).hom

set_option maxHeartbeats 1600000 in
-- The projective scalar-unit comparison elaborates large derived-category instances.
/-- The standard projective-unit representative identification, evaluated at one.
This is the generic module-derived comparison, independent of coefficient models.
Source: current sk-cor-trace Complement (iii), scalar cohomology representatives
(blueprint: lem-pd-cup-graded-commutativity). -/
def cohomologyClassEquiv (M : DerivedCategory (ModuleCat.{u + 1} (Γ Λ))) (i : ℤ) :
    ((𝟙_ (DerivedCategory (ModuleCat.{u + 1} (Γ Λ)))) ⟶ M⟦i⟧) ≃
      ↥((DerivedCategory.homologyFunctor (ModuleCat.{u + 1} (Γ Λ)) i).obj M) :=
  ((DerivedCategory.singleFunctorObjUnitIso _).symm.homCongr (Iso.refl _)).trans
    (((DerivedCategory.shiftFunctorCompPreadditiveCoyonedaObjSingleFunctorZeroIso
      (ModuleCat.of.{u + 1} (Γ Λ) (Γ Λ)) i).app M).addCommGroupIsoToAddEquiv.toEquiv.trans
        ((ModuleCat.homLinearEquiv (R := Γ Λ) (S := ℤ)
          (M := ModuleCat.of.{u + 1} (Γ Λ) (Γ Λ))
          (N := (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} (Γ Λ)) i).obj M)).toEquiv.trans
          (LinearMap.ringLmapEquivSelf (Γ Λ) ℤ
            ↥((DerivedCategory.homologyFunctor (ModuleCat.{u + 1} (Γ Λ)) i).obj M)).toEquiv))

set_option maxHeartbeats 1600000 in
-- Give the scalar complex explicitly to avoid metavariable-driven instance search.
/-- Ordinary cup on the actual scalar cohomology modules, formed by tensoring unit-map
representatives, extracting their shifts, and applying coefficient multiplication.
Source: current sk-cor-trace Complement (iii), homogeneous classes
(blueprint: lem-pd-cup-graded-commutativity). -/
def cup (k : Type u) [Field k] [IsAlgClosed k] {X : Scheme.{u}}
    (a : X ⟶ Spec (.of k)) (i j : ℤ)
    (x : (condensedRingOrdinaryCohomology Λ a i).obj (𝟙_ (D Λ X)))
    (y : (condensedRingOrdinaryCohomology Λ a j).obj (𝟙_ (D Λ X))) :
    (condensedRingOrdinaryCohomology Λ a (i + j)).obj (𝟙_ (D Λ X)) :=
  let M := (condensedRingOrdinaryCoefficientComplex Λ a).obj (𝟙_ (D Λ X))
  let x' := (cohomologyClassEquiv Λ M i).symm x
  let y' := (cohomologyClassEquiv Λ M j).symm y
  let mulMap := multiplication Λ k a
  cohomologyClassEquiv Λ M (i + j)
    ((λ_ _).inv ≫ (x' ⊗ₘ y') ≫
      (DerivedCategory.shiftTensorShiftIso _ M M i j).hom ≫
        mulMap⟦i + j⟧')

/-- Untwisting a pulled-back degree-zero line using any of its bases. A line is
represented invariantly by a point complex isomorphic to the coefficient unit.
Source: current sk-cor-trace Complement (iii), free rank-one degree-zero line
(blueprint: lem-pd-cup-graded-commutativity). -/
def untwist {X Y : Scheme.{u}} (a : X ⟶ Y) (V : D Λ Y)
    (basis : V ≅ 𝟙_ (D Λ Y)) (K : D Λ X) : K ⊗ (P Λ a).obj V ⟶ K :=
  K ◁ ((P Λ a).map basis.hom ≫ (leftDerivedUpperStarUnitIso Λ a).hom) ≫ (ρ_ K).hom

/-- Both product comparisons for a pulled-back free line, and the naturality squares
which remove its basis in either factor. The assertion quantifies over every basis.
Source: current sk-cor-trace Complement (iii), tensoring and untwisting
(blueprint: lem-pd-cup-graded-commutativity). -/
def LineCompatibility (k : Type u) [Field k] [IsAlgClosed k] {X : Scheme.{u}}
    (a : X ⟶ Spec (.of k)) [IsProper a] (K L : D Λ X) : Prop :=
  ∀ (V : D Λ (Spec (.of k))) (basis : V ≅ 𝟙_ (D Λ (Spec (.of k)))),
    ProperProductComparison Λ k a (K ⊗ (P Λ a).obj V) L ∧
    ProperProductComparison Λ k a K (L ⊗ (P Λ a).obj V) ∧
    (((condensedRingOrdinaryCoefficientComplex Λ a).map (untwist Λ a V basis K) ⊗ₘ
        𝟙 _) ≫ scalarCup Λ k a K L =
      scalarCup Λ k a (K ⊗ (P Λ a).obj V) L ≫
        (condensedRingOrdinaryCoefficientComplex Λ a).map
          (untwist Λ a V basis K ⊗ₘ 𝟙 L)) ∧
    ((𝟙 _ ⊗ₘ (condensedRingOrdinaryCoefficientComplex Λ a).map
        (untwist Λ a V basis L)) ≫ scalarCup Λ k a K L =
      scalarCup Λ k a K (L ⊗ (P Λ a).obj V) ≫
        (condensedRingOrdinaryCoefficientComplex Λ a).map
          (𝟙 K ⊗ₘ untwist Λ a V basis L))

private theorem classEquiv_neg (M : DerivedCategory (ModuleCat.{u + 1} (Γ Λ)))
    (i : ℤ) (f : (𝟙_ _) ⟶ M⟦i⟧) :
    cohomologyClassEquiv Λ M i (-f) = -cohomologyClassEquiv Λ M i f := by
  simp [cohomologyClassEquiv, Iso.homCongr]

private theorem classEquiv_smul (M : DerivedCategory (ModuleCat.{u + 1} (Γ Λ)))
    (i : ℤ) (t : ℤˣ) (f : (𝟙_ _) ⟶ M⟦i⟧) :
    cohomologyClassEquiv Λ M i (t • f) = t • cohomologyClassEquiv Λ M i f := by
  rcases Int.units_eq_one_or t with h | h
  · simp [h]
  · simpa [h] using classEquiv_neg Λ M i f

private theorem classEquiv_transport (M : DerivedCategory (ModuleCat.{u + 1} (Γ Λ)))
    (i j : ℤ) (h : i = j) (f : (𝟙_ _) ⟶ M⟦i⟧) :
    cohomologyClassEquiv Λ M j (f ≫ eqToHom (congrArg (fun n ↦ M⟦n⟧) h)) =
      (eqToHom (congrArg (fun n ↦
        (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} (Γ Λ)) n).obj M) h))
          (cohomologyClassEquiv Λ M i f) := by
  subst j
  simp

private theorem scalar_tensor_comparison (k : Type u) [Field k] [IsAlgClosed k]
    {X : Scheme.{u}} (a : X ⟶ Spec (.of k)) (K L : D Λ X)
    {M : D Λ (Spec (.of k))} (f : M ⟶ (R Λ a).obj K) :
    ((TraceCupPoint.fiber Λ k).map f ⊗ₘ
        𝟙 ((condensedRingOrdinaryCoefficientComplex Λ a).obj L)) ≫
      TraceCupPoint.tensor Λ k ((R Λ a).obj K) ((R Λ a).obj L) =
    TraceCupPoint.tensor Λ k M ((R Λ a).obj L) ≫
      (TraceCupPoint.fiber Λ k).map (f ▷ (R Λ a).obj L) := by
  unfold condensedRingOrdinaryCoefficientComplex
  dsimp only [Functor.comp_obj]
  have hn := fiber_tensor_natural Λ k f (𝟙 ((R Λ a).obj L))
  erw [(TraceCupPoint.fiber Λ k).map_id] at hn
  simpa only [tensorHom_id] using hn

private theorem scalar_product_comparison (k : Type u) [Field k] [IsAlgClosed k]
    {X : Scheme.{u}} (a : X ⟶ Spec (.of k)) (K L : D Λ X)
    {M Q : D Λ (Spec (.of k))} (f : M ⟶ (R Λ a).obj K)
    (m : (R Λ a).obj K ⊗ (R Λ a).obj L ⟶ (R Λ a).obj (K ⊗ L))
    (n : M ⊗ (R Λ a).obj L ⟶ Q) (v : Q ⟶ (R Λ a).obj (K ⊗ L))
    (h : f ▷ (R Λ a).obj L ≫ m = n ≫ v) :
    TraceCupPoint.tensor Λ k M ((R Λ a).obj L) ≫
        (TraceCupPoint.fiber Λ k).map n ≫ (TraceCupPoint.fiber Λ k).map v =
      ((TraceCupPoint.fiber Λ k).map f ⊗ₘ
        𝟙 ((condensedRingOrdinaryCoefficientComplex Λ a).obj L)) ≫
        (TraceCupPoint.tensor Λ k ((R Λ a).obj K) ((R Λ a).obj L) ≫
          (TraceCupPoint.fiber Λ k).map m) := by
  rw [← Functor.map_comp, ← h, Functor.map_comp]
  rw [← reassoc_of% scalar_tensor_comparison Λ k a K L f]

private theorem proper_site_comparison (k : Type u) [Field k] [IsAlgClosed k]
    {X : Scheme.{u}} (a : X ⟶ Spec (.of k)) [IsProper a]
    (c : Compactification a) (κ : F Λ c ⟶ R Λ a) (K L : D Λ X)
    (hp : pf Λ c K ((R Λ a).obj L) ≫
        κ.app (K ⊗ (P Λ a).obj ((R Λ a).obj L)) =
      (κ.app K ▷ (R Λ a).obj L) ≫ moduleObjectProjectionMap Λ a K ((R Λ a).obj L)) :
    κ.app K ▷ (R Λ a).obj L ≫ siteCup Λ a K L =
      (derivedUpperStarLowerStarAdjunction Λ a).cupProductOfProjection
        (F Λ c) (exceptionalProjectionMorphismOfCompactification Λ c) K L ≫
          κ.app (K ⊗ L) := by
  dsimp only [Adjunction.cupProductOfProjection]
  rw [Category.assoc, κ.naturality, ← Category.assoc]
  unfold pf at hp
  rw [hp, Category.assoc, ← siteCup_projection]

private theorem proper_product (k : Type u) [Field k] [IsAlgClosed k]
    {X : Scheme.{u}} (a : X ⟶ Spec (.of k)) [IsProper a] (K L : D Λ X)
    (hp : ∀ c : Compactification a,
      pf Λ c K ((R Λ a).obj L) ≫
          (properComparison Λ c).app (K ⊗ (P Λ a).obj ((R Λ a).obj L)) =
        ((properComparison Λ c).app K ▷ (R Λ a).obj L) ≫
          moduleObjectProjectionMap Λ a K ((R Λ a).obj L)) :
    ProperProductComparison Λ k a K L := by
  refine ⟨siteCup_projection Λ a K L, ?_⟩
  intro c
  have hs := proper_site_comparison Λ k a c (properComparison Λ c) K L (hp c)
  refine ⟨hs, ?_⟩
  unfold scalarCup
  exact scalar_product_comparison Λ k a K L ((properComparison Λ c).app K)
    (siteCup Λ a K L)
    ((derivedUpperStarLowerStarAdjunction Λ a).cupProductOfProjection
      (F Λ c) (exceptionalProjectionMorphismOfCompactification Λ c) K L)
    ((properComparison Λ c).app (K ⊗ L)) hs

private theorem scalar_symmetry (k : Type u) [Field k] [IsAlgClosed k]
    {X : Scheme.{u}} (a : X ⟶ Spec (.of k)) (K L : D Λ X)
    (hf : ∀ M N : D Λ (Spec (.of k)),
      TraceCupPoint.tensor Λ k M N ≫ (TraceCupPoint.fiber Λ k).map
          ((TraceCupPoint.siteBraiding Λ (Spec (.of k))).braiding M N).hom =
        ((TraceCupPoint.scalarBraiding Λ).braiding
          ((TraceCupPoint.fiber Λ k).obj M) ((TraceCupPoint.fiber Λ k).obj N)).hom ≫
            TraceCupPoint.tensor Λ k N M) :
    scalarCup Λ k a K L ≫ (condensedRingOrdinaryCoefficientComplex Λ a).map
        ((TraceCupPoint.siteBraiding Λ X).braiding K L).hom =
      ((TraceCupPoint.scalarBraiding Λ).braiding
        ((condensedRingOrdinaryCoefficientComplex Λ a).obj K)
        ((condensedRingOrdinaryCoefficientComplex Λ a).obj L)).hom ≫
          scalarCup Λ k a L K := by
  unfold scalarCup condensedRingOrdinaryCoefficientComplex
  dsimp only [Functor.comp_map, Functor.comp_obj]
  rw [Category.assoc, ← Functor.map_comp, siteCup_symmetry,
    Functor.map_comp, ← Category.assoc, hf, Category.assoc]

private theorem lines (k : Type u) [Field k] [IsAlgClosed k]
    {X : Scheme.{u}} (a : X ⟶ Spec (.of k)) [IsProper a] (K L : D Λ X)
    (hp : ∀ K L : D Λ X, ProperProductComparison Λ k a K L) :
    LineCompatibility Λ k a K L := by
  intro V basis
  refine ⟨hp _ _, hp _ _, ?_, ?_⟩
  · simpa only [tensorHom_id] using
      scalarCup_natural_left Λ k a (untwist Λ a V basis K) L
  · simpa only [id_tensorHom] using
      scalarCup_natural_right Λ k a K (untwist Λ a V basis L)

private theorem multiplication_comm (k : Type u) [Field k] [IsAlgClosed k]
    {X : Scheme.{u}} (a : X ⟶ Spec (.of k))
    (hs : scalarCup Λ k a (𝟙_ _) (𝟙_ _) ≫
        (condensedRingOrdinaryCoefficientComplex Λ a).map
          ((TraceCupPoint.siteBraiding Λ X).braiding (𝟙_ _) (𝟙_ _)).hom =
      ((TraceCupPoint.scalarBraiding Λ).braiding
        ((condensedRingOrdinaryCoefficientComplex Λ a).obj (𝟙_ _))
        ((condensedRingOrdinaryCoefficientComplex Λ a).obj (𝟙_ _))).hom ≫
          scalarCup Λ k a (𝟙_ _) (𝟙_ _)) :
    ((TraceCupPoint.scalarBraiding Λ).braiding
        ((condensedRingOrdinaryCoefficientComplex Λ a).obj (𝟙_ _))
        ((condensedRingOrdinaryCoefficientComplex Λ a).obj (𝟙_ _))).hom ≫
      multiplication Λ k a = multiplication Λ k a := by
  let := TraceCupPoint.siteBraiding Λ X
  unfold multiplication
  rw [← Category.assoc, ← hs, Category.assoc, ← Functor.map_comp]
  rw [braiding_leftUnitor, ← unitors_equal]

private theorem cup_comm_from_representatives (k : Type u) [Field k] [IsAlgClosed k]
    {X : Scheme.{u}} (a : X ⟶ Spec (.of k))
    (hc : ∀ (i j : ℤ)
      (x : (𝟙_ _) ⟶ ((condensedRingOrdinaryCoefficientComplex Λ a).obj (𝟙_ _)) ⟦i⟧)
      (y : (𝟙_ _) ⟶ ((condensedRingOrdinaryCoefficientComplex Λ a).obj (𝟙_ _)) ⟦j⟧),
      (λ_ _).inv ≫ (x ⊗ₘ y) ≫
          (DerivedCategory.shiftTensorShiftIso _ _ _ i j).hom ≫
            (multiplication Λ k a) ⟦i + j⟧' =
        (i * j).negOnePow • ((λ_ _).inv ≫ (y ⊗ₘ x) ≫
          (DerivedCategory.shiftTensorShiftIso _ _ _ j i).hom ≫
            (multiplication Λ k a) ⟦j + i⟧' ≫ eqToHom (by rw [add_comm])))
    (i j : ℤ)
    (x : (condensedRingOrdinaryCohomology Λ a i).obj (𝟙_ (D Λ X)))
    (y : (condensedRingOrdinaryCohomology Λ a j).obj (𝟙_ (D Λ X))) :
    cup Λ k a i j x y = (i * j).negOnePow •
      (eqToHom (by rw [add_comm]) :
        (condensedRingOrdinaryCohomology Λ a (j + i)).obj (𝟙_ (D Λ X)) ⟶
          (condensedRingOrdinaryCohomology Λ a (i + j)).obj (𝟙_ (D Λ X)))
            (cup Λ k a j i y x) := by
  unfold condensedRingOrdinaryCohomology at x y ⊢
  dsimp only [Functor.comp_obj] at x y ⊢
  unfold cup
  dsimp only
  rw [hc, classEquiv_smul]
  simp only [← Category.assoc]
  rw [classEquiv_transport Λ _ _ _ (add_comm j i)]

set_option maxHeartbeats 1600000 in
-- The statement compares several fully specified derived functor composites.
/-- The canonical scalar lax cup for smooth proper X over Fbar_q is Koszul symmetric,
equals the proper mixed-support projection/counit cup, is graded commutative on all
integer scalar cohomology groups, and is unchanged by a degree-zero scalar line.

The coefficient hypothesis is precisely the continuous E or finite-subextension-valued
Qbar_l case of def-pur-admissible-condensed-ring. No model over the finite field or
pure-dimension assumption is supplied.

Source: current sk-cor-trace.proof.md, Complement (iii)
(blueprint: lem-pd-cup-graded-commutativity).

Proof in words: compute the pullback tensorator on balanced K-flat generators. The
Koszul swap gives the same signed generator on both paths. Transpose under the native
adjunction: the two symmetry composites have identical tensors of counits, so are equal.
The proper identity-open compactification reduces its projection to the module
projection; the canonical refinement transports this equality to any compactification.
Projection followed by the second counit has the same transpose as siteCup. Apply exact
point sections and their normalized tensor comparison. Multiplication of the coefficient
unit is commutative; signed shift-tensor representatives give (-1)^(ij), hence the same
formula on actual cohomology through classEquiv. For any degree-zero line, choose a
basis, use tensor and counit naturality, and cancel it. A change of basis multiplies both
paths by the same unit, so the two untwisting squares are independent of that choice. -/
theorem native_cup_graded_commutativity
    (d : WeilConjectures.FiniteFieldDatum.{u}) (c : d.CoefficientDatum)
    (E : PadicAlgCl.FiniteIntermediateField c.l)
    (_hΛ : Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj.{u} E)) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicAlgClRingObj.{u} c.l)))
    {X : Scheme.{u}} (a : X ⟶ Spec (.of d.k)) [Smooth a] [IsProper a] :
    (∀ K L : CondensedConstructibleFiniteTor Λ X,
      (siteCup Λ a K.obj L.obj ≫ (R Λ a).map
          ((TraceCupPoint.siteBraiding Λ X).braiding K.obj L.obj).hom =
        ((TraceCupPoint.siteBraiding Λ (Spec (.of d.k))).braiding
          ((R Λ a).obj K.obj) ((R Λ a).obj L.obj)).hom ≫ siteCup Λ a L.obj K.obj) ∧
      (scalarCup Λ d.k a K.obj L.obj ≫ (condensedRingOrdinaryCoefficientComplex Λ a).map
          ((TraceCupPoint.siteBraiding Λ X).braiding K.obj L.obj).hom =
        ((TraceCupPoint.scalarBraiding Λ).braiding
          ((condensedRingOrdinaryCoefficientComplex Λ a).obj K.obj)
          ((condensedRingOrdinaryCoefficientComplex Λ a).obj L.obj)).hom ≫
            scalarCup Λ d.k a L.obj K.obj) ∧
      ProperProductComparison Λ d.k a K.obj L.obj ∧
      LineCompatibility Λ d.k a K.obj L.obj) ∧
    (∀ (i j : ℤ)
      (x : (condensedRingOrdinaryCohomology Λ a i).obj (𝟙_ (D Λ X)))
      (y : (condensedRingOrdinaryCohomology Λ a j).obj (𝟙_ (D Λ X))),
      cup Λ d.k a i j x y = (i * j).negOnePow •
        (eqToHom (by rw [add_comm]) :
          (condensedRingOrdinaryCohomology Λ a (j + i)).obj (𝟙_ (D Λ X)) ⟶
            (condensedRingOrdinaryCohomology Λ a (i + j)).obj (𝟙_ (D Λ X)))
              (cup Λ d.k a j i y x)) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing.CupGradedCommutativity
