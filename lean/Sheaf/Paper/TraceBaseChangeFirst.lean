/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q16
-/
module

public import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Monoidal
public import Sheaf.Paper.CondensedModuleDerivedPushpull
public import Sheaf.Paper.CartesianCoefficients
public import Sheaf.Paper.ProEtaleTateTwistsOfUniverses
public import Sheaf.Paper.LocalizingAdmissibleCoefficients
public import Sheaf.Paper.CondensedConstantConstructibility
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import Sheaf.AlgebraicGeometry.ChosenCartesianSquare
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategoryBraided
import Sheaf.Paper.IntegralResidueDerivedMonoidal
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.UnitCoherence
import Sheaf.Paper.InverseImageModuleFlat
import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapMonoidal
import Sheaf.CategoryTheory.Adjunction.LeftCoefficientProjectionAction
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Braided
import Sheaf.UpstreamExtra.WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Counit
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Braided


/-!
# Trace and base-change rearrangement before the first triangle

Source: blueprint main-20261015, sec-six-functors-basics/sk-thm-int-restriction,
`sk-thm-int-restriction-line.proof.md`, (1), first triangle
(blueprint: lem-sfb-trace-base-change-first).

All operations below are on the ordinary unbounded derived categories of internal
modules over the pulled-back condensed coefficient ring. The square and tensor
comparisons, projection maps and source identification are specified constructions.
The internal-module tensor helpers are owned by this item; the general ringed-topos
tensor-pullback interface remains publicly imported with its recorded declaration.
-/

@[expose] public noncomputable section

set_option autoImplicit false
attribute [local instance 20000]
  DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory
attribute [local irreducible] CategoryTheory.Functor.leftDerivedFunctor
  CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.leftDerivedTensorComparison CategoryTheory.Functor.leftDerivedFunctorCounit

set_option synthInstance.maxSize 2048

universe u u₁ u₂ u₃ v₁ v₂ v₃

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj

section NamedSheafSymmetry
attribute [local instance] Sheaf.monoidalCategory
namespace CategoryTheory
/-- The canonical sheaf symmetry with its canonical braiding named explicitly.
The record update is definitionally equal to the existing symmetric structure;
it prevents comparison of two separately generated braiding structures downstream.
Source: the symmetric monoidal sheafification construction in Mathlib
(blueprint: lem-sfb-trace-base-change-first). -/
@[instance_reducible]
def traceSheafSymmetric
    {C : Type u₁} [Category.{v₁} C] (J : GrothendieckTopology C)
    (A : Type u₂) [Category.{v₂} A] [MonoidalCategory A] [SymmetricCategory A]
    [(J.W (A := A)).IsMonoidal] [HasWeakSheafify J A] :
    SymmetricCategory (Sheaf J A) :=
  { Sheaf.symmetricCategory J A with
    toBraidedCategory := Sheaf.braidedCategory J A }
private theorem traceSheafSymmetric_eq
    {C : Type u₁} [Category.{v₁} C] (J : GrothendieckTopology C)
    (A : Type u₂) [Category.{v₂} A] [MonoidalCategory A] [SymmetricCategory A]
    [(J.W (A := A)).IsMonoidal] [HasWeakSheafify J A] :
    traceSheafSymmetric J A = Sheaf.symmetricCategory J A := rfl
end CategoryTheory
end NamedSheafSymmetry
attribute [local instance 20000] CategoryTheory.traceSheafSymmetric

namespace CategoryTheory
/-- The canonical derived Koszul braiding, assembled while the base category is abstract.
Source: Stacks 07A4 (blueprint: lem-sfb-trace-base-change-first). -/
def traceCanonicalDerivedBraiding
    {A : Type u₁} [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [HasDerivedCategory.{u + 1} A]
    [MonoidalCategory A] [MonoidalClosed A] [MonoidalPreadditive A] [BraidedCategory A]
    [Abelian.HasFunctorialFlatResolution A]
    (K L : DerivedCategory A) : K ⊗ L ≅ L ⊗ K :=
  (DerivedCategory.braidedCategory' A).braiding K L
end CategoryTheory



section MapTensorHelper

variable {C D : Type*} [Category C] [Category D]
  [MonoidalCategory C] [BraidedCategory C] [HasCoequalizers C]
  [∀ A : C, PreservesColimitsOfSize.{0, 0} (tensorLeft A)]
  [∀ A : C, PreservesColimitsOfSize.{0, 0} (tensorRight A)]
  [MonoidalCategory D] [BraidedCategory D] [HasCoequalizers D]
  [∀ A : D, PreservesColimitsOfSize.{0, 0} (tensorLeft A)]
  [∀ A : D, PreservesColimitsOfSize.{0, 0} (tensorRight A)]
  (F : C ⥤ D) [F.Braided] [PreservesColimitsOfShape WalkingParallelPair F]
  {R : C} [MonObj R] [IsCommMonObj R]

private theorem map_tensor_inverse (M N : Mod C R) :
    F.map (Mod.tensorObjπ M N) ≫ (Functor.OplaxMonoidal.δ (F.mapMod R) M N).hom =
      Functor.OplaxMonoidal.δ F M.X N.X ≫
        Mod.tensorObjπ ((F.mapMod R).obj M) ((F.mapMod R).obj N) := by
  apply (cancel_mono (F.mapModTensorIso M N).hom.hom).1
  change (F.map (Mod.tensorObjπ M N) ≫ (F.mapModTensorIso M N).inv.hom) ≫ _ = _
  have hi := congrArg Mod.Hom.hom (F.mapModTensorIso M N).inv_hom_id
  simp only [Mod.comp_hom', Mod.id_hom'] at hi
  rw [Category.assoc, hi]
  erw [Category.comp_id]
  erw [Category.assoc, Functor.tensorπ_mapModTensorIso_hom_hom,
    Functor.Monoidal.δ_μ_assoc]

end MapTensorHelper

section ExtensionTensorHelper

variable {C : Type*} [Category C] [MonoidalCategory C] [BraidedCategory C]
  [HasCoequalizers C] [HasEqualizers C] [MonoidalClosed C]
  [∀ A : C, PreservesColimitsOfSize.{0, 0} (tensorLeft A)]
  [∀ A : C, PreservesColimitsOfSize.{0, 0} (tensorRight A)]
  {R S : C} [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S]
  (α : R ⟶ S) [IsMonHom α] [IsIso α]

omit [HasEqualizers C] [MonoidalClosed C] in
private theorem extension_tensor_inverse
    (hunit : ∀ A : Mod C R, Mod.extendUnitHom α A ≫
      ((Mod.extendScalarsIsoComapInv α).hom.app A).hom = 𝟙 _) (M N : Mod C R) :
    Mod.tensorObjπ M N ≫ Mod.extendUnitHom α (M ⊗ N) ≫
        (Functor.OplaxMonoidal.δ (Mod.extendScalars α) M N).hom =
      (Mod.extendUnitHom α M ⊗ₘ Mod.extendUnitHom α N) ≫
        Mod.tensorObjπ ((Mod.extendScalars α).obj M) ((Mod.extendScalars α).obj N) := by
  rw [Functor.Monoidal.transport_δ]
  simp only [Iso.symm_inv, Iso.symm_hom, Mod.comp_hom']
  rw [reassoc_of% (hunit (M ⊗ N))]
  change Mod.tensorObjπ M N ≫ (Mod.comapTensorIso (asIso α).inv M N).inv.hom ≫ _ = _
  have hπ : Mod.tensorObjπ M N ≫ (Mod.comapTensorIso (asIso α).inv M N).inv.hom =
      Mod.tensorObjπ ((Mod.comap (asIso α).inv).obj M)
        ((Mod.comap (asIso α).inv).obj N) := by
    apply (cancel_mono (Mod.comapTensorIso (asIso α).inv M N).hom.hom).1
    have hi := congrArg Mod.Hom.hom (Mod.comapTensorIso (asIso α).inv M N).inv_hom_id
    simp only [Mod.comp_hom', Mod.id_hom'] at hi
    rw [Category.assoc, hi]
    erw [Category.comp_id]
    exact (Mod.tensorπ_comapTensorIso_hom_hom (asIso α).inv M N).symm
  erw [reassoc_of% hπ]
  have h (A : Mod C R) : ((Mod.extendScalarsIsoComapInv α).inv.app A).hom =
      Mod.extendUnitHom α A := by
    apply (cancel_mono ((Mod.extendScalarsIsoComapInv α).hom.app A).hom).1
    have hi := congrArg Mod.Hom.hom ((Mod.extendScalarsIsoComapInv α).inv_hom_id_app A)
    simp only [Mod.comp_hom', Mod.id_hom'] at hi
    exact hi.trans (hunit A).symm
  rw [MonoidalCategory.tensorHom_def]
  simp only [Mod.comp_hom']
  erw [Mod.tensorObjπ_whiskerRight_assoc, Mod.tensorObjπ_whiskerLeft]
  rw [h, h]
  erw [← tensorHom_def_assoc]

end ExtensionTensorHelper

section OrdinaryBraidingHelpers
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe v u' v'
section
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
  [HasCoequalizers C]
  [∀ A : C, PreservesColimitsOfSize.{0, 0} (tensorLeft A)]
  [∀ A : C, PreservesColimitsOfSize.{0, 0} (tensorRight A)]
  {D : Type u'} [Category.{v'} D] [MonoidalCategory D] [SymmetricCategory D]
  [HasCoequalizers D]
  [∀ A : D, PreservesColimitsOfSize.{0, 0} (tensorLeft A)]
  [∀ A : D, PreservesColimitsOfSize.{0, 0} (tensorRight A)]
  (F : C ⥤ D) [F.Braided] [PreservesColimitsOfShape WalkingParallelPair F]
  {R : C} [MonObj R] [IsCommMonObj R]
private theorem mapMod_braided (M N : Mod C R) :
    Functor.LaxMonoidal.μ (F.mapMod R) M N ≫ (F.mapMod R).map (β_ M N).hom =
      (β_ ((F.mapMod R).obj M) ((F.mapMod R).obj N)).hom ≫
        Functor.LaxMonoidal.μ (F.mapMod R) N M := by
  apply Mod.hom_ext
  rw [← cancel_epi (Mod.tensorObjπ ((F.mapMod R).obj M) ((F.mapMod R).obj N))]
  change Mod.tensorObjπ _ _ ≫ (F.mapModTensorIso M N).hom.hom ≫
      F.map (β_ M N).hom.hom =
    Mod.tensorObjπ _ _ ≫ (β_ ((F.mapMod R).obj M) ((F.mapMod R).obj N)).hom.hom ≫
      (F.mapModTensorIso N M).hom.hom
  erw [reassoc_of% Functor.tensorπ_mapModTensorIso_hom_hom, ← F.map_comp]
  erw [Mod.braiding_hom_hom, Mod.tensorObjπ_braidingHomX, F.map_comp]
  rw [Functor.LaxBraided.braided_assoc]
  erw [Mod.braiding_hom_hom, Mod.tensorObjπ_braidingHomX_assoc,
    Functor.tensorπ_mapModTensorIso_hom_hom]
  rfl
end
section
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
  [HasCoequalizers C]
  [∀ A : C, PreservesColimitsOfSize.{0, 0} (tensorLeft A)]
  [∀ A : C, PreservesColimitsOfSize.{0, 0} (tensorRight A)]
  {R S : C} [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
  (ψ : S ⟶ R) [IsMonHom ψ] [IsIso ψ]
private theorem comap_braided (M N : Mod C R) :
    Functor.LaxMonoidal.μ (Mod.comap ψ) M N ≫ (Mod.comap ψ).map (β_ M N).hom =
      (β_ ((Mod.comap ψ).obj M) ((Mod.comap ψ).obj N)).hom ≫
        Functor.LaxMonoidal.μ (Mod.comap ψ) N M := by
  apply Mod.hom_ext
  rw [← cancel_epi (Mod.tensorObjπ ((Mod.comap ψ).obj M) ((Mod.comap ψ).obj N))]
  change Mod.tensorObjπ _ _ ≫ (Mod.comapTensorIso ψ M N).hom.hom ≫
      (β_ M N).hom.hom =
    Mod.tensorObjπ _ _ ≫ (β_ ((Mod.comap ψ).obj M) ((Mod.comap ψ).obj N)).hom.hom ≫
      (Mod.comapTensorIso ψ N M).hom.hom
  have ht := Mod.tensorπ_comapTensorIso_hom_hom ψ M N
  rw [← Category.assoc, ht]
  erw [Mod.braiding_hom_hom, Mod.tensorObjπ_braidingHomX]
  erw [Mod.braiding_hom_hom, Mod.tensorObjπ_braidingHomX_assoc,
    Mod.tensorπ_comapTensorIso_hom_hom]
  rfl
end
section Extend
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
  [HasCoequalizers C] [HasEqualizers C] [MonoidalClosed C]
  [∀ A : C, PreservesColimitsOfSize.{0, 0} (tensorLeft A)]
  [∀ A : C, PreservesColimitsOfSize.{0, 0} (tensorRight A)]
  {R S : C} [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
  (φ : R ⟶ S) [IsMonHom φ] [IsIso φ]
@[instance_reducible]
private noncomputable def extend_braided : (Mod.extendScalars φ).LaxBraided := by
  let ψ := (asIso φ).inv
  let : (Mod.comap ψ : Mod C R ⥤ Mod C S).LaxBraided :=
    { braided := comap_braided ψ }
  let i := Mod.extendScalarsIsoComapInv φ
  let : NatTrans.IsMonoidal i.symm.hom := {
    unit := by simp [i, Functor.Monoidal.transport_ε]
    tensor M N := by simp [i, Functor.Monoidal.transport_μ] }
  exact Functor.LaxBraided.ofNatIso i.symm
end Extend

end OrdinaryBraidingHelpers

namespace CategoryTheory.Functor
open Functor.LaxMonoidal Functor.OplaxMonoidal _root_.DerivedCategory
variable {C : Type u₁} [Category.{u + 1} C] [Abelian C] [IsGrothendieckAbelian.{u + 1} C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
  [Abelian.HasFunctorialFlatResolution C]
  {D : Type u₂} [Category.{u + 1} D] [Abelian D] [IsGrothendieckAbelian.{u + 1} D]
  [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalClosed D] [BraidedCategory D]
  [Abelian.HasFunctorialFlatResolution D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [F.PreservesFlat] [F.IsLeftAdjoint] [F.Monoidal]
  (hG : ∀ X Y : C, F.map (β_ X Y).hom ≫ δ F Y X =
    δ F X Y ≫ (β_ (F.obj X) (F.obj Y)).hom)
private local instance : BraidedCategory (DerivedCategory C) := DerivedCategory.braidedCategory' C
private local instance : BraidedCategory (DerivedCategory D) := DerivedCategory.braidedCategory' D
private theorem generic_derived_delta (K M : DerivedCategory C) :
    letI := F.residueDerivedMonoidal
    δ F.leftDerivedFunctor K M = ((F.leftDerivedTensorComparison).app K).app M := rfl
include hG
private theorem generic_derived_braid_Qh
    (P Q : HomotopyCategory C (.up ℤ))
    (hP : F.kFlatMap P) :
    letI := F.residueDerivedMonoidal
    F.leftDerivedFunctor.map (β_ (Qh.obj P) (Qh.obj Q)).hom ≫
        δ F.leftDerivedFunctor (Qh.obj Q) (Qh.obj P) =
      δ F.leftDerivedFunctor (Qh.obj P) (Qh.obj Q) ≫
        (β_ (F.leftDerivedFunctor.obj (Qh.obj P)) (F.leftDerivedFunctor.obj (Qh.obj Q))).hom := by
  let := F.residueDerivedMonoidal
  have : IsIso (μ Qh ((F.mapHomotopyCategory (.up ℤ)).obj Q)
      ((F.mapHomotopyCategory (.up ℤ)).obj P)) :=
    isIso_μNatTrans_Qh_app_app_of_kFlat _ _ hP
  rw [← cancel_mono ((F.leftDerivedFunctorCounit.app Q ⊗ₘ
    F.leftDerivedFunctorCounit.app P) ≫
    μ Qh ((F.mapHomotopyCategory (.up ℤ)).obj Q)
      ((F.mapHomotopyCategory (.up ℤ)).obj P))]
  simp only [generic_derived_delta, Category.assoc]
  rw [F.leftDerivedTensorComparison_app_app_comp_tensorHom,
    ← BraidedCategory.braiding_naturality_assoc]
  have hβ : (β_ ((F.mapHomotopyCategory (.up ℤ) ⋙ Qh).obj P)
      ((F.mapHomotopyCategory (.up ℤ) ⋙ Qh).obj Q)).hom ≫
        μ Qh ((F.mapHomotopyCategory (.up ℤ)).obj Q)
          ((F.mapHomotopyCategory (.up ℤ)).obj P) =
      μ Qh ((F.mapHomotopyCategory (.up ℤ)).obj P)
          ((F.mapHomotopyCategory (.up ℤ)).obj Q) ≫
        Qh.map (β_ ((F.mapHomotopyCategory (.up ℤ)).obj P)
          ((F.mapHomotopyCategory (.up ℤ)).obj Q)).hom :=
    DerivedCategory.braidedCategory_braiding_hom_μ_Qh D _ _
  rw [hβ]
  rw [reassoc_of% (F.leftDerivedTensorComparison_app_app_comp_tensorHom P Q)]
  rw [← Functor.map_comp_assoc]
  rw [DerivedCategory.braidedCategory_braiding_hom_μ_Qh C P Q]
  rw [Functor.map_comp_assoc]
  have hn : F.leftDerivedFunctor.map (Qh.map (β_ P Q).hom) ≫
      F.leftDerivedFunctorCounit.app (Q ⊗ P) =
      F.leftDerivedFunctorCounit.app (P ⊗ Q) ≫
        Qh.map ((F.mapHomotopyCategory (.up ℤ)).map (β_ P Q).hom) :=
    F.leftDerivedFunctorCounit.naturality _
  erw [reassoc_of% hn]
  rw [← Qh.map_comp, ← Qh.map_comp]
  erw [Functor.mapHomotopyCategory_map_braiding_hom_δ _ hG P Q]
  rfl


/-- The comonoidal structure of `Lg^*` is compatible with the derived braidings:
`Lg^* β_{K, M} ≫ δ_{M, K} = δ_{K, M} ≫ β_{Lg^* K, Lg^* M}`. -/
private theorem generic_derived_braid
    (K M : DerivedCategory C) :
    letI := F.residueDerivedMonoidal
    F.leftDerivedFunctor.map (β_ K M).hom ≫ δ F.leftDerivedFunctor M K =
      δ F.leftDerivedFunctor K M ≫
        (β_ (F.leftDerivedFunctor.obj K) (F.leftDerivedFunctor.obj M)).hom := by
  let := F.residueDerivedMonoidal
  obtain ⟨P, hP, ⟨eP⟩⟩ := F.residue_exists_kFlatMap_iso K
  obtain ⟨Q, -, ⟨eQ⟩⟩ := F.residue_exists_kFlatMap_iso M
  exact Functor.OplaxMonoidal.map_braiding_hom_δ_of_iso _ eP eQ
    (generic_derived_braid_Qh F hG P Q hP)

/-- The canonical monoidal structure on the derived functor preserves the
Koszul braiding, by its comparison square on K-flat resolutions. -/
private theorem generic_derived_braid_lax
    (K M : DerivedCategory C) :
    letI := F.residueDerivedMonoidal
    μ F.leftDerivedFunctor K M ≫ F.leftDerivedFunctor.map (β_ K M).hom =
      (β_ (F.leftDerivedFunctor.obj K) (F.leftDerivedFunctor.obj M)).hom ≫
        μ F.leftDerivedFunctor M K := by
  let := F.residueDerivedMonoidal
  exact Functor.Monoidal.μ_map_braiding_hom_of_δ _ K M
    (generic_derived_braid F hG K M)


end CategoryTheory.Functor



namespace CategoryTheory.Functor
variable {C : Type u₁} [Category.{u + 1} C] [Abelian C] [IsGrothendieckAbelian.{u + 1} C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
  [Abelian.HasFunctorialFlatResolution C]
  {D : Type u₂} [Category.{u + 1} D] [Abelian D] [IsGrothendieckAbelian.{u + 1} D]
  [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalClosed D] [BraidedCategory D]
  [Abelian.HasFunctorialFlatResolution D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [F.PreservesFlat] [F.IsLeftAdjoint] [F.Monoidal]
omit [F.PreservesFlat] in
/-- The degree-zero unit comparison, packaged before specialization to sheaf modules.
This is the explicit composite through the exact-functor comparison, the quotient
factorization and the ordinary unit isomorphism; no data is chosen.
Source: Stacks 07A4 (blueprint: lem-sfb-trace-base-change-first). -/
@[irreducible]
def traceDegreeZeroUnitIso : F.leftDerivedFunctor.obj (𝟙_ _) ≅ 𝟙_ _ :=
  F.leftDerivedFunctorIsoMapDerivedCategory.app (𝟙_ _) ≪≫
    F.mapDerivedCategoryFactors.app (𝟙_ _) ≪≫
    DerivedCategory.Q.mapIso
      (((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).app (𝟙_ _)) ≪≫
        (HomologicalComplex.single _ (.up ℤ) 0).mapIso
          (Functor.Monoidal.εIso F).symm)

omit [F.PreservesFlat] in
private theorem derived_unit_explicit :
    F.traceDegreeZeroUnitIso = F.leftDerivedTensorUnitIso := by
  unfold traceDegreeZeroUnitIso
  apply Iso.ext
  unfold Functor.leftDerivedTensorUnitIso
  simp only [Iso.trans_hom, Functor.mapIso_hom, asIso_hom]
  rw [← Functor.leftDerivedFunctorIsoMapDerivedCategory_hom_app_fac]
  erw [Functor.mapDerivedCategoryFactorsh_hom_app F (𝟙_ _)]
  simp only [Functor.map_comp, Category.assoc]
  rw [← DerivedCategory.Qh.map_comp_assoc]
  have hi := Iso.inv_hom_id_app (F.mapHomotopyCategoryFactors (.up ℤ))
    (𝟙_ _)
  erw [hi]
  erw [DerivedCategory.Qh.map_id, Category.id_comp]
  simp only [DerivedCategory.quotientCompQhIso,
    HomologicalComplexUpToQuasiIso.quotientCompQhIso,
    CategoryTheory.Quotient.lift.isLift_hom, Category.id_comp]
  erw [Functor.map_id, Category.id_comp]
  rfl
/-- The explicit unit composite is the inverse unitator of the derived monoidal functor. -/
private theorem derived_unit_monoidal_explicit :
    letI := F.residueDerivedMonoidal
    F.traceDegreeZeroUnitIso =
      (Functor.Monoidal.εIso F.leftDerivedFunctor).symm := by
  let := F.residueDerivedMonoidal
  apply Iso.ext
  change _ = Functor.OplaxMonoidal.η F.leftDerivedFunctor
  rw [residueDerivedOplax_η_eq_tensorUnitIso]
  exact congrArg Iso.hom (derived_unit_explicit F)

variable {E : Type u₃} [Category.{u + 1} E] [Abelian E] [IsGrothendieckAbelian.{u + 1} E]
  [MonoidalCategory E] [MonoidalPreadditive E] [MonoidalClosed E] [BraidedCategory E]
  [Abelian.HasFunctorialFlatResolution E]
  (G : D ⥤ E) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [G.PreservesFlat] [G.IsLeftAdjoint] [G.Monoidal]
  (H : C ⥤ E) [H.Additive] [PreservesFiniteLimits H] [PreservesFiniteColimits H]
  [H.PreservesFlat] [H.IsLeftAdjoint] [H.Monoidal]
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
private theorem derived_comp_explicit (τ : H ≅ F ⋙ G) [NatTrans.IsMonoidal τ.hom]
    (M N : DerivedCategory C) :
    (H.leftDerivedFunctorNatIso τ ≪≫ F.leftDerivedFunctorCompIso G).hom.app (M ⊗ N) ≫
        G.leftDerivedFunctor.map ((F.leftDerivedTensorComparison.app M).app N) ≫
        (G.leftDerivedTensorComparison.app (F.leftDerivedFunctor.obj M)).app
          (F.leftDerivedFunctor.obj N) =
      ((H.leftDerivedTensorComparison.app M).app N) ≫
        ((H.leftDerivedFunctorNatIso τ ≪≫ F.leftDerivedFunctorCompIso G).hom.app M ⊗ₘ
          (H.leftDerivedFunctorNatIso τ ≪≫ F.leftDerivedFunctorCompIso G).hom.app N) := by
  simp only [Iso.trans_hom, NatTrans.comp_app, Category.assoc]
  rw [map_leftDerivedTensorComparison_app_app_comp,
    Iso.hom_inv_id_app_assoc, leftDerivedTensorComparison_naturality_app_assoc]
  simp only [tensorHom_comp_tensorHom]

end CategoryTheory.Functor

private theorem tensor_square_family
    {C V : Type*} [Category C] [Category V] [MonoidalCategory C] [MonoidalCategory V]
    {I : Type*} (L : I → C ⥤ V)
    (dL : ∀ i, ∀ K M : C, (L i).obj (K ⊗ M) ⟶ (L i).obj K ⊗ (L i).obj M)
    {A B : C ⥤ V}
    (dA : ∀ K M, A.obj (K ⊗ M) ⟶ A.obj K ⊗ A.obj M)
    (dB : ∀ K M, B.obj (K ⊗ M) ⟶ B.obj K ⊗ B.obj M)
    {i j : I} (h : i = j) (a : L i ≅ A) (b : L j ≅ B)
    (ha : ∀ K M, a.hom.app (K ⊗ M) ≫ dA K M =
      dL i K M ≫ (a.hom.app K ⊗ₘ a.hom.app M))
    (hb : ∀ K M, b.hom.app (K ⊗ M) ≫ dB K M =
      dL j K M ≫ (b.hom.app K ⊗ₘ b.hom.app M)) (K M : C) :
    (b.symm ≪≫ eqToIso (congrArg L h.symm) ≪≫ a).hom.app (K ⊗ M) ≫ dA K M =
      dB K M ≫ ((b.symm ≪≫ eqToIso (congrArg L h.symm) ≪≫ a).hom.app K ⊗ₘ
        (b.symm ≪≫ eqToIso (congrArg L h.symm) ≪≫ a).hom.app M) := by
  subst j
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, eqToIso_refl,
    Iso.refl_hom, Category.id_comp, Category.assoc]
  rw [ha, ← cancel_epi (b.hom.app (K ⊗ M)), Iso.hom_inv_id_app_assoc,
    ← Category.assoc, hb, Category.assoc, tensorHom_comp_tensorHom]
  simp only [Iso.hom_inv_id_app_assoc]

private theorem unit_of_oplax
    {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D]
    {F G : C ⥤ D} [F.Monoidal] [G.Monoidal] (e : F ⟶ G)
    (he : e.app (𝟙_ C) ≫ Functor.OplaxMonoidal.η G = Functor.OplaxMonoidal.η F) :
    Functor.LaxMonoidal.ε F ≫ e.app (𝟙_ C) = Functor.LaxMonoidal.ε G := by
  rw [← cancel_mono (Functor.OplaxMonoidal.η G), Category.assoc, he,
    Functor.Monoidal.ε_η, Functor.Monoidal.ε_η]

private theorem tensorπ_tensorHom
    {C : Type*} [Category C] [MonoidalCategory C] [BraidedCategory C]
    [HasCoequalizers C]
    [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
    [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)]
    {R : C} [MonObj R] [IsCommMonObj R] {M N M' N' : Mod C R}
    (a : M ⟶ M') (b : N ⟶ N') :
    Mod.tensorObjπ M N ≫ (a ⊗ₘ b).hom =
      (a.hom ⊗ₘ b.hom) ≫ Mod.tensorObjπ M' N' := by
  rw [MonoidalCategory.tensorHom_def, Mod.comp_hom', Mod.tensorObjπ_whiskerRight_assoc,
    Mod.tensorObjπ_whiskerLeft, ← MonoidalCategory.tensorHom_def_assoc]

private theorem conjugate_tensor_only
    {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [MonoidalCategory D]
    {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C}
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂)
    [L₁.OplaxMonoidal] [L₂.OplaxMonoidal] [R₁.LaxMonoidal] [R₂.LaxMonoidal]
    [a₁.IsMonoidal] [a₂.IsMonoidal]
    (e : R₁ ⟶ R₂)
    (he : ∀ X Y, Functor.LaxMonoidal.μ R₁ X Y ≫ e.app (X ⊗ Y) =
      (e.app X ⊗ₘ e.app Y) ≫ Functor.LaxMonoidal.μ R₂ X Y) (X Y : C) :
    ((conjugateEquiv a₁ a₂).symm e).app (X ⊗ Y) ≫
        Functor.OplaxMonoidal.δ L₁ X Y =
      Functor.OplaxMonoidal.δ L₂ X Y ≫
        (((conjugateEquiv a₁ a₂).symm e).app X ⊗ₘ
          ((conjugateEquiv a₁ a₂).symm e).app Y) := by
  apply (a₂.homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit,
    Functor.map_comp, Functor.map_comp, ← Category.assoc,
    ← unit_conjugateEquiv_symm, Category.assoc, ← e.naturality,
    Adjunction.unit_app_tensor_comp_map_δ_assoc, he,
    tensorHom_comp_tensorHom_assoc, unit_conjugateEquiv_symm a₁ a₂ e X,
    unit_conjugateEquiv_symm a₁ a₂ e Y, ← tensorHom_comp_tensorHom_assoc,
    Functor.LaxMonoidal.μ_natural, Adjunction.unit_app_tensor_comp_map_δ_assoc]

private theorem monoidal_core_roundtrip
    {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [MonoidalCategory D] (F : C ⥤ D) [m : F.Monoidal] :
    (Functor.CoreMonoidal.ofOplaxMonoidal F).toMonoidal = m := by
  apply Functor.Monoidal.ext
  · exact Functor.Monoidal.inv_η _
  · funext M N
    exact Functor.Monoidal.inv_δ _ M N
  · rfl
  · rfl

private theorem proof_transport_one {A : Sort*} (P : A → Prop) {a b : A}
    (h : a = b) (hb : P b) : P a := by
  cases h
  exact hb
private theorem proof_transport_three {A B C : Sort*} (P : A → B → C → Prop)
    {a a' : A} {b b' : B} {c c' : C}
    (ha : a = a') (hb : b = b') (hc : c = c') (h : P a' b' c') : P a b c := by
  cases ha
  cases hb
  cases hc
  exact h

namespace AlgebraicGeometry.ProEtale.CondensedRing

section TensorPullbackHelpers

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The ordinary comparison sends the tensor of the two universal pullback sections to
its universal tensor section; on the regular module it is the coefficient map alpha.
These are equalities of sheaf maps, so include all local generators, rather than only
sections over schemes in the image of base change.
Source: Stacks 03EL (blueprint: lem-sfb-trace-base-change-first). -/
def CondensedTensorNormalization (m : (upperStar Λ f).CoreMonoidal) : Prop :=
  (∀ M N : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y),
    (Mod.tensorObjπ M N) ≫ ((upperStarLowerStarAdjunction Λ f).unit.app (M ⊗ N)).hom ≫
        (ProEtale.lowerStar Ab.{u + 1} f).map ((m.μIso M N).inv.hom) =
      (((upperStarLowerStarAdjunction Λ f).unit.app M).hom ⊗ₘ
        ((upperStarLowerStarAdjunction Λ f).unit.app N).hom) ≫
      Functor.LaxMonoidal.μ (ProEtale.lowerStar Ab.{u + 1} f)
        ((upperStar Λ f).obj M).X ((upperStar Λ f).obj N).X ≫
      (ProEtale.lowerStar Ab.{u + 1} f).map
        (Mod.tensorObjπ ((upperStar Λ f).obj M) ((upperStar Λ f).obj N))) ∧
  ((upperStarLowerStarAdjunction Λ f).unit.app (𝟙_ _)).hom ≫
      (ProEtale.lowerStar Ab.{u + 1} f).map m.εIso.inv.hom =
    condensedPushforwardHom Λ f

private theorem module_unit_hom
    (M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) :
    ((upperStarLowerStarAdjunction Λ f).unit.app M).hom =
      (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} f).unit.app M.X ≫
        (ProEtale.lowerStar Ab.{u + 1} f).map
          (Mod.extendUnitHom (condensedPullbackHom Λ f)
            (((ProEtale.upperStar Ab.{u + 1} f).mapMod (condensedRingObj Λ Y)).obj M)) := by
  have h := upperStarLowerStarAdjunction_homEquiv_hom Λ f M _ (𝟙 _)
  rw [Adjunction.homEquiv_unit, CategoryTheory.Functor.map_id] at h
  erw [Category.comp_id] at h
  erw [Mod.id_hom', Category.comp_id] at h
  exact h

private theorem canonical_tensor_normalization :
    CondensedTensorNormalization Λ f
      (Functor.CoreMonoidal.ofOplaxMonoidal (upperStar Λ f)) := by
  constructor
  · intro M N
    change Mod.tensorObjπ M N ≫
        ((upperStarLowerStarAdjunction Λ f).unit.app (M ⊗ N)).hom ≫
        (ProEtale.lowerStar Ab.{u + 1} f).map
          (Functor.OplaxMonoidal.δ (upperStar Λ f) M N).hom = _
    let F := ProEtale.upperStar Ab.{u + 1} f
    let G := ProEtale.lowerStar Ab.{u + 1} f
    let E := Mod.extendScalars (condensedPullbackHom Λ f)
    let A := (F.mapMod (condensedRingObj Λ Y)).obj M
    let B := (F.mapMod (condensedRingObj Λ Y)).obj N
    let d := Functor.OplaxMonoidal.δ (F.mapMod (condensedRingObj Λ Y)) M N
    have hd : Functor.OplaxMonoidal.δ (upperStar Λ f) M N =
        E.map d ≫ Functor.OplaxMonoidal.δ E A B := rfl
    have hn := congrArg Mod.Hom.hom
      ((Mod.extendRestrictAdjunction (condensedPullbackHom Λ f)).unit.naturality d)
    simp only [Functor.id_map, Functor.comp_map, Mod.comp_hom', Mod.comap_map_hom,
      extendRestrictAdjunction_condensedPullbackHom_unit_app_hom] at hn
    rw [module_unit_hom, module_unit_hom, module_unit_hom, hd, Mod.comp_hom']
    have ht := (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} f).unit.naturality
      (Mod.tensorObjπ M N)
    dsimp only [Functor.id_map, Functor.comp_map] at ht
    simp only [Category.assoc]
    rw [reassoc_of% ht]
    rw [← G.map_comp, ← G.map_comp]
    have he : F.map (Mod.tensorObjπ M N) ≫
        (Mod.extendUnitHom (condensedPullbackHom Λ f)
          ((F.mapMod (condensedRingObj Λ Y)).obj (M ⊗ N)) ≫
          ((E.map d).hom ≫ (Functor.OplaxMonoidal.δ E A B).hom)) =
      Functor.OplaxMonoidal.δ F M.X N.X ≫
        (Mod.extendUnitHom (condensedPullbackHom Λ f) A ⊗ₘ
          Mod.extendUnitHom (condensedPullbackHom Λ f) B) ≫
            Mod.tensorObjπ (E.obj A) (E.obj B) := by
      rw [← reassoc_of% hn]
      erw [reassoc_of% (map_tensor_inverse (ProEtale.upperStar Ab.{u + 1} f) M N),
        extension_tensor_inverse (condensedPullbackHom Λ f)
          (extendUnitHom_extendScalarsIsoComapInv_hom_app Λ f) A B]
    rw [he, G.map_comp,
      (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} f).unit_app_tensor_comp_map_δ_assoc]
    rw [G.map_comp, ← Functor.LaxMonoidal.μ_natural_assoc]
    rw [tensorHom_comp_tensorHom_assoc]
    rfl
  · change ((upperStarLowerStarAdjunction Λ f).unit.app (𝟙_ _)).hom ≫
        (ProEtale.lowerStar Ab.{u + 1} f).map
          (Functor.Monoidal.εIso (upperStar Λ f)).inv.hom = _
    simpa only [Adjunction.homEquiv_unit, Mod.comp_hom', lowerStar,
      Functor.comp_map, Mod.comap_map_hom, Functor.mapMod, Mod.homMk] using
      homEquiv_εIso_inv_hom Λ f

/-- The ordinary tensor pullback has one uniquely normalized strong monoidal structure.
Source: Stacks 03EL (blueprint: lem-sfb-trace-base-change-first).
Proof: present relative tensor by its two balancing arrows. Inverse image preserves
this coequalizer and the abelian-sheaf tensor. Extension along alpha sends
s tensor (m tensor n) to (s tensor m) tensor (1 tensor n), with inverse multiplying
the coefficient factors. The adjunction unit gives precisely the displayed equations.
The balancing quotient and sheafification show that these equations determine the
maps uniquely. The associativity and unit diagrams agree on these generators, so
these maps constitute CoreMonoidal, uniquely, including its inverse and proof fields. -/
theorem condensedTensorCore_existsUnique :
    ∃! m : (upperStar Λ f).CoreMonoidal, CondensedTensorNormalization Λ f m := by
  let c := Functor.CoreMonoidal.ofOplaxMonoidal (upperStar Λ f)
  refine ⟨c, canonical_tensor_normalization Λ f, ?_⟩
  intro m hm
  have hη : m.εIso.inv = c.εIso.inv := by
    apply ((upperStarLowerStarAdjunction Λ f).homEquiv _ _).injective
    apply Mod.hom_ext
    simp only [Adjunction.homEquiv_unit, Mod.comp_hom']
    exact hm.2.trans (canonical_tensor_normalization Λ f).2.symm
  have hδ (M N : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y)) : (m.μIso M N).inv = (c.μIso M N).inv := by
    apply ((upperStarLowerStarAdjunction Λ f).homEquiv _ _).injective
    apply Mod.hom_ext
    simp only [Adjunction.homEquiv_unit, Mod.comp_hom']
    apply (cancel_epi (Mod.tensorObjπ M N)).1
    exact (hm.1 M N).trans ((canonical_tensor_normalization Λ f).1 M N).symm
  have he : m.εIso = c.εIso := Iso.ext_inv hη
  have ht : m.μIso = c.μIso := funext (fun M ↦ funext (fun N ↦ Iso.ext_inv (hδ M N)))
  have core_ext (m n : (upperStar Λ f).CoreMonoidal)
      (he : m.εIso = n.εIso) (ht : m.μIso = n.μIso) : m = n := by
    cases m
    cases n
    cases he
    cases ht
    rfl
  exact core_ext m c he ht

/-- The specified ordinary strong monoidal structure, selected by its unique equations.
Source: Stacks 03EL (blueprint: lem-sfb-trace-base-change-first). -/
def condensedTensorCore : (upperStar Λ f).CoreMonoidal :=
  (condensedTensorCore_existsUnique Λ f).exists.choose

private theorem condensedTensorCore_eq :
    condensedTensorCore Λ f =
      Functor.CoreMonoidal.ofOplaxMonoidal (upperStar Λ f) :=
  (condensedTensorCore_existsUnique Λ f).unique
    (condensedTensorCore_existsUnique Λ f).exists.choose_spec
    (canonical_tensor_normalization Λ f)

/-- Canonical strong monoidal module inverse image.
Source: Stacks 03EL (blueprint: lem-sfb-trace-base-change-first). -/
instance condensedUpperStarMonoidal : (upperStar Λ f).Monoidal :=
  (condensedTensorCore Λ f).toMonoidal

private theorem condensedUpperStarMonoidal_eq :
    condensedUpperStarMonoidal Λ f = monoidal_upperStar Λ f := by
  let := monoidal_upperStar Λ f
  unfold condensedUpperStarMonoidal
  rw [condensedTensorCore_eq]
  exact monoidal_core_roundtrip (upperStar Λ f)

attribute [local irreducible] condensedTensorCore condensedUpperStarMonoidal
private theorem ordinary_upperStar_braiding
    (M N : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y)) :
    Functor.LaxMonoidal.μ (upperStar Λ f) M N ≫ (upperStar Λ f).map (β_ M N).hom =
      (β_ ((upperStar Λ f).obj M) ((upperStar Λ f).obj N)).hom ≫
        Functor.LaxMonoidal.μ (upperStar Λ f) N M := by
  apply proof_transport_one
    (fun m : (upperStar Λ f).Monoidal ↦
      letI := m
      Functor.LaxMonoidal.μ (upperStar Λ f) M N ≫
          (upperStar Λ f).map (β_ M N).hom =
        (β_ ((upperStar Λ f).obj M) ((upperStar Λ f).obj N)).hom ≫
          Functor.LaxMonoidal.μ (upperStar Λ f) N M)
    (condensedUpperStarMonoidal_eq Λ f)
  let := monoidal_upperStar Λ f
  let G := ProEtale.upperStar Ab.{u + 1} f
  let : (G.mapMod (condensedRingObj Λ Y)).LaxBraided :=
    { braided := mapMod_braided G }
  let := extend_braided (condensedPullbackHom Λ f)
  exact Functor.LaxBraided.braided (F := G.mapMod (condensedRingObj Λ Y) ⋙
    Mod.extendScalars (condensedPullbackHom Λ f)) M N

/-- Module inverse image preserves flat modules.
Source: Stacks 0G7E (blueprint: lem-sfb-trace-base-change-first).
Proof: pass through the exact internal-to-sectionwise module equivalence. The
normalized tensor comparison is the usual scalar-extension comparison there by its
unit-generator equations. Pullback of a flat sheaf is flat by the local tensor
criterion, so tensoring with the pulled-back module is exact. Transport back through
the exact equivalence. This is flatness in the existing monoidal module category. -/
@[instance] theorem condensedUpperStarPreservesFlat : (upperStar Λ f).PreservesFlat := by
  have hf := inverseImageModule_preservesFlat f (condensedRingObj Λ Y)
    (condensedRingObj Λ X) (asIso (condensedPullbackHom Λ f)).inv
  refine ⟨fun {M} hM ↦ ?_⟩
  exact ObjectProperty.flat.prop_of_iso
    ((Functor.isoWhiskerLeft
      ((ProEtale.upperStar Ab.{u + 1} f).mapMod (condensedRingObj Λ Y))
      (Mod.extendScalarsIsoComapInv (condensedPullbackHom Λ f))).app M).symm
    (hf.flat_obj hM)


/-- The canonical derived unit comparison, computed on the regular module in degree zero.
Source: Stacks 07A4 (blueprint: lem-sfb-trace-base-change-first). -/
def condensedDerivedUnitIso :
    (upperStar Λ f).leftDerivedFunctor.obj (𝟙_ _) ≅ 𝟙_ _ :=
  (upperStar Λ f).traceDegreeZeroUnitIso


end TensorPullbackHelpers

section CompositionCoherence
attribute [local irreducible] Mod.monoidalCategoryStruct
set_option backward.isDefEq.respectTransparency false
private theorem lower_mu_pi
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    letI := (upperStarLowerStarAdjunction Λ f).rightAdjointLaxMonoidal
    Mod.tensorObjπ ((lowerStar Λ f).obj M) ((lowerStar Λ f).obj N) ≫
      (Functor.LaxMonoidal.μ (lowerStar Λ f) M N).hom =
    Functor.LaxMonoidal.μ (ProEtale.lowerStar Ab.{u + 1} f) M.X N.X ≫
      (ProEtale.lowerStar Ab.{u + 1} f).map (Mod.tensorObjπ M N) := by
  let := (upperStarLowerStarAdjunction Λ f).rightAdjointLaxMonoidal
  let a := upperStarLowerStarAdjunction Λ f
  let G := ProEtale.lowerStar Ab.{u + 1} f
  change Mod.tensorObjπ ((lowerStar Λ f).obj M) ((lowerStar Λ f).obj N) ≫
    (a.homEquiv _ _ (Functor.OplaxMonoidal.δ (upperStar Λ f)
      ((lowerStar Λ f).obj M) ((lowerStar Λ f).obj N) ≫
      (a.counit.app M ⊗ₘ a.counit.app N))).hom = _
  rw [Adjunction.homEquiv_unit]
  simp only [Mod.comp_hom', Functor.map_comp, lowerStar_map_hom]
  erw [reassoc_of% ((condensedTensorCore_existsUnique Λ f).exists.choose_spec.1
    ((lowerStar Λ f).obj M) ((lowerStar Λ f).obj N))]
  erw [← Functor.map_comp]
  rw [MonoidalCategory.tensorHom_def (a.counit.app M) (a.counit.app N)]
  simp only [Mod.comp_hom']
  erw [Mod.tensorObjπ_whiskerRight_assoc, Mod.tensorObjπ_whiskerLeft]
  rw [← MonoidalCategory.tensorHom_def_assoc]
  rw [G.map_comp]
  erw [← Functor.LaxMonoidal.μ_natural_assoc]
  rw [← Category.assoc, tensorHom_comp_tensorHom]
  have hM := congrArg Mod.Hom.hom (a.right_triangle_components M)
  have hN := congrArg Mod.Hom.hom (a.right_triangle_components N)
  simp only [Mod.comp_hom', lowerStar_map_hom, Mod.id_hom'] at hM hN
  erw [hM, hN, tensorHom_id, id_whiskerRight, Category.id_comp]


private theorem lower_comp_tensor
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    letI := (upperStarLowerStarAdjunction Λ f).rightAdjointLaxMonoidal
    letI := (upperStarLowerStarAdjunction Λ g).rightAdjointLaxMonoidal
    letI := (upperStarLowerStarAdjunction Λ (f ≫ g)).rightAdjointLaxMonoidal
    Functor.LaxMonoidal.μ (lowerStar Λ f ⋙ lowerStar Λ g) M N ≫
      (lowerStarComp Λ f g).hom.app (M ⊗ N) =
    ((lowerStarComp Λ f g).hom.app M ⊗ₘ (lowerStarComp Λ f g).hom.app N) ≫
      Functor.LaxMonoidal.μ (lowerStar Λ (f ≫ g)) M N := by
  let := (upperStarLowerStarAdjunction Λ f).rightAdjointLaxMonoidal
  let := (upperStarLowerStarAdjunction Λ g).rightAdjointLaxMonoidal
  let := (upperStarLowerStarAdjunction Λ (f ≫ g)).rightAdjointLaxMonoidal
  apply Mod.hom_ext
  apply (cancel_epi (Mod.tensorObjπ
    ((lowerStar Λ f ⋙ lowerStar Λ g).obj M)
    ((lowerStar Λ f ⋙ lowerStar Λ g).obj N))).1
  simp only [Functor.LaxMonoidal.comp_μ, Mod.comp_hom', lowerStar_map_hom,
    lowerStarComp_hom_app_hom, Functor.comp_obj, Category.assoc]
  erw [reassoc_of% (lower_mu_pi Λ g ((lowerStar Λ f).obj M)
    ((lowerStar Λ f).obj N))]
  erw [← Functor.map_comp_assoc, lower_mu_pi Λ f M N]
  erw [reassoc_of% (tensorπ_tensorHom ((lowerStarComp Λ f g).hom.app M)
    ((lowerStarComp Λ f g).hom.app N))]
  erw [lower_mu_pi Λ (f ≫ g) M N]
  simp only [lowerStarComp_hom_app_hom, Functor.map_comp, Category.assoc]
  erw [(ProEtale.lowerStarComp Ab.{u + 1} f g).hom.naturality
    (Mod.tensorObjπ M N)]
  rw [← Category.assoc, ← Category.assoc]
  exact congrArg (fun z ↦ z ≫ (ProEtale.lowerStar Ab.{u + 1} (f ≫ g)).map
    (Mod.tensorObjπ M N))
    (NatTrans.IsMonoidal.tensor (τ := (ProEtale.lowerStarComp Ab.{u + 1} f g).hom)
      M.X N.X)

private theorem upper_comp_tensor
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (M N : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z)) :
    Functor.LaxMonoidal.μ (upperStar Λ (f ≫ g)) M N ≫
      (upperStarComp Λ f g).hom.app (M ⊗ N) =
    ((upperStarComp Λ f g).hom.app M ⊗ₘ (upperStarComp Λ f g).hom.app N) ≫
      Functor.LaxMonoidal.μ (upperStar Λ g ⋙ upperStar Λ f) M N := by
  let := (upperStarLowerStarAdjunction Λ f).rightAdjointLaxMonoidal
  let := (upperStarLowerStarAdjunction Λ g).rightAdjointLaxMonoidal
  let := (upperStarLowerStarAdjunction Λ (f ≫ g)).rightAdjointLaxMonoidal
  have hi : (conjugateEquiv
      ((upperStarLowerStarAdjunction Λ g).comp (upperStarLowerStarAdjunction Λ f))
      (upperStarLowerStarAdjunction Λ (f ≫ g))).symm
        (lowerStarComp Λ f g).hom = (upperStarComp Λ f g).hom := by
    apply (conjugateEquiv _ _).injective
    rw [Equiv.apply_symm_apply]
    exact (congrArg Iso.hom (conjugateIsoEquiv_upperStarComp Λ f g)).symm
  have ht := conjugate_tensor_only
    ((upperStarLowerStarAdjunction Λ g).comp (upperStarLowerStarAdjunction Λ f))
    (upperStarLowerStarAdjunction Λ (f ≫ g)) (lowerStarComp Λ f g).hom
    (lower_comp_tensor Λ f g) M N
  rw [hi] at ht
  rw [← cancel_mono (Functor.OplaxMonoidal.δ (upperStar Λ g ⋙ upperStar Λ f) M N),
    Category.assoc, ht, Functor.Monoidal.μ_δ_assoc, Category.assoc,
    Functor.Monoidal.μ_δ, Category.comp_id]

private theorem upper_comp_monoidal
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    NatTrans.IsMonoidal (upperStarComp Λ f g).hom := by
  constructor
  · apply proof_transport_three
      (fun (mf : (upperStar Λ f).Monoidal) (mg : (upperStar Λ g).Monoidal)
          (mfg : (upperStar Λ (f ≫ g)).Monoidal) ↦
        letI := mf
        letI := mg
        letI := mfg
        Functor.LaxMonoidal.ε (upperStar Λ (f ≫ g)) ≫
            (upperStarComp Λ f g).hom.app (𝟙_ _) =
          Functor.LaxMonoidal.ε (upperStar Λ g ⋙ upperStar Λ f))
      (condensedUpperStarMonoidal_eq Λ f) (condensedUpperStarMonoidal_eq Λ g)
      (condensedUpperStarMonoidal_eq Λ (f ≫ g))
    let := monoidal_upperStar Λ f
    let := monoidal_upperStar Λ g
    let := monoidal_upperStar Λ (f ≫ g)
    refine unit_of_oplax (upperStarComp Λ f g).hom ?_
    simpa only [Functor.OplaxMonoidal.comp_η, Functor.Monoidal.εIso_inv] using
      upperStarComp_hom_app_unit Λ f g
  · exact upper_comp_tensor Λ f g
end CompositionCoherence

attribute [local irreducible] condensedTensorCore condensedUpperStarMonoidal

/-- The adjunction transpose defining projection, expressed over abstract categories.
Source: Stacks 0B56 (blueprint: lem-sfb-trace-base-change-first). -/
def traceProjectionFromComparison
    {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
    [MonoidalCategory C] [MonoidalCategory D]
    {F : C ⥤ D} {P : D ⥤ C} (adj : F ⊣ P)
    (δ : ∀ K M : C, F.obj (K ⊗ M) ⟶ F.obj K ⊗ F.obj M) (K : C) (N : D) :
    K ⊗ P.obj N ⟶ P.obj (F.obj K ⊗ N) :=
  adj.homEquiv (K ⊗ P.obj N) (F.obj K ⊗ N)
    (δ K (P.obj N) ≫ (𝟙 (F.obj K) ⊗ₘ adj.counit.app N))

/-- Compose the specified symmetry, inverse projection and inverse base change.
The concrete B below supplies only the canonical comparisons.
Source: blueprint definition of B (blueprint: lem-sfb-trace-base-change-first). -/
def traceBFromComparisons
    {C : Type u₁} {D : Type u₂} {V : Type u₃}
    [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} V]
    [MonoidalCategory D] [MonoidalCategory V]
    (F : C ⥤ D) (P : D ⥤ C) (U₁ U₂ : D ⥤ V) (Q : V ⥤ D)
    (TY : C) (N : D)
    (s : U₂.obj (F.obj TY) ≅ U₁.obj (F.obj TY))
    (π : F.obj TY ⊗ Q.obj (U₁.obj N) ≅
      Q.obj (U₂.obj (F.obj TY) ⊗ U₁.obj N))
    (b : F.obj (P.obj N) ≅ Q.obj (U₁.obj N))
    (σ : U₁.obj N ⊗ U₁.obj (F.obj TY) ≅ U₁.obj (F.obj TY) ⊗ U₁.obj N)
    (τ : F.obj TY ⊗ Q.obj (U₁.obj N) ≅ Q.obj (U₁.obj N) ⊗ F.obj TY) :
    Q.obj (U₁.obj N ⊗ U₁.obj (F.obj TY)) ≅ F.obj (P.obj N) ⊗ F.obj TY :=
  Q.mapIso (σ ≪≫ tensorIso s.symm (Iso.refl _)) ≪≫ π.symm ≪≫ τ ≪≫
    tensorIso b.symm (Iso.refl _)

private theorem traceBFromComparisons_naturality
    {C : Type u₁} {D : Type u₂} {V : Type u₃}
    [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} V]
    [MonoidalCategory D] [MonoidalCategory V]
    (F : C ⥤ D) (P : D ⥤ C) (U₁ U₂ : D ⥤ V) (Q : V ⥤ D)
    (TY : C) {M N : D} (m : M ⟶ N)
    (s : U₂.obj (F.obj TY) ≅ U₁.obj (F.obj TY))
    (πM : F.obj TY ⊗ Q.obj (U₁.obj M) ≅
      Q.obj (U₂.obj (F.obj TY) ⊗ U₁.obj M))
    (πN : F.obj TY ⊗ Q.obj (U₁.obj N) ≅
      Q.obj (U₂.obj (F.obj TY) ⊗ U₁.obj N))
    (bM : F.obj (P.obj M) ≅ Q.obj (U₁.obj M))
    (bN : F.obj (P.obj N) ≅ Q.obj (U₁.obj N))
    (σM : U₁.obj M ⊗ U₁.obj (F.obj TY) ≅ U₁.obj (F.obj TY) ⊗ U₁.obj M)
    (σN : U₁.obj N ⊗ U₁.obj (F.obj TY) ≅ U₁.obj (F.obj TY) ⊗ U₁.obj N)
    (τM : F.obj TY ⊗ Q.obj (U₁.obj M) ≅ Q.obj (U₁.obj M) ⊗ F.obj TY)
    (τN : F.obj TY ⊗ Q.obj (U₁.obj N) ≅ Q.obj (U₁.obj N) ⊗ F.obj TY)
    (hπ : (𝟙 _ ⊗ₘ Q.map (U₁.map m)) ≫ πN.hom =
      πM.hom ≫ Q.map (𝟙 _ ⊗ₘ U₁.map m))
    (hb : F.map (P.map m) ≫ bN.hom = bM.hom ≫ Q.map (U₁.map m))
    (hσ : (U₁.map m ⊗ₘ 𝟙 _) ≫ σN.hom = σM.hom ≫ (𝟙 _ ⊗ₘ U₁.map m))
    (hτ : (𝟙 _ ⊗ₘ Q.map (U₁.map m)) ≫ τN.hom =
      τM.hom ≫ (Q.map (U₁.map m) ⊗ₘ 𝟙 _)) :
    Q.map (U₁.map m ⊗ₘ 𝟙 _) ≫
        (traceBFromComparisons F P U₁ U₂ Q TY N s πN bN σN τN).hom =
      (traceBFromComparisons F P U₁ U₂ Q TY M s πM bM σM τM).hom ≫
        (F.map (P.map m) ⊗ₘ 𝟙 _) := by
  have hc : (U₁.map m ⊗ₘ 𝟙 _) ≫
      (σN.hom ≫ (s.inv ⊗ₘ 𝟙 _)) =
      (σM.hom ≫ (s.inv ⊗ₘ 𝟙 _)) ≫ (𝟙 _ ⊗ₘ U₁.map m) := by
    rw [← Category.assoc, hσ, Category.assoc, Category.assoc]
    congr 1
    simp only [tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id]
  have hp : Q.map (𝟙 _ ⊗ₘ U₁.map m) ≫ πN.inv =
      πM.inv ≫ (𝟙 _ ⊗ₘ Q.map (U₁.map m)) := by
    apply (cancel_epi πM.hom).1
    simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
    rw [← hπ, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hbi : Q.map (U₁.map m) ≫ bN.inv = bM.inv ≫ F.map (P.map m) := by
    apply (cancel_epi bM.hom).1
    simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
    rw [← hb, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  simp only [traceBFromComparisons, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, tensorIso_hom, Iso.refl_hom, Category.assoc]
  rw [← Q.map_comp_assoc, hc, Q.map_comp, Category.assoc,
    reassoc_of% hp, reassoc_of% hτ]
  simp only [tensorHom_comp_tensorHom, Category.comp_id, hbi]

/-- The trace hypotheses written over arbitrary monoidal categories. Specialization below
supplies the canonical module functors, square mates, projection maps and unit comparison.
Source: blueprint hypotheses (blueprint: lem-sfb-trace-base-change-first). -/
structure TraceFirstHypotheses
    {C : Type u₁} {D : Type u₂} {V : Type u₃}
    [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} V]
    [MonoidalCategory C] [MonoidalCategory D] [MonoidalCategory V]
    (LC : ObjectProperty C) (LD : ObjectProperty D) (LV : ObjectProperty V)
    (F : C ⥤ D) (P : D ⥤ C) (U₁ U₂ : D ⥤ V) (Q₁ Q₂ : V ⥤ D)
    (s : F ⋙ U₂ ≅ F ⋙ U₁)
    (b₁ : P ⋙ F ⟶ U₂ ⋙ Q₁) (b₂ : P ⋙ F ⟶ U₁ ⋙ Q₂)
    (unitIso : F.obj (𝟙_ C) ≅ 𝟙_ D)
    (πF : ∀ (K : C) (N : D), K ⊗ P.obj N ⟶ P.obj (F.obj K ⊗ N))
    (πP : ∀ (K : D) (N : V), K ⊗ Q₁.obj N ⟶ Q₁.obj (U₁.obj K ⊗ N))
    (πQ : ∀ (K : D) (N : V), K ⊗ Q₂.obj N ⟶ Q₂.obj (U₂.obj K ⊗ N))
    (TY : C) where
  /-- The trace for f. -/
  t : P.obj (F.obj TY) ⟶ 𝟙_ C
  /-- The trace for p1, on the common twist. -/
  t₁ : Q₁.obj (U₁.obj (F.obj TY)) ⟶ 𝟙_ D
  /-- The trace for p2, on the common twist. -/
  t₂ : Q₂.obj (U₁.obj (F.obj TY)) ⟶ 𝟙_ D
  /-- The first trace compatibility, including the square comparison. -/
  trace₁ : b₁.app (F.obj TY) ≫ Q₁.map (s.hom.app TY) ≫ t₁ =
    F.map t ≫ unitIso.hom
  /-- The second trace compatibility. -/
  trace₂ : b₂.app (F.obj TY) ≫ t₂ = F.map t ≫ unitIso.hom
  /-- The first base-change mate is invertible on the localizing category. -/
  base₁ : ∀ N : D, LD N → IsIso (b₁.app N)
  /-- The second base-change mate is invertible on the localizing category. -/
  base₂ : ∀ N : D, LD N → IsIso (b₂.app N)
  /-- The projections used to define e are invertible. -/
  projectionF : ∀ K : C, LC K → IsIso (πF K (F.obj TY))
  /-- The projections on the right side are invertible. -/
  projectionP : ∀ N : D, LD N → IsIso (πP N (U₁.obj (F.obj TY)))
  /-- The projections used in B are invertible. -/
  projectionQ : ∀ N : D, LD N → IsIso (πQ (F.obj TY) (U₁.obj N))
  /-- Preservation by the inverse image of f. -/
  pullF : ∀ K : C, LC K → LD (F.obj K)
  /-- Preservation by the direct image of f. -/
  pushF : ∀ N : D, LD N → LC (P.obj N)
  /-- Preservation by the inverse image of p1. -/
  pullP : ∀ N : D, LD N → LV (U₁.obj N)
  /-- Preservation by the direct image of p1. -/
  pushP : ∀ N : V, LV N → LD (Q₁.obj N)
  /-- Preservation by the inverse image of p2. -/
  pullQ : ∀ N : D, LD N → LV (U₂.obj N)
  /-- Preservation by the direct image of p2. -/
  pushQ : ∀ N : V, LV N → LD (Q₂.obj N)
  /-- Preservation by G. -/
  preservesG : ∀ K : C, LC K → LD (F.obj K ⊗ F.obj TY)
  /-- Preservation by H. -/
  preservesH : ∀ N : D, LD N → LV (U₁.obj N ⊗ U₁.obj (F.obj TY))


/-- Trace evaluation by an inverse projection, with the right unit identification.
Source: blueprint definition of e (blueprint: lem-sfb-trace-base-change-first). -/
def traceAbstractCounit
    {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
    [MonoidalCategory C] [MonoidalCategory D]
    (F : C ⥤ D) (P : D ⥤ C) (K : C) (T : D)
    (π : K ⊗ P.obj T ⟶ P.obj (F.obj K ⊗ T)) (hπ : IsIso π)
    (t : P.obj T ⟶ 𝟙_ C) : P.obj (F.obj K ⊗ T) ⟶ K :=
  @inv _ _ _ _ π hπ ≫ (𝟙 K ⊗ₘ t) ≫ (ρ_ K).hom


/-- A square mate, with the canonical adjunctions supplied as data.
Source: Stacks 07A7 (blueprint: lem-sfb-trace-base-change-first). -/
def traceAbstractMate
    {C : Type u₁} {D : Type u₂} {V : Type u₃}
    [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} V]
    {F : C ⥤ D} {P : D ⥤ C} {U₁ U₂ : D ⥤ V} {Q : V ⥤ D}
    (a : F ⊣ P) (b : U₂ ⊣ Q) (s : F ⋙ U₂ ≅ F ⋙ U₁) :
    P ⋙ F ⟶ U₁ ⋙ Q :=
  (mateEquiv a b (TwoSquare.mk _ _ _ _ s.hom)).natTrans

private theorem scalar_evaluation
    {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D]
    {F : C ⥤ D} {P : D ⥤ C} [F.Monoidal] (a : F ⊣ P)
    (N : D) (K : C) (t : K ⟶ 𝟙_ C) :
    ((a.rightAdjointProjectionMap (Functor.OplaxMonoidal.δNatTrans F)).app N).app K ≫
        P.map (𝟙 N ⊗ₘ F.map t) ≫
        P.map (𝟙 N ⊗ₘ Functor.OplaxMonoidal.η F) ≫ P.map (ρ_ N).hom =
      (𝟙 (P.obj N) ⊗ₘ t) ≫ (ρ_ (P.obj N)).hom := by
  have hn := ((a.rightAdjointProjectionMap
    (Functor.OplaxMonoidal.δNatTrans F)).app N).naturality t
  dsimp at hn
  simp only [← id_tensorHom] at hn
  change (𝟙 (P.obj N) ⊗ₘ t) ≫
      ((a.rightAdjointProjectionMap (Functor.OplaxMonoidal.δNatTrans F)).app N).app (𝟙_ C) =
    ((a.rightAdjointProjectionMap (Functor.OplaxMonoidal.δNatTrans F)).app N).app K ≫
      P.map (𝟙 N ⊗ₘ F.map t) at hn
  rw [← reassoc_of% hn]
  have hu := a.rightAdjointProjectionMap_rightUnitality
    (Functor.OplaxMonoidal.δNatTrans F) (Functor.OplaxMonoidal.η F)
    (fun X ↦ Functor.OplaxMonoidal.right_unitality_hom F X) N
  simpa only [Category.assoc, id_tensorHom] using congrArg
    (fun z ↦ (𝟙 (P.obj N) ⊗ₘ t) ≫ z) hu

section Symmetry
variable {C D : Type*} [Category C] [Category D]
  [MonoidalCategory C] [SymmetricCategory C] [MonoidalCategory D] [SymmetricCategory D]
  {F : C ⥤ D} {P : D ⥤ C} [F.Braided] (a : F ⊣ P)

private theorem fixed_projection_eq (K : C) (N : D) :
    a.homEquiv _ _ (Functor.OplaxMonoidal.δ F K (P.obj N) ≫
      (𝟙 (F.obj K) ⊗ₘ a.counit.app N)) = a.leftCoefficientProjectionMap K N := by
  apply (a.homEquiv _ _).symm.injective
  simpa only [Equiv.symm_apply_apply, Adjunction.homEquiv_counit, Functor.id_obj] using
    ((a.leftCoefficientProjectionMap_coherence).2.1 K N).symm

private theorem direct_projection_eq (N : D) (K : C) :
    ((a.rightAdjointProjectionMap (Functor.OplaxMonoidal.δNatTrans F)).app N).app K =
      (β_ (P.obj N) K).hom ≫
        a.homEquiv _ _ (Functor.OplaxMonoidal.δ F K (P.obj N) ≫
          (𝟙 (F.obj K) ⊗ₘ a.counit.app N)) ≫ P.map (β_ (F.obj K) N).hom := by
  rw [fixed_projection_eq, Adjunction.leftCoefficientProjectionMap]
  simp only [← Category.assoc, SymmetricCategory.symmetry, Category.id_comp]
  rw [Category.assoc, ← P.map_comp,
    SymmetricCategory.symmetry]
  erw [P.map_id, Category.comp_id]
end Symmetry

set_option backward.isDefEq.respectTransparency false in
private theorem B_inverse
    {C D V : Type*} [Category C] [Category D] [Category V]
    [MonoidalCategory D] [SymmetricCategory D]
    [MonoidalCategory V] [SymmetricCategory V]
    (F : C ⥤ D) (P : D ⥤ C) (U₁ U₂ : D ⥤ V) (Q : V ⥤ D)
    [U₂.Braided] (a : U₂ ⊣ Q) (TY : C) (N : D)
    (s : U₂.obj (F.obj TY) ≅ U₁.obj (F.obj TY))
    (hπ : IsIso (traceProjectionFromComparison a (Functor.OplaxMonoidal.δ U₂)
      (F.obj TY) (U₁.obj N)))
    (b : F.obj (P.obj N) ≅ Q.obj (U₁.obj N)) :
    (traceBFromComparisons F P U₁ U₂ Q TY N s
      (@asIso _ _ _ _ _ hπ) b (β_ _ _) (β_ _ _)).inv =
      (b.hom ⊗ₘ 𝟙 _) ≫
        ((a.rightAdjointProjectionMap (Functor.OplaxMonoidal.δNatTrans U₂)).app
          (U₁.obj N)).app (F.obj TY) ≫ Q.map (𝟙 _ ⊗ₘ s.hom) := by
  rw [direct_projection_eq]
  simp only [traceBFromComparisons, Iso.trans_inv, Iso.symm_inv, tensorIso_inv,
    Iso.refl_inv, Functor.mapIso_inv, asIso_hom, traceProjectionFromComparison,
    Functor.id_obj, Category.assoc]
  rw [← Q.map_comp]
  simp only [SymmetricCategory.braiding_swap_eq_inv_braiding]
  congr 3
  apply Q.congr_map
  exact BraidedCategory.braiding_inv_naturality _ _

set_option backward.isDefEq.respectTransparency false in
private theorem first_transpose
    {A B C : Type*} [Category A] [Category B] [Category C]
    {F : A ⥤ B} {R : B ⥤ A} {H : B ⥤ C} {S : C ⥤ B}
    (adj : F ⊣ R) (adj' : H ⊣ S)
    (T : A × A ⥤ A) (U : B × B ⥤ B) (V : C × C ⥤ C)
    (t : T ⋙ F ⟶ (F.prod F) ⋙ U) (h : U ⋙ H ⟶ (H.prod H) ⋙ V)
    (M N : B) (Z : C) (ex : F.obj (R.obj M) ⟶ S.obj Z) :
    ((adj.comp adj').homEquiv _ _).symm
      (adj.homEquiv _ _ (t.app (R.obj M, R.obj N) ≫
          U.map (Prod.mkHom (𝟙 _) (adj.counit.app N))) ≫
        R.map (U.map (Prod.mkHom ex (𝟙 N)) ≫
          adj'.homEquiv _ _ (h.app (S.obj Z, N) ≫
            V.map (Prod.mkHom (adj'.counit.app Z) (𝟙 _))))) =
      H.map (t.app (R.obj M, R.obj N)) ≫
        h.app (F.obj (R.obj M), F.obj (R.obj N)) ≫
        V.map (Prod.mkHom (H.map ex ≫ adj'.counit.app Z)
          (H.map (adj.counit.app N))) := by
  rw [Adjunction.comp_homEquiv]
  dsimp only [Functor.id_obj, Functor.comp_obj, Functor.prod_obj]
  rw [Equiv.symm_trans_apply]
  erw [adj.homEquiv_naturality_right_symm,
    Equiv.symm_apply_apply]
  erw [adj'.homEquiv_naturality_left_symm, adj'.homEquiv_naturality_left_symm,
    Equiv.symm_apply_apply]
  simp only [Functor.map_comp, Category.assoc]
  have hn := h.naturality
    (Prod.mkHom (𝟙 (F.obj (R.obj M))) (adj.counit.app N))
  have he := h.naturality (Prod.mkHom ex (𝟙 N))
  dsimp only [Functor.comp_map, Functor.prod_map] at hn he
  rw [reassoc_of% he, reassoc_of% hn]
  simp only [← V.map_comp]
  congr 2
  congr 1
  ext <;> simp

set_option backward.isDefEq.respectTransparency false in
private theorem second_transpose
    {A B C : Type*} [Category A] [Category B] [Category C]
    {F : A ⥤ B} {R : B ⥤ A} {H : B ⥤ C} {S : C ⥤ B}
    (adj : F ⊣ R) (adj' : H ⊣ S)
    (T : A × A ⥤ A) (U : B × B ⥤ B) (V : C × C ⥤ C)
    (t : T ⋙ F ⟶ (F.prod F) ⋙ U) (h : U ⋙ H ⟶ (H.prod H) ⋙ V)
    (M N : B) (Z : C) (ex : F.obj (R.obj N) ⟶ S.obj Z) :
    ((adj.comp adj').homEquiv _ _).symm
      (adj.homEquiv _ _ (t.app (R.obj M, R.obj N) ≫
          U.map (Prod.mkHom (adj.counit.app M) (𝟙 _))) ≫
        R.map (U.map (Prod.mkHom (𝟙 M) ex) ≫
          adj'.homEquiv _ _ (h.app (M, S.obj Z) ≫
            V.map (Prod.mkHom (𝟙 _) (adj'.counit.app Z))))) =
      H.map (t.app (R.obj M, R.obj N)) ≫
        h.app (F.obj (R.obj M), F.obj (R.obj N)) ≫
        V.map (Prod.mkHom (H.map (adj.counit.app M))
          (H.map ex ≫ adj'.counit.app Z)) := by
  rw [Adjunction.comp_homEquiv]
  dsimp only [Functor.id_obj, Functor.comp_obj, Functor.prod_obj]
  rw [Equiv.symm_trans_apply]
  erw [adj.homEquiv_naturality_right_symm,
    Equiv.symm_apply_apply]
  erw [adj'.homEquiv_naturality_left_symm, adj'.homEquiv_naturality_left_symm,
    Equiv.symm_apply_apply]
  simp only [Functor.map_comp, Category.assoc]
  have hn := h.naturality
    (Prod.mkHom (adj.counit.app M) (𝟙 (F.obj (R.obj N))))
  have he := h.naturality (Prod.mkHom (𝟙 M) ex)
  dsimp only [Functor.comp_map, Functor.prod_map] at hn he
  rw [reassoc_of% he, reassoc_of% hn]
  simp only [← V.map_comp]
  congr 2
  congr 1
  ext <;> simp

set_option backward.isDefEq.respectTransparency false in
private theorem conjugate_transpose
    {A B : Type*} [Category A] [Category B]
    {F G : A ⥤ B} {R S : B ⥤ A} (adj : F ⊣ R) (adj' : G ⊣ S)
    (theta : G ≅ F) {T : A} {Z : B} (f : T ⟶ S.obj Z) :
    (adj.homEquiv _ _).symm
        (f ≫ (conjugateIsoEquiv adj adj' theta).inv.app Z) =
      theta.inv.app T ≫ (adj'.homEquiv _ _).symm f := by
  change F.map (f ≫ (conjugateEquiv adj' adj theta.inv).app Z) ≫
      adj.counit.app Z = _
  rw [Functor.map_comp, Category.assoc, conjugateEquiv_counit]
  rw [← Category.assoc, theta.inv.naturality f]
  simp only [Category.assoc, Adjunction.homEquiv_counit]

set_option backward.isDefEq.respectTransparency false in
private theorem kunneth_factorization
    {C D V : Type*} [Category C] [Category D] [Category V]
    {F : C ⥤ D} {P : D ⥤ C} {U₁ U₂ : D ⥤ V} {Q₁ Q₂ : V ⥤ D}
    (a : F ⊣ P) (a₁ : U₁ ⊣ Q₁) (a₂ : U₂ ⊣ Q₂)
    (T : C × C ⥤ C) (U : D × D ⥤ D) (R : V × V ⥤ V)
    (d : T ⋙ F ⟶ (F.prod F) ⋙ U)
    (d₁ : U ⋙ U₁ ⟶ (U₁.prod U₁) ⋙ R)
    (d₂ : U ⋙ U₂ ⟶ (U₂.prod U₂) ⋙ R)
    (s : F ⋙ U₂ ≅ F ⋙ U₁)
    (hs : ∀ K L : C,
      s.hom.app (T.obj (K, L)) ≫ U₁.map (d.app (K, L)) ≫
          d₁.app (F.obj K, F.obj L) =
        U₂.map (d.app (K, L)) ≫ d₂.app (F.obj K, F.obj L) ≫
          R.map (Prod.mkHom (s.hom.app K) (s.hom.app L)))
    (M N : D) :
    a.homEquiv _ _ (d.app (P.obj M, P.obj N) ≫
        U.map (Prod.mkHom (𝟙 _) (a.counit.app N))) ≫
      P.map (U.map (Prod.mkHom (traceAbstractMate a a₂ s |>.app M) (𝟙 N)) ≫
        a₂.homEquiv _ _ (d₂.app (Q₂.obj (U₁.obj M), N) ≫
          R.map (Prod.mkHom (a₂.counit.app (U₁.obj M)) (𝟙 _)))) ≫
      (conjugateIsoEquiv (a.comp a₂) (a.comp a₁) s.symm).hom.app
        (R.obj (U₁.obj M, U₂.obj N)) =
    a.homEquiv _ _ (d.app (P.obj M, P.obj N) ≫
        U.map (Prod.mkHom (a.counit.app M) (𝟙 _))) ≫
      P.map (U.map (Prod.mkHom (𝟙 M) (traceAbstractMate a a₁ s.symm |>.app N)) ≫
        a₁.homEquiv _ _ (d₁.app (M, Q₁.obj (U₂.obj N)) ≫
          R.map (Prod.mkHom (𝟙 _) (a₁.counit.app (U₂.obj N))))) := by
  have hex := mateEquiv_counit a a₂ (TwoSquare.mk _ _ _ _ s.hom) M
  have hbar := mateEquiv_counit a a₁ (TwoSquare.mk _ _ _ _ s.inv) N
  change U₂.map ((traceAbstractMate a a₂ s).app M) ≫ a₂.counit.app (U₁.obj M) =
    s.hom.app (P.obj M) ≫ U₁.map (a.counit.app M) at hex
  change U₁.map ((traceAbstractMate a a₁ s.symm).app N) ≫ a₁.counit.app (U₂.obj N) =
    s.inv.app (P.obj N) ≫ U₂.map (a.counit.app N) at hbar
  have hF := first_transpose a a₂ T U R d d₂ M N (U₁.obj M)
    ((traceAbstractMate a a₂ s).app M)
  rw [hex] at hF
  have hG := second_transpose a a₁ T U R d d₁ M N (U₂.obj N)
    ((traceAbstractMate a a₁ s.symm).app N)
  rw [hbar] at hG
  apply ((a.comp a₁).homEquiv _ _).symm.injective
  have hc : (conjugateIsoEquiv (a.comp a₂) (a.comp a₁) s.symm).hom =
      (conjugateIsoEquiv (a.comp a₁) (a.comp a₂) s).inv := rfl
  rw [hc, ← Category.assoc]
  erw [conjugate_transpose (a.comp a₁) (a.comp a₂) s]
  dsimp only [Functor.comp_obj, Functor.id_obj, Prod.fst, Prod.snd] at hF hG ⊢
  erw [hF, hG]
  apply (cancel_epi (s.hom.app (T.obj (P.obj M, P.obj N)))).1
  simp only [← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]
  simp only [Category.assoc]
  rw [reassoc_of% (hs (P.obj M) (P.obj N))]
  simp only [← R.map_comp]
  congr 2
  congr 1
  ext <;> simp

/-- Extract a component of a tensor comparison at its declared endpoints.
Source: Stacks 07A4 (blueprint: lem-sfb-trace-base-change-first). -/
def traceTensorComponent
    {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
    [MonoidalCategory C] [MonoidalCategory D] (F : C ⥤ D)
    (δ : (Functor.postcompose₂.obj F).obj (curriedTensor C) ⟶
      (((Functor.whiskeringLeft₂ _).obj F).obj F).obj (curriedTensor D)) (K M : C) :
    F.obj (K ⊗ M) ⟶ F.obj K ⊗ F.obj M :=
  (δ.app K).app M

/-- The complete displayed formula, on arbitrary monoidal categories. Its specialization
below fixes every functor, adjunction, mate, tensor comparison and symmetry canonically.
The conclusion includes the naturality of B and the stated trace identity.
Source: blueprint first triangle (blueprint: lem-sfb-trace-base-change-first). -/
def TraceFirstFormula
    {C : Type u₁} {D : Type u₂} {V : Type u₃}
    [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} V]
    [MonoidalCategory C] [MonoidalCategory D] [MonoidalCategory V]
    (LC : ObjectProperty C) (LD : ObjectProperty D) (LV : ObjectProperty V)
    (F : C ⥤ D) (P : D ⥤ C) (U₁ U₂ : D ⥤ V) (Q₁ Q₂ : V ⥤ D)
    (a : F ⊣ P) (a₁ : U₁ ⊣ Q₁) (a₂ : U₂ ⊣ Q₂)
    (s : F ⋙ U₂ ≅ F ⋙ U₁)
    (unitIso : F.obj (𝟙_ C) ≅ 𝟙_ D)
    (δF : ∀ K M : C, F.obj (K ⊗ M) ⟶ F.obj K ⊗ F.obj M)
    (δ₁ : ∀ K M : D, U₁.obj (K ⊗ M) ⟶ U₁.obj K ⊗ U₁.obj M)
    (δ₂ : ∀ K M : D, U₂.obj (K ⊗ M) ⟶ U₂.obj K ⊗ U₂.obj M)
    (σD : ∀ K M : D, K ⊗ M ≅ M ⊗ K)
    (σV : ∀ K M : V, K ⊗ M ≅ M ⊗ K) (TY : C) : Prop :=
  ∀ H : TraceFirstHypotheses LC LD LV F P U₁ U₂ Q₁ Q₂ s
      (traceAbstractMate a a₁ s.symm) (traceAbstractMate a a₂ s) unitIso
      (traceProjectionFromComparison a δF)
      (traceProjectionFromComparison a₁ δ₁)
      (traceProjectionFromComparison a₂ δ₂) TY,
    (∀ (M N : D) (hM : LD M) (hN : LD N) (m : M ⟶ N),
      Q₂.map ((U₁ ⋙ tensorRight (U₁.obj (F.obj TY))).map m) ≫
          (traceBFromComparisons F P U₁ U₂ Q₂ TY N (s.app TY)
            (@asIso _ _ _ _ _ (H.projectionQ N hN))
            (@asIso _ _ _ _ _ (H.base₂ N hN))
            (σV _ _) (σD _ _)).hom =
        (traceBFromComparisons F P U₁ U₂ Q₂ TY M (s.app TY)
          (@asIso _ _ _ _ _ (H.projectionQ M hM))
          (@asIso _ _ _ _ _ (H.base₂ M hM)) (σV _ _) (σD _ _)).hom ≫
            (P ⋙ F ⋙ tensorRight (F.obj TY)).map m) ∧
    ∀ (N : D) (hN : LD N),
      P.map (traceBFromComparisons F P U₁ U₂ Q₂ TY N (s.app TY)
          (@asIso _ _ _ _ _ (H.projectionQ N hN))
          (@asIso _ _ _ _ _ (H.base₂ N hN)) (σV _ _) (σD _ _)).hom ≫
        traceAbstractCounit F P (P.obj N) (F.obj TY)
          (traceProjectionFromComparison a δF _ _) (H.projectionF _ (H.pushF N hN)) H.t =
      (conjugateIsoEquiv (a.comp a₂) (a.comp a₁) s.symm).hom.app
          (U₁.obj N ⊗ U₁.obj (F.obj TY)) ≫
        P.map (traceAbstractCounit U₁ Q₁ N (U₁.obj (F.obj TY))
          (traceProjectionFromComparison a₁ δ₁ _ _) (H.projectionP N hN) H.t₁)

/-- Canonical tensor comparisons for three fixed functors, with their tensor structures
stored once. This bundle prevents repeated proof abstraction inside concrete derived tensors.
Source: Stacks 07A4; derived-completeness implementation notes
(blueprint: lem-sfb-trace-base-change-first). -/
structure TraceComparisonData
    {C : Type u₁} {D : Type u₂} {V : Type u₃}
    [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} V]
    (F : C ⥤ D) (U₁ U₂ : D ⥤ V) where
  /-- The tensor structure in the source category. -/
  [monoidalC : MonoidalCategory C]
  /-- The tensor structure in the middle category. -/
  [monoidalD : MonoidalCategory D]
  /-- The tensor structure in the final category. -/
  [monoidalV : MonoidalCategory V]
  /-- The specified unit comparison. -/
  unitIso : F.obj (𝟙_ C) ≅ 𝟙_ D
  /-- The tensor comparison for the first functor. -/
  tensorF : ∀ K M : C, F.obj (K ⊗ M) ⟶ F.obj K ⊗ F.obj M
  /-- The tensor comparison for the first branch. -/
  tensorOne : ∀ K M : D, U₁.obj (K ⊗ M) ⟶ U₁.obj K ⊗ U₁.obj M
  /-- The tensor comparison for the second branch. -/
  tensorTwo : ∀ K M : D, U₂.obj (K ⊗ M) ⟶ U₂.obj K ⊗ U₂.obj M
  /-- The specified symmetry in the middle category. -/
  symmetryD : ∀ K M : D, K ⊗ M ≅ M ⊗ K
  /-- The specified symmetry in the final category. -/
  symmetryV : ∀ K M : V, K ⊗ M ≅ M ⊗ K

/-- Tensor compatibility expressed using the stored canonical structures. -/
private def traceDataSquare
    {C : Type u₁} {D : Type u₂} {V : Type u₃}
    [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} V]
    {F : C ⥤ D} {U₁ U₂ : D ⥤ V} (T : TraceComparisonData F U₁ U₂)
    (s : F ⋙ U₂ ≅ F ⋙ U₁) : Prop :=
  letI := T.monoidalC
  letI := T.monoidalD
  letI := T.monoidalV
  ∀ K M : C,
    s.hom.app (K ⊗ M) ≫ U₁.map (T.tensorF K M) ≫
        T.tensorOne (F.obj K) (F.obj M) =
      U₂.map (T.tensorF K M) ≫ T.tensorTwo (F.obj K) (F.obj M) ≫
        (s.hom.app K ⊗ₘ s.hom.app M)

/-- The displayed trace formula using one stored collection of tensor structures and
canonical comparisons. The formula itself is exactly `TraceFirstFormula`.
Source: blueprint first triangle (blueprint: lem-sfb-trace-base-change-first). -/
def traceDataFormula
    {C : Type u₁} {D : Type u₂} {V : Type u₃}
    [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} V]
    {F : C ⥤ D} {U₁ U₂ : D ⥤ V} (T : TraceComparisonData F U₁ U₂)
    (LC : ObjectProperty C) (LD : ObjectProperty D) (LV : ObjectProperty V)
    (P : D ⥤ C) (Q₁ Q₂ : V ⥤ D)
    (a : F ⊣ P) (a₁ : U₁ ⊣ Q₁) (a₂ : U₂ ⊣ Q₂)
    (s : F ⋙ U₂ ≅ F ⋙ U₁) (TY : C) : Prop :=
  letI := T.monoidalC
  letI := T.monoidalD
  letI := T.monoidalV
  TraceFirstFormula LC LD LV F P U₁ U₂ Q₁ Q₂ a a₁ a₂ s
    T.unitIso T.tensorF T.tensorOne T.tensorTwo T.symmetryD T.symmetryV TY

section AbstractTrace
variable {C D V : Type*} [Category C] [Category D] [Category V]
  [MonoidalCategory C] [SymmetricCategory C]
  [MonoidalCategory D] [SymmetricCategory D]
  [MonoidalCategory V] [SymmetricCategory V]
  (LC : ObjectProperty C) (LD : ObjectProperty D) (LV : ObjectProperty V)
  (F : C ⥤ D) (P : D ⥤ C) (U₁ U₂ : D ⥤ V) (Q₁ Q₂ : V ⥤ D)
  [F.Braided] [U₁.Braided] [U₂.Braided]
  (a : F ⊣ P) (a₁ : U₁ ⊣ Q₁) (a₂ : U₂ ⊣ Q₂)
  (s : F ⋙ U₂ ≅ F ⋙ U₁) (TY : C)
  (hs : ∀ K L : C, s.hom.app (K ⊗ L) ≫
    U₁.map (Functor.OplaxMonoidal.δ F K L) ≫
      Functor.OplaxMonoidal.δ U₁ (F.obj K) (F.obj L) =
    U₂.map (Functor.OplaxMonoidal.δ F K L) ≫
      Functor.OplaxMonoidal.δ U₂ (F.obj K) (F.obj L) ≫
        (s.hom.app K ⊗ₘ s.hom.app L))

private theorem projection_nat
    {A B : Type*} [Category A] [Category B]
    [MonoidalCategory A] [SymmetricCategory A]
    [MonoidalCategory B] [SymmetricCategory B]
    {L : A ⥤ B} {R : B ⥤ A} [L.Braided] (adj : L ⊣ R)
    {K K' : A} {N N' : B} (k : K ⟶ K') (n : N ⟶ N') :
    (k ⊗ₘ R.map n) ≫ traceProjectionFromComparison adj
        (Functor.OplaxMonoidal.δ L) K' N' =
      traceProjectionFromComparison adj (Functor.OplaxMonoidal.δ L) K N ≫
        R.map (L.map k ⊗ₘ n) := by
  unfold traceProjectionFromComparison
  erw [fixed_projection_eq, fixed_projection_eq]
  exact ((adj.leftCoefficientProjectionMap_coherence).1 K K' N N' k n).symm

include hs in
set_option backward.isDefEq.respectTransparency false in
private theorem abstract_trace_formula :
    TraceFirstFormula LC LD LV F P U₁ U₂ Q₁ Q₂ a a₁ a₂ s
      (Functor.Monoidal.εIso F).symm (Functor.OplaxMonoidal.δ F)
      (Functor.OplaxMonoidal.δ U₁) (Functor.OplaxMonoidal.δ U₂)
      (fun K M ↦ β_ K M) (fun K M ↦ β_ K M) TY := by
  intro H
  constructor
  · intro M N hM hN m
    simp only [Functor.comp_map]
    change Q₂.map (U₁.map m ▷ _) ≫ _ = _ ≫ (F.map (P.map m) ▷ _)
    simp only [← tensorHom_id]
    apply traceBFromComparisons_naturality
    · simpa only [Functor.map_id, U₂.map_id, id_tensorHom, asIso_hom] using
        projection_nat a₂ (𝟙 (F.obj TY)) (U₁.map m)
    · exact (traceAbstractMate a a₂ s).naturality m
    · exact BraidedCategory.braiding_naturality _ _
    · exact BraidedCategory.braiding_naturality _ _
  · intro N hN
    let T := F.obj TY
    let A := P.obj N
    let K := P.obj T
    let B := traceBFromComparisons F P U₁ U₂ Q₂ TY N (s.app TY)
      (@asIso _ _ _ _ _ (H.projectionQ N hN))
      (@asIso _ _ _ _ _ (H.base₂ N hN)) (β_ _ _) (β_ _ _)
    let πf := traceProjectionFromComparison a (Functor.OplaxMonoidal.δ F) A T
    let κ := conjugateIsoEquiv (a.comp a₂) (a.comp a₁) s.symm
    let j : U₁.obj N ⊗ U₂.obj T ≅ U₁.obj N ⊗ U₁.obj T :=
      tensorIso (Iso.refl _) (s.app TY)
    let lamf := ((a.rightAdjointProjectionMap
      (Functor.OplaxMonoidal.δNatTrans F)).app N).app K
    let πp := traceProjectionFromComparison a₁ (Functor.OplaxMonoidal.δ U₁)
      N (U₂.obj T)
    have := H.projectionF A (H.pushF N hN)
    have := H.projectionP N hN
    have := H.projectionQ N hN
    have := H.base₂ N hN
    apply (cancel_epi (πf ≫ P.map B.inv)).1
    change (πf ≫ P.map B.inv) ≫ (P.map B.hom ≫ _) =
      (πf ≫ P.map B.inv) ≫ (κ.hom.app _ ≫ _)
    have hfact : πf ≫ P.map B.inv ≫ κ.hom.app _ =
        lamf ≫ P.map ((𝟙 N ⊗ₘ (traceAbstractMate a a₁ s.symm).app T) ≫
          πp ≫ Q₁.map j.hom) := by
      rw [show B.inv = _ from B_inverse F P U₁ U₂ Q₂ a₂ TY N (s.app TY)
        (H.projectionQ N hN) (@asIso _ _ _ _ _ (H.base₂ N hN))]
      simp only [P.map_comp, Category.assoc]
      erw [κ.hom.naturality]
      dsimp only [Functor.comp_map]
      rw [← Category.assoc, ← Category.assoc]
      let df : tensor C ⋙ F ⟶ (F.prod F) ⋙ tensor D := {
        app := fun Z ↦ Functor.OplaxMonoidal.δ F Z.1 Z.2
        naturality := fun X Y m ↦ (Functor.OplaxMonoidal.δ_natural F m.1 m.2).symm }
      let d₁ : tensor D ⋙ U₁ ⟶ (U₁.prod U₁) ⋙ tensor V := {
        app := fun Z ↦ Functor.OplaxMonoidal.δ U₁ Z.1 Z.2
        naturality := fun X Y m ↦ (Functor.OplaxMonoidal.δ_natural U₁ m.1 m.2).symm }
      let d₂ : tensor D ⋙ U₂ ⟶ (U₂.prod U₂) ⋙ tensor V := {
        app := fun Z ↦ Functor.OplaxMonoidal.δ U₂ Z.1 Z.2
        naturality := fun X Y m ↦ (Functor.OplaxMonoidal.δ_natural U₂ m.1 m.2).symm }
      have hk := kunneth_factorization a a₁ a₂ (tensor C) (tensor D) (tensor V)
        df d₁ d₂ s
        (fun K L ↦ ?_) N T
      · simpa only [traceProjectionFromComparison, lamf, πf, πp, P.map_comp,
          Adjunction.rightAdjointProjectionMap_app_app, Functor.id_obj,
          Functor.comp_obj, asIso_hom, A, T, K, κ, j, tensorIso_hom,
          Iso.refl_hom,
          curriedTensor_obj_obj, curriedTensor_map_app, ← tensorHom_id,
          Functor.whiskeringLeft₂_obj_obj_obj_obj_obj,
          Functor.OplaxMonoidal.δNatTrans_app_app, df, d₁, d₂, tensor_obj,
          tensor_map, Category.assoc] using
          congrArg (fun z ↦ z ≫ P.map (Q₁.map j.hom)) hk
      · simpa only [df, d₁, d₂, tensor_obj, tensor_map] using hs K L
    simp only [Category.assoc] at hfact ⊢
    rw [← P.map_comp_assoc, B.inv_hom_id, P.map_id, Category.id_comp]
    rw [← Category.assoc (P.map B.inv), ← Category.assoc πf, hfact]
    dsimp only [traceAbstractCounit]
    simp only [Category.assoc, P.map_comp]
    have hnat := projection_nat a₁ (𝟙 N) (s.hom.app TY)
    simp only [U₁.map_id, id_tensorHom] at hnat
    have hnat' : (𝟙 N ⊗ₘ Q₁.map (s.hom.app TY)) ≫
        traceProjectionFromComparison a₁ (Functor.OplaxMonoidal.δ U₁) N (U₁.obj T) =
      πp ≫ Q₁.map j.hom := by
      change _ = πp ≫ Q₁.map (𝟙 _ ⊗ₘ s.hom.app TY)
      simpa only [id_tensorHom, j, tensorIso_hom, Iso.refl_hom, T, πp,
        Functor.comp_obj] using hnat
        -- natural isomorphism components are definitionally their hom components
    rw [← P.map_comp_assoc πp, ← hnat', P.map_comp]
    simp only [Category.assoc]
    rw [← P.map_comp_assoc, ← Category.assoc, IsIso.hom_inv_id, Category.id_comp]
    rw [← P.map_comp_assoc (traceProjectionFromComparison a₁ _ N (U₁.obj T)),
      IsIso.hom_inv_id, P.map_id, Category.id_comp]
    simp only [P.map_comp, Category.assoc]
    simp only [← P.map_comp]
    simp only [tensorHom_comp_tensorHom_assoc, Category.comp_id]
    change _ = lamf ≫ P.map ((𝟙 N ⊗ₘ
      ((traceAbstractMate a a₁ s.symm).app (F.obj TY) ≫
        Q₁.map (s.hom.app TY) ≫ H.t₁)) ≫ (ρ_ N).hom)
    rw [H.trace₁]
    simpa only [← P.map_comp, tensorHom_comp_tensorHom_assoc,
      tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id, Category.assoc,
      Functor.Monoidal.εIso_inv, Iso.symm_hom, lamf] using
      (scalar_evaluation a N K H.t).symm
end AbstractTrace

/-- The canonical derived braiding satisfies the existing derived symmetry law. -/
private theorem canonical_derived_symmetry
    {A : Type u₁} [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [SymmetricCategory A]
    [MonoidalPreadditive A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    (K M : DerivedCategory A) :
    (CategoryTheory.traceCanonicalDerivedBraiding K M).hom ≫
        (CategoryTheory.traceCanonicalDerivedBraiding M K).hom = 𝟙 (K ⊗ M) := by
  exact @SymmetricCategory.symmetry (DerivedCategory A) _ _
    (DerivedCategory.symmetricCategory A) K M

section DerivedTraceAssembly
variable {C : Type u₁} [Category.{u + 1} C] [Abelian C]
  [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C] [SymmetricCategory C]
  [MonoidalPreadditive C] [MonoidalClosed C] [Abelian.HasFunctorialFlatResolution C]
  {D : Type u₂} [Category.{u + 1} D] [Abelian D]
  [IsGrothendieckAbelian.{u + 1} D] [MonoidalCategory D] [SymmetricCategory D]
  [MonoidalPreadditive D] [MonoidalClosed D] [Abelian.HasFunctorialFlatResolution D]
  {V : Type u₃} [Category.{u + 1} V] [Abelian V]
  [IsGrothendieckAbelian.{u + 1} V] [MonoidalCategory V] [SymmetricCategory V]
  [MonoidalPreadditive V] [MonoidalClosed V] [Abelian.HasFunctorialFlatResolution V]
  (LC : ObjectProperty (DerivedCategory C)) (LD : ObjectProperty (DerivedCategory D))
  (LV : ObjectProperty (DerivedCategory V))
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [F.IsLeftAdjoint] [F.PreservesFlat] [F.Monoidal]
  (U₁ U₂ : D ⥤ V)
  [U₁.Additive] [PreservesFiniteLimits U₁] [PreservesFiniteColimits U₁]
  [U₁.IsLeftAdjoint] [U₁.PreservesFlat] [U₁.Monoidal]
  [U₂.Additive] [PreservesFiniteLimits U₂] [PreservesFiniteColimits U₂]
  [U₂.IsLeftAdjoint] [U₂.PreservesFlat] [U₂.Monoidal]
  (P : DerivedCategory D ⥤ DerivedCategory C)
  (Q₁ Q₂ : DerivedCategory V ⥤ DerivedCategory D)
  (a : F.leftDerivedFunctor ⊣ P)
  (a₁ : U₁.leftDerivedFunctor ⊣ Q₁) (a₂ : U₂.leftDerivedFunctor ⊣ Q₂)
  (s : F.leftDerivedFunctor ⋙ U₂.leftDerivedFunctor ≅
    F.leftDerivedFunctor ⋙ U₁.leftDerivedFunctor)
  (TY : DerivedCategory C)

/-- The existing total-derived tensor, degree-zero unit and Koszul comparisons,
constructed while the three abelian categories are abstract. No data is chosen.
Source: Stacks 07A4 (blueprint: lem-sfb-trace-base-change-first). -/
def derivedTraceComparisonData :
    TraceComparisonData F.leftDerivedFunctor U₁.leftDerivedFunctor U₂.leftDerivedFunctor where
  unitIso := F.traceDegreeZeroUnitIso
  tensorF K M := (F.leftDerivedTensorComparison.app K).app M
  tensorOne K M := (U₁.leftDerivedTensorComparison.app K).app M
  tensorTwo K M := (U₂.leftDerivedTensorComparison.app K).app M
  symmetryD := CategoryTheory.traceCanonicalDerivedBraiding
  symmetryV := CategoryTheory.traceCanonicalDerivedBraiding

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

/-- Derive the tensor compatibility of a square before specializing its categories. -/
private theorem derived_square_assembly
    {I : Type*} (L : I → C ⥤ V)
    [∀ i, (L i).Additive] [∀ i, PreservesFiniteLimits (L i)]
    [∀ i, PreservesFiniteColimits (L i)] [∀ i, (L i).IsLeftAdjoint]
    [∀ i, (L i).PreservesFlat] [∀ i, (L i).Monoidal]
    {i j : I} (w : i = j) (e₁ : L i ≅ F ⋙ U₁) (e₂ : L j ≅ F ⋙ U₂)
    [NatTrans.IsMonoidal e₁.hom] [NatTrans.IsMonoidal e₂.hom] :
    traceDataSquare (derivedTraceComparisonData F U₁ U₂)
      (((L j).leftDerivedFunctorNatIso e₂ ≪≫ F.leftDerivedFunctorCompIso U₂).symm ≪≫
        eqToIso (congrArg (fun h ↦ (L h).leftDerivedFunctor) w.symm) ≪≫
          ((L i).leftDerivedFunctorNatIso e₁ ≪≫ F.leftDerivedFunctorCompIso U₁)) := by
  let a : (L i).leftDerivedFunctor ≅ F.leftDerivedFunctor ⋙ U₁.leftDerivedFunctor :=
    (L i).leftDerivedFunctorNatIso e₁ ≪≫ F.leftDerivedFunctorCompIso U₁
  let b : (L j).leftDerivedFunctor ≅ F.leftDerivedFunctor ⋙ U₂.leftDerivedFunctor :=
    (L j).leftDerivedFunctorNatIso e₂ ≪≫ F.leftDerivedFunctorCompIso U₂
  let e : F.leftDerivedFunctor ⋙ U₂.leftDerivedFunctor ≅
      F.leftDerivedFunctor ⋙ U₁.leftDerivedFunctor :=
    b.symm ≪≫ eqToIso (congrArg (fun h ↦ (L h).leftDerivedFunctor) w.symm) ≪≫ a
  change ∀ K M : DerivedCategory C,
    e.hom.app (K ⊗ M) ≫
        U₁.leftDerivedFunctor.map ((F.leftDerivedTensorComparison.app K).app M) ≫
        (U₁.leftDerivedTensorComparison.app (F.leftDerivedFunctor.obj K)).app
          (F.leftDerivedFunctor.obj M) =
      U₂.leftDerivedFunctor.map ((F.leftDerivedTensorComparison.app K).app M) ≫
        (U₂.leftDerivedTensorComparison.app (F.leftDerivedFunctor.obj K)).app
          (F.leftDerivedFunctor.obj M) ≫ (e.hom.app K ⊗ₘ e.hom.app M)
  intro K M
  simpa only [Category.assoc] using
    (tensor_square_family (C := DerivedCategory C) (V := DerivedCategory V)
      (A := F.leftDerivedFunctor ⋙ U₁.leftDerivedFunctor)
      (B := F.leftDerivedFunctor ⋙ U₂.leftDerivedFunctor) (i := i) (j := j)
      (fun h ↦ (L h).leftDerivedFunctor)
      (fun h A B ↦ ((L h).leftDerivedTensorComparison.app A).app B)
      (fun A B ↦ U₁.leftDerivedFunctor.map ((F.leftDerivedTensorComparison.app A).app B) ≫
        (U₁.leftDerivedTensorComparison.app (F.leftDerivedFunctor.obj A)).app
          (F.leftDerivedFunctor.obj B))
      (fun A B ↦ U₂.leftDerivedFunctor.map ((F.leftDerivedTensorComparison.app A).app B) ≫
        (U₂.leftDerivedTensorComparison.app (F.leftDerivedFunctor.obj A)).app
          (F.leftDerivedFunctor.obj B))
      w a b
      (fun A B ↦ Functor.derived_comp_explicit F U₁ (L i) e₁ A B)
      (fun A B ↦ Functor.derived_comp_explicit F U₂ (L j) e₂ A B) K M)

/-- Assemble the canonical derived comparisons before specializing the coefficient categories.
All unit and braiding identifications are checked with ordinary categories still abstract. -/
private theorem derived_trace_assembly
    (hF : ∀ K M : C, Functor.LaxMonoidal.μ F K M ≫ F.map (β_ K M).hom =
      (β_ (F.obj K) (F.obj M)).hom ≫ Functor.LaxMonoidal.μ F M K)
    (h₁ : ∀ K M : D, Functor.LaxMonoidal.μ U₁ K M ≫ U₁.map (β_ K M).hom =
      (β_ (U₁.obj K) (U₁.obj M)).hom ≫ Functor.LaxMonoidal.μ U₁ M K)
    (h₂ : ∀ K M : D, Functor.LaxMonoidal.μ U₂ K M ≫ U₂.map (β_ K M).hom =
      (β_ (U₂.obj K) (U₂.obj M)).hom ≫ Functor.LaxMonoidal.μ U₂ M K)
    (hs : traceDataSquare (derivedTraceComparisonData F U₁ U₂) s) :
    traceDataFormula (derivedTraceComparisonData F U₁ U₂)
      LC LD LV P Q₁ Q₂ a a₁ a₂ s TY := by
  change TraceFirstFormula LC LD LV F.leftDerivedFunctor P
      U₁.leftDerivedFunctor U₂.leftDerivedFunctor Q₁ Q₂ a a₁ a₂ s
      F.traceDegreeZeroUnitIso
      (fun K M ↦ (F.leftDerivedTensorComparison.app K).app M)
      (fun K M ↦ (U₁.leftDerivedTensorComparison.app K).app M)
      (fun K M ↦ (U₂.leftDerivedTensorComparison.app K).app M)
      (fun K M ↦ CategoryTheory.traceCanonicalDerivedBraiding K M)
      (fun K M ↦ CategoryTheory.traceCanonicalDerivedBraiding K M) TY
  change ∀ K M : DerivedCategory C,
      s.hom.app (K ⊗ M) ≫
          U₁.leftDerivedFunctor.map ((F.leftDerivedTensorComparison.app K).app M) ≫
          (U₁.leftDerivedTensorComparison.app (F.leftDerivedFunctor.obj K)).app
            (F.leftDerivedFunctor.obj M) =
        U₂.leftDerivedFunctor.map ((F.leftDerivedTensorComparison.app K).app M) ≫
          (U₂.leftDerivedTensorComparison.app (F.leftDerivedFunctor.obj K)).app
            (F.leftDerivedFunctor.obj M) ≫ (s.hom.app K ⊗ₘ s.hom.app M) at hs
  let : BraidedCategory (DerivedCategory C) := DerivedCategory.braidedCategory' C
  let : SymmetricCategory (DerivedCategory C) := {
    toBraidedCategory := DerivedCategory.braidedCategory' C
    symmetry := canonical_derived_symmetry }
  let : BraidedCategory (DerivedCategory D) := DerivedCategory.braidedCategory' D
  let : SymmetricCategory (DerivedCategory D) := {
    toBraidedCategory := DerivedCategory.braidedCategory' D
    symmetry := canonical_derived_symmetry }
  let : BraidedCategory (DerivedCategory V) := DerivedCategory.braidedCategory' V
  let : SymmetricCategory (DerivedCategory V) := {
    toBraidedCategory := DerivedCategory.braidedCategory' V
    symmetry := canonical_derived_symmetry }
  let : F.LaxBraided := { braided := hF }
  let : F.Braided := {}
  let : F.leftDerivedFunctor.Braided := by
    let := F.residueDerivedMonoidal
    refine { braided := ?_ }
    intro K M
    apply CategoryTheory.Functor.generic_derived_braid_lax
    intro A B
    simp only [Functor.map_braiding, Category.assoc, Functor.Monoidal.μ_δ,
      Category.comp_id]
  let : U₁.LaxBraided := { braided := h₁ }
  let : U₁.Braided := {}
  let : U₁.leftDerivedFunctor.Braided := by
    let := U₁.residueDerivedMonoidal
    refine { braided := ?_ }
    intro K M
    apply CategoryTheory.Functor.generic_derived_braid_lax
    intro A B
    simp only [Functor.map_braiding, Category.assoc, Functor.Monoidal.μ_δ,
      Category.comp_id]
  let : U₂.LaxBraided := { braided := h₂ }
  let : U₂.Braided := {}
  let : U₂.leftDerivedFunctor.Braided := by
    let := U₂.residueDerivedMonoidal
    refine { braided := ?_ }
    intro K M
    apply CategoryTheory.Functor.generic_derived_braid_lax
    intro A B
    simp only [Functor.map_braiding, Category.assoc, Functor.Monoidal.μ_δ,
      Category.comp_id]
  have hdF : Functor.OplaxMonoidal.δ F.leftDerivedFunctor =
      fun K M ↦ (F.leftDerivedTensorComparison.app K).app M := rfl
  have hd₁ : Functor.OplaxMonoidal.δ U₁.leftDerivedFunctor =
      fun K M ↦ (U₁.leftDerivedTensorComparison.app K).app M := rfl
  have hd₂ : Functor.OplaxMonoidal.δ U₂.leftDerivedFunctor =
      fun K M ↦ (U₂.leftDerivedTensorComparison.app K).app M := rfl
  have hcD (K M : DerivedCategory D) :
      CategoryTheory.traceCanonicalDerivedBraiding K M = β_ K M := rfl
  have hcV (K M : DerivedCategory V) :
      CategoryTheory.traceCanonicalDerivedBraiding K M = β_ K M := rfl
  have hu := CategoryTheory.Functor.derived_unit_monoidal_explicit F
  refine proof_transport_one
    (fun e ↦ TraceFirstFormula LC LD LV F.leftDerivedFunctor P
        U₁.leftDerivedFunctor U₂.leftDerivedFunctor Q₁ Q₂ a a₁ a₂ s
        e
        (fun K M ↦ (F.leftDerivedTensorComparison.app K).app M)
        (fun K M ↦ (U₁.leftDerivedTensorComparison.app K).app M)
        (fun K M ↦ (U₂.leftDerivedTensorComparison.app K).app M)
        (fun K M ↦ CategoryTheory.traceCanonicalDerivedBraiding K M)
        (fun K M ↦ CategoryTheory.traceCanonicalDerivedBraiding K M) TY) hu ?_
  have hs' : ∀ K M : DerivedCategory C,
      s.hom.app (K ⊗ M) ≫
          U₁.leftDerivedFunctor.map (Functor.OplaxMonoidal.δ F.leftDerivedFunctor K M) ≫
          Functor.OplaxMonoidal.δ U₁.leftDerivedFunctor
            (F.leftDerivedFunctor.obj K) (F.leftDerivedFunctor.obj M) =
        U₂.leftDerivedFunctor.map (Functor.OplaxMonoidal.δ F.leftDerivedFunctor K M) ≫
          Functor.OplaxMonoidal.δ U₂.leftDerivedFunctor
            (F.leftDerivedFunctor.obj K) (F.leftDerivedFunctor.obj M) ≫
          (s.hom.app K ⊗ₘ s.hom.app M) := by
    simpa only [hdF, hd₁, hd₂] using hs
  simpa only [hdF, hd₁, hd₂, hcD, hcV] using
    (abstract_trace_formula LC LD LV
      F.leftDerivedFunctor P U₁.leftDerivedFunctor U₂.leftDerivedFunctor Q₁ Q₂
      a a₁ a₂ s TY hs')
end DerivedTraceAssembly

attribute [local irreducible] TraceFirstFormula

section ModuleTraceAssembly
variable {C : Type u₁} [Category.{u + 1} C] [Abelian C]
  [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C] [SymmetricCategory C]
  [MonoidalPreadditive C] [MonoidalClosed C] [Abelian.HasFunctorialFlatResolution C]
  {D : Type u₂} [Category.{u + 1} D] [Abelian D]
  [IsGrothendieckAbelian.{u + 1} D] [MonoidalCategory D] [SymmetricCategory D]
  [MonoidalPreadditive D] [MonoidalClosed D] [Abelian.HasFunctorialFlatResolution D]
  {V : Type u₃} [Category.{u + 1} V] [Abelian V]
  [IsGrothendieckAbelian.{u + 1} V] [MonoidalCategory V] [SymmetricCategory V]
  [MonoidalPreadditive V] [MonoidalClosed V] [Abelian.HasFunctorialFlatResolution V]
  (RC : C) [MonObj RC] [IsCommMonObj RC]
  (RD : D) [MonObj RD] [IsCommMonObj RD]
  (RV : V) [MonObj RV] [IsCommMonObj RV]
  (LC : ObjectProperty (DerivedCategory (Mod C RC)))
  (LD : ObjectProperty (DerivedCategory (Mod D RD)))
  (LV : ObjectProperty (DerivedCategory (Mod V RV)))
  (F : Mod C RC ⥤ Mod D RD) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [F.IsLeftAdjoint] [F.PreservesFlat] [F.Monoidal]
  (U₁ U₂ : Mod D RD ⥤ Mod V RV)
  [U₁.Additive] [PreservesFiniteLimits U₁] [PreservesFiniteColimits U₁]
  [U₁.IsLeftAdjoint] [U₁.PreservesFlat] [U₁.Monoidal]
  [U₂.Additive] [PreservesFiniteLimits U₂] [PreservesFiniteColimits U₂]
  [U₂.IsLeftAdjoint] [U₂.PreservesFlat] [U₂.Monoidal]
  (P : DerivedCategory (Mod D RD) ⥤ DerivedCategory (Mod C RC))
  (Q₁ Q₂ : DerivedCategory (Mod V RV) ⥤ DerivedCategory (Mod D RD))
  (a : F.leftDerivedFunctor ⊣ P)
  (a₁ : U₁.leftDerivedFunctor ⊣ Q₁) (a₂ : U₂.leftDerivedFunctor ⊣ Q₂)
  (s : F.leftDerivedFunctor ⋙ U₂.leftDerivedFunctor ≅
    F.leftDerivedFunctor ⋙ U₁.leftDerivedFunctor)
  (TY : DerivedCategory (Mod C RC))

/-- The canonical derived comparisons for internal modules, with ambient categories
still abstract. Its fields are exactly those of `derivedTraceComparisonData`.
Source: Stacks 07A4 (blueprint: lem-sfb-trace-base-change-first). -/
def moduleTraceComparisonData :
    TraceComparisonData F.leftDerivedFunctor U₁.leftDerivedFunctor U₂.leftDerivedFunctor :=
  derivedTraceComparisonData F U₁ U₂

/-- Assemble the canonical derived comparisons before specializing the coefficient categories.
All unit and braiding identifications are checked with ordinary categories still abstract. -/
private theorem module_trace_assembly
    (hF : ∀ K M : Mod C RC, Functor.LaxMonoidal.μ F K M ≫ F.map (β_ K M).hom =
      (β_ (F.obj K) (F.obj M)).hom ≫ Functor.LaxMonoidal.μ F M K)
    (h₁ : ∀ K M : Mod D RD, Functor.LaxMonoidal.μ U₁ K M ≫ U₁.map (β_ K M).hom =
      (β_ (U₁.obj K) (U₁.obj M)).hom ≫ Functor.LaxMonoidal.μ U₁ M K)
    (h₂ : ∀ K M : Mod D RD, Functor.LaxMonoidal.μ U₂ K M ≫ U₂.map (β_ K M).hom =
      (β_ (U₂.obj K) (U₂.obj M)).hom ≫ Functor.LaxMonoidal.μ U₂ M K)
    (hs : traceDataSquare (moduleTraceComparisonData RC RD RV F U₁ U₂) s) :
    traceDataFormula
      (moduleTraceComparisonData RC RD RV F U₁ U₂)
      LC LD LV P Q₁ Q₂ a a₁ a₂ s TY := by
  exact derived_trace_assembly LC LD LV F U₁ U₂ P Q₁ Q₂ a a₁ a₂ s TY hF h₁ h₂ hs
end ModuleTraceAssembly

attribute [local irreducible] traceDataFormula






variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- The recorded ambient unbounded internal-module derived category.
Source: blueprint standing setting (blueprint: lem-sfb-trace-base-change-first). -/
abbrev TraceD (Z : Scheme.{u}) :=
  DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z))

/-- Loc(Dbc), using the recorded constant-model constructibility and localizing closure.
Source: blueprint standing setting (blueprint: lem-sfb-trace-base-change-first). -/
@[irreducible]
def TraceLoc (Z : Scheme.{u}) : ObjectProperty (TraceD Λ Z) :=
  CategoryTheory.localizingClosure (constantModelBoundedConstructible Λ Z)

/-- Alias for the total left derived functor of the full module inverse image.
Source: blueprint standing setting (blueprint: lem-sfb-trace-base-change-first). -/
def tracePull {Z B : Scheme.{u}} (h : Z ⟶ B) : TraceD Λ B ⥤ TraceD Λ Z :=
  moduleObjectDerivedPullback Λ h

/-- Alias for the total right derived functor of the full module direct image.
Source: blueprint standing setting (blueprint: lem-sfb-trace-base-change-first). -/
def tracePush {Z B : Scheme.{u}} (h : Z ⟶ B) : TraceD Λ Z ⥤ TraceD Λ B :=
  moduleObjectDerivedPushforward Λ h

/-- The existing canonical adjunction, with its functors named explicitly.
Source: blueprint derived module adjunction (blueprint: lem-sfb-trace-base-change-first). -/
@[irreducible]
def traceAdjunction {Z B : Scheme.{u}} (h : Z ⟶ B) :
    tracePull Λ h ⊣ tracePush Λ h :=
  derivedUpperStarLowerStarAdjunction Λ h

variable {X Y W : Scheme.{u}} (f : X ⟶ Y) (p q : W ⟶ X)

/-- The canonical pullback composition with named functor endpoints.
Source: Stacks 0D6D (blueprint: lem-sfb-trace-base-change-first). -/
def tracePullComp {Z B C : Scheme.{u}} (a : Z ⟶ B) (b : B ⟶ C) :
    tracePull Λ (a ≫ b) ≅ tracePull Λ b ⋙ tracePull Λ a :=
  leftDerivedUpperStarComp Λ a b

/-- The canonical inverse-image square comparison, from the recorded composition maps.
Source: Stacks 07A7 (blueprint: lem-sfb-trace-base-change-first). -/
@[irreducible]
def tracePullSquare (w : p ≫ f = q ≫ f) :
    tracePull Λ f ⋙ tracePull Λ q ≅ tracePull Λ f ⋙ tracePull Λ p :=
  (tracePullComp Λ q f).symm ≪≫
    eqToIso (congrArg (fun h : W ⟶ Y => tracePull Λ h) w.symm) ≪≫
      tracePullComp Λ p f


/-- The recorded canonical comparisons for the three pullbacks, stored in one bundle.
Its fields are the existing derived tensor, degree-zero unit and Koszul symmetry maps.
Source: Stacks 07A4 (blueprint: lem-sfb-trace-base-change-first). -/
def traceNativeComparisonData :
    TraceComparisonData (tracePull Λ f) (tracePull Λ p) (tracePull Λ q) :=
  moduleTraceComparisonData
    (condensedRingObj Λ Y) (condensedRingObj Λ X) (condensedRingObj Λ W)
    (upperStar Λ f) (upperStar Λ p) (upperStar Λ q)

section SquareCoherence
attribute [local irreducible] upperStar lowerStar
attribute [local irreducible] CategoryTheory.Functor.rightDerivedFunctor
attribute [local irreducible] Mod.monoidalCategoryStruct
private theorem trace_square_tensor (w : p ≫ f = q ≫ f) :
    traceDataSquare (traceNativeComparisonData Λ f p q) (tracePullSquare Λ f p q w) := by
  let := upper_comp_monoidal Λ p f
  let := upper_comp_monoidal Λ q f
  unfold tracePullSquare
  exact derived_square_assembly
    (upperStar Λ f) (upperStar Λ p) (upperStar Λ q)
    (fun h : W ⟶ Y ↦ upperStar Λ h) w
    (upperStarComp Λ p f) (upperStarComp Λ q f)
end SquareCoherence

/-- The base twist R_Y(1)[2], its recorded integral line placed in degree zero.
Source: sk-def-sp-tate-twist (blueprint: lem-sfb-trace-base-change-first). -/
@[irreducible]
def traceTate (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (Z : Scheme.{u}) : TraceD (Profinite.padicIntegersRingObj ℓ E.1) Z :=
  ((DerivedCategory.singleFunctor _ 0).obj (spIntegralTwist Z ℓ E)) ⟦(2 : ℤ)⟧


/-- The exact formula with all data fixed by the canonical internal-module operations.
The monoidal structures occur only in this proposition's body, avoiding the repeated
proof-irrelevance descent described in DerivedCategory/Complete/Defs.lean.
Source: blueprint first triangle (blueprint: lem-sfb-trace-base-change-first). -/
def TraceFirstAssertion {X Y W : Scheme.{u}} (f : X ⟶ Y) (p q : W ⟶ X)
    (sq : ChosenCartesianSquare p q f f) (TY : TraceD Λ Y) : Prop :=
  traceDataFormula (traceNativeComparisonData Λ f p q)
    (TraceLoc Λ Y) (TraceLoc Λ X) (TraceLoc Λ W)
    (tracePush Λ f) (tracePush Λ p) (tracePush Λ q)
    (traceAdjunction Λ f) (traceAdjunction Λ p) (traceAdjunction Λ q)
    (tracePullSquare Λ f p q sq.w) TY

section ConcreteTrace
attribute [local irreducible] upperStar lowerStar
attribute [local irreducible] CategoryTheory.Functor.rightDerivedFunctor
attribute [local irreducible] Mod.monoidalCategoryStruct
private theorem concrete_trace_formula (sq : ChosenCartesianSquare p q f f)
    (TY : TraceD Λ Y) : TraceFirstAssertion Λ f p q sq TY := by
  unfold TraceFirstAssertion traceNativeComparisonData
  exact module_trace_assembly
    (condensedRingObj Λ Y) (condensedRingObj Λ X) (condensedRingObj Λ W)
    (TraceLoc Λ Y) (TraceLoc Λ X) (TraceLoc Λ W)
    (upperStar Λ f) (upperStar Λ p) (upperStar Λ q)
    (tracePush Λ f) (tracePush Λ p) (tracePush Λ q)
    (traceAdjunction Λ f) (traceAdjunction Λ p) (traceAdjunction Λ q)
    (tracePullSquare Λ f p q sq.w) TY
    (ordinary_upperStar_braiding Λ f) (ordinary_upperStar_braiding Λ p)
    (ordinary_upperStar_braiding Λ q) (trace_square_tensor Λ f p q sq.w)
end ConcreteTrace

/-- Trace/base-change rearrangement before the first triangle, over O_E.
Source: blueprint main-20261015, sk-thm-int-restriction-line.proof.md, (1)
(blueprint: lem-sfb-trace-base-change-first).

Proof:
1. Identify the normalized ordinary tensor structure with the canonical strong
monoidal pullback and prove preservation of flat modules. Its derived structure
has the specified tensor and degree-zero unit comparisons and Koszul braiding.
2. Check ordinary pullback composition after the balanced-tensor quotient and
transport this compatibility to the specified derived square.
3. Transpose the two projection/base-change factorizations through the composite
adjunctions. The mate-counit equations and tensor compatibility of the square give
identical transposes, so injectivity of the adjunction bijection identifies them.
4. Expand B and cancel its inverse and the invertible projection maps. Naturality
moves the square comparison through projection; trace1 and the scalar projection
unit formula identify the two remaining composites. The same naturality equations
prove naturality of B. Only the displayed maps on Loc(Dbc) are inverted. -/
theorem trace_base_change_first
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    {X Y W : Scheme.{u}}
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))] [W.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    [LocallyOfFiniteType (W ↘ Spec (.of k))] [QuasiCompact (W ↘ Spec (.of k))]
    [IsSeparated (W ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))] [IsProper f]
    (p q : W ⟶ X) [p.IsOver (Spec (.of k))] [q.IsOver (Spec (.of k))]
    (sq : ChosenCartesianSquare p q f f) :
    TraceFirstAssertion (Profinite.padicIntegersRingObj ℓ E.1) f p q sq
      (traceTate ℓ E Y) := by
  exact concrete_trace_formula (Profinite.padicIntegersRingObj ℓ E.1) f p q sq _

end AlgebraicGeometry.ProEtale.CondensedRing
