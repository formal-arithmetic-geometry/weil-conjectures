/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q08
-/
module

public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Sheaf.CategoryTheory.SheafTensor
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import Sheaf.Algebra.Homology.PreservesTotalTensorKFlatQuasiIso
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import Sheaf.CategoryTheory.ConstantRingModuleSheaves
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Sheaf.CategoryTheory.CommutativeSiteDerivedConstantModuleFunctor
public import WeilConjectures.CategoryTheory.Monoidal.DerivedBraided
public import WeilConjectures.Algebra.Homology.HomotopyCategory.Braided
public import WeilConjectures.Algebra.Homology.Monoidal.MapHomologicalComplex
public import WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory
public import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import Sheaf.CategoryTheory.RingedSiteGrothendieckCoefficientUniverse
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Monoidal.RestrictScalarsBraided
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Braided.Basic
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.NaturalTransformation
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.ChangeOfRings
import all Sheaf.SecSmoothPurity.CochainInverseComparison
import all Sheaf.Algebra.Homology.RingIsomorphismTensorTransport
import Sheaf.Algebra.Homology.RingedDerivedTensorNative
import Sheaf.CategoryTheory.Monoidal.NormalizedBraidedLocalization
import Mathlib.CategoryTheory.Adjunction.Limits
import all Sheaf.Algebra.Homology.ExactMonoidalEquivalenceTotalKFlat
import Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.CategoryTheory.Abelian.Flat.PreservesFlat
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Unit

/-! # Constant scalar restriction and tensor products

Source: Stacks Project, Modules on Sites, Tags 03CY and 0GMW, and Cohomology on Sites,
Tags 06YN, 06YP, 06YS, 0G7D, 06YT and 06YU
(blueprint: lem-sfb-constant-scalar-restriction-tensor).

The coefficient-sized small site implements the size convention. The restriction is the
existing literal restriction along the constant commutative-ring sheafification unit.

## Main statements

* `ordinary_exists`: normalized ordinary symmetric monoidal equivalence.
* `total_symmetry`: coherence of the existing canonical signed-total comparison.
* `flat_iff`, `kflat_iff`: preservation and reflection of the two flatness conditions.
* `derived_comparison`: the normalized coherent comparison on unbounded derived tensors.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u v wR wB dU dV dW

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace CategoryTheory.ConstantScalarRestriction

private theorem rightFlat_iff {D : Type dU} [Category.{dV} D]
    [MonoidalCategory D] [BraidedCategory D] (M : D) :
    ObjectProperty.flat M ↔ exactFunctor D D (tensorRight M) := by
  refine ⟨fun h ↦ h.2, fun h ↦ ⟨?_, h⟩⟩
  exact (exactFunctor D D).prop_of_iso (BraidedCategory.tensorLeftIsoTensorRight M).symm h

private theorem flat_equivalence {D : Type dU} {E : Type u}
    [Category.{dV} D] [Category.{v} E] [MonoidalCategory D] [MonoidalCategory E]
    (F : D ⥤ E) [F.Monoidal] [F.IsEquivalence] (M : D) :
    ObjectProperty.flat M ↔ ObjectProperty.flat (F.obj M) := by
  let : F.PreservesFlat := F.preservesFlat_of_isEquivalence
  let : F.asEquivalence.functor.Monoidal := inferInstanceAs F.Monoidal
  let : F.inv.Monoidal := F.asEquivalence.inverseMonoidal
  let : F.inv.PreservesFlat := F.inv.preservesFlat_of_isEquivalence
  refine ⟨Functor.PreservesFlat.flat_obj, fun h ↦ ?_⟩
  exact ObjectProperty.prop_of_iso _ (F.asEquivalence.unitIso.app M).symm
    (Functor.PreservesFlat.flat_obj (F := F.inv) h)

private theorem flatResolutionTransport
    {D : Type*} {E : Type*} [Category* D] [Category* E]
    [Abelian D] [Abelian E] [MonoidalCategory D] [MonoidalCategory E]
    (F : D ⥤ E) [F.Additive] [F.Monoidal] [F.IsEquivalence]
    [Abelian.HasFunctorialFlatResolution D] :
    Abelian.HasFunctorialFlatResolution E := by
  let e := F.asEquivalence
  obtain ⟨L⟩ := (inferInstance : Abelian.HasFunctorialFlatResolution D)
  refine ⟨{
    F := ObjectProperty.lift _ (e.inverse ⋙ L.F ⋙ ObjectProperty.flat.ι ⋙ F)
      (fun X ↦ (flat_equivalence F _).mp (L.F.obj (e.inverse.obj X)).property)
    π := ?_
    epi_π_app := ?_ }⟩
  · exact { app X := F.map (L.π.app (e.inverse.obj X)) ≫ e.counitIso.hom.app X
            naturality X Y f := by
              change F.map (L.F.map (e.inverse.map f)).hom ≫
                F.map (L.π.app (e.inverse.obj Y)) ≫ e.counitIso.hom.app Y =
                  (F.map (L.π.app (e.inverse.obj X)) ≫ e.counitIso.hom.app X) ≫ f
              have hn := L.π.naturality (e.inverse.map f)
              change (L.F.map (e.inverse.map f)).hom ≫ L.π.app (e.inverse.obj Y) =
                L.π.app (e.inverse.obj X) ≫ e.inverse.map f at hn
              rw [← F.map_comp_assoc, hn, F.map_comp, Category.assoc]
              simpa only [e, Functor.asEquivalence, Functor.comp_map,
                Functor.id_map, Category.assoc] using
                congrArg (F.map (L.π.app (e.inverse.obj X)) ≫ ·)
                  (e.counitIso.hom.naturality f) }
  · intro X
    change Epi (F.map (L.π.app (e.inverse.obj X)) ≫ e.counitIso.hom.app X)
    infer_instance

/-- Cache the canonical signed-total monoidal structure on complexes.
Source: Stacks 06YN (blueprint: lem-sfb-constant-scalar-restriction-tensor). -/
@[instance_reducible]
def complexTensorMemo (D : Type dU) [Category.{dV} D] [Abelian D]
    [HasColimitsOfSize.{0, 0} D] [MonoidalCategory D] [MonoidalClosed D]
    [MonoidalPreadditive D] [BraidedCategory D] :
    MonoidalCategory (CochainComplex D ℤ) := inferInstance

/-- Cache the canonical K-flat localization monoidal structure.
Source: Stacks 06YT (blueprint: lem-sfb-constant-scalar-restriction-tensor). -/
@[instance_reducible]
def derivedTensorMemo (D : Type dU) [Category.{dV} D] [Abelian D]
    [IsGrothendieckAbelian.{dV} D] [HasColimitsOfSize.{0, 0} D]
    [MonoidalCategory D] [MonoidalClosed D] [MonoidalPreadditive D] [BraidedCategory D]
    [Abelian.HasFunctorialFlatResolution D] [HasDerivedCategory.{dW} D] :
    MonoidalCategory (DerivedCategory D) := inferInstance

attribute [local instance] complexTensorMemo derivedTensorMemo

/-- Koszul symmetry compatibility for a termwise monoidal functor, expressed once
with abstract coefficient-category structures.
Source: Stacks 06YL (blueprint: lem-sfb-constant-scalar-restriction-tensor). -/
def ComplexSymmetryCompatibility
    (D : Type dU) (E : Type u) [Category.{dV} D] [Category.{v} E]
    [Abelian D] [Abelian E]
    [HasColimitsOfSize.{0, 0} D] [HasColimitsOfSize.{0, 0} E]
    [MonoidalCategory D] [MonoidalCategory E]
    [MonoidalClosed D] [MonoidalClosed E]
    [MonoidalPreadditive D] [MonoidalPreadditive E]
    [BraidedCategory D] [BraidedCategory E]
    (G : D ⥤ E) [G.Additive] [G.IsEquivalence] [G.Monoidal] : Prop :=
  ∃ h : (G.mapHomologicalComplex (.up ℤ)).Braided,
    h.toMonoidal = (inferInstance : (G.mapHomologicalComplex (.up ℤ)).Monoidal)

/-- The acyclic test and both quasi-isomorphism tests for the termwise image of a
complex, formulated once over abstract coefficient categories.
Source: Stacks 06YN and 06YP (blueprint: lem-sfb-constant-scalar-restriction-tensor). -/
def KFlatComparison
    (D : Type dU) (E : Type u) [Category.{dV} D] [Category.{v} E]
    [Abelian D] [Abelian E] [MonoidalCategory D] [MonoidalCategory E]
    [MonoidalPreadditive D] [MonoidalPreadditive E]
    [HasCountableCoproducts D] [HasCountableCoproducts E]
    (G : D ⥤ E) [G.Additive] (κ : CochainComplex D ℤ → Prop)
    (P : CochainComplex D ℤ) : Prop :=
  (κ P ↔ ∀ A : CochainComplex E ℤ, A.Acyclic →
    (HomologicalComplex.tensorObj A ((G.mapHomologicalComplex (.up ℤ)).obj P)).Acyclic) ∧
  (κ P ↔ P.IsKFlatForTotalTensor) ∧
  (κ P ↔ CochainComplex.IsKFlatForTotalTensor
    ((G.mapHomologicalComplex (.up ℤ)).obj P))

private theorem abstract_kflat_comparison
    {D : Type dU} {E : Type u} [Category.{dV} D] [Category.{v} E]
    [Abelian D] [Abelian E] [MonoidalCategory D] [MonoidalCategory E]
    [MonoidalPreadditive D] [MonoidalPreadditive E]
    [SymmetricCategory D] [SymmetricCategory E]
    [HasCountableCoproducts D] [HasCountableCoproducts E]
    [TensorPreservesCountableCoproducts D] [TensorPreservesCountableCoproducts E]
    (F : D ⥤ E) [F.Additive] [F.Braided] [F.IsEquivalence]
    (P : CochainComplex D ℤ) :
    KFlatComparison D E F
      (fun Q ↦ ∀ A : CochainComplex D ℤ, A.Acyclic → (A ⊗ Q).Acyclic) P := by
  let e := F.asEquivalence
  let : e.functor.Monoidal := by
    dsimp only [e, Functor.asEquivalence]
    infer_instance
  let : e.functor.Additive := by
    dsimp only [e, Functor.asEquivalence]
    infer_instance
  have hsrc := Equivalence.acyclic_tensor_swap P
  have hmap := Equivalence.acyclic_tensor_map_iff e P
  have htgt := Equivalence.acyclic_tensor_swap
    ((F.mapHomologicalComplex (.up ℤ)).obj P)
  have hs := hsrc.symm.trans (Equivalence.acyclic_tensor_iff_kFlat P)
  have ht := hsrc.symm.trans (hmap.trans htgt)
  exact ⟨ht, hs, ht.trans (htgt.symm.trans
    (Equivalence.acyclic_tensor_iff_kFlat _))⟩

/-- The canonical localization tensor square on every pair of K-flat representatives.
Source: Stacks 06YU (blueprint: lem-sfb-constant-scalar-restriction-tensor). -/
def derivedTensorCompatibility
    (D : Type dU) (E : Type u) [Category.{dV} D] [Category.{v} E]
    [Abelian D] [Abelian E] [IsGrothendieckAbelian.{dV} D]
    [IsGrothendieckAbelian.{v} E]
    [HasColimitsOfSize.{0, 0} D] [HasColimitsOfSize.{0, 0} E]
    [MonoidalCategory D] [MonoidalCategory E]
    [MonoidalClosed D] [MonoidalClosed E]
    [MonoidalPreadditive D] [MonoidalPreadditive E]
    [BraidedCategory D] [BraidedCategory E]
    [Abelian.HasFunctorialFlatResolution D] [Abelian.HasFunctorialFlatResolution E]
    [HasDerivedCategory.{wR} D] [HasDerivedCategory.{wB} E]
    (G : D ⥤ E) [G.Additive] [G.IsEquivalence] [G.Monoidal]
    (κ : CochainComplex D ℤ → Prop)
    (monoidal : G.mapDerivedCategory.Monoidal) : Prop :=
  ∀ (P Q : CochainComplex D ℤ), κ P → κ Q →
    @Functor.OplaxMonoidal.δ _ _ _ _ _ _ G.mapDerivedCategory
        monoidal.toOplaxMonoidal (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q) ≫
      (G.mapDerivedCategoryFactors.hom.app P ⊗ₘ G.mapDerivedCategoryFactors.hom.app Q) ≫
      Functor.LaxMonoidal.μ DerivedCategory.Q
        ((G.mapHomologicalComplex (.up ℤ)).obj P)
        ((G.mapHomologicalComplex (.up ℤ)).obj Q) =
    G.mapDerivedCategory.map (Functor.LaxMonoidal.μ DerivedCategory.Q P Q) ≫
      G.mapDerivedCategoryFactors.hom.app (P ⊗ Q) ≫
      DerivedCategory.Q.map (Functor.mapCochainComplexμIso G P Q).inv

/-- Compatibility of the derived tensor comparison with the canonical Koszul braiding.
Source: Stacks 06YU (blueprint: lem-sfb-constant-scalar-restriction-tensor). -/
def derivedSymmetryCompatibility
    (D : Type dU) (E : Type u) [Category.{dV} D] [Category.{v} E]
    [Abelian D] [Abelian E] [IsGrothendieckAbelian.{dV} D]
    [IsGrothendieckAbelian.{v} E]
    [HasColimitsOfSize.{0, 0} D] [HasColimitsOfSize.{0, 0} E]
    [MonoidalCategory D] [MonoidalCategory E]
    [MonoidalClosed D] [MonoidalClosed E]
    [MonoidalPreadditive D] [MonoidalPreadditive E]
    [BraidedCategory D] [BraidedCategory E]
    [Abelian.HasFunctorialFlatResolution D] [Abelian.HasFunctorialFlatResolution E]
    [HasDerivedCategory.{wR} D] [HasDerivedCategory.{wB} E]
    (G : D ⥤ E) [G.Additive] [G.IsEquivalence]
    (monoidal : G.mapDerivedCategory.Monoidal) : Prop :=
  ∀ (X Y : DerivedCategory D),
    G.mapDerivedCategory.map
        (DerivedMonoidal.braiding' (DerivedCategory.Qh (C := D))
          (HomotopyCategory.quasiIso D (.up ℤ)) X Y).hom ≫
        @Functor.OplaxMonoidal.δ _ _ _ _ _ _ G.mapDerivedCategory
          monoidal.toOplaxMonoidal Y X =
      @Functor.OplaxMonoidal.δ _ _ _ _ _ _ G.mapDerivedCategory
          monoidal.toOplaxMonoidal X Y ≫
        (DerivedMonoidal.braiding' (DerivedCategory.Qh (C := E))
          (HomotopyCategory.quasiIso E (.up ℤ))
          (G.mapDerivedCategory.obj X) (G.mapDerivedCategory.obj Y)).hom

/-- The degree-zero regular-unit normalization of the derived tensor comparison.
Source: Stacks 06YU (blueprint: lem-sfb-constant-scalar-restriction-tensor). -/
def derivedUnitCompatibility
    (D : Type dU) (E : Type u) [Category.{dV} D] [Category.{v} E]
    [Abelian D] [Abelian E] [IsGrothendieckAbelian.{dV} D]
    [IsGrothendieckAbelian.{v} E]
    [HasColimitsOfSize.{0, 0} D] [HasColimitsOfSize.{0, 0} E]
    [MonoidalCategory D] [MonoidalCategory E]
    [MonoidalClosed D] [MonoidalClosed E]
    [MonoidalPreadditive D] [MonoidalPreadditive E]
    [BraidedCategory D] [BraidedCategory E]
    [Abelian.HasFunctorialFlatResolution D] [Abelian.HasFunctorialFlatResolution E]
    [HasDerivedCategory.{wR} D] [HasDerivedCategory.{wB} E]
    (G : D ⥤ E) [G.Additive] [G.IsEquivalence] [G.Monoidal]
    (monoidal : G.mapDerivedCategory.Monoidal) : Prop :=
  @Functor.LaxMonoidal.ε _ _ _ _ _ _ G.mapDerivedCategory
        monoidal.toLaxMonoidal ≫
      G.mapDerivedCategory.map (Functor.LaxMonoidal.ε DerivedCategory.Q) ≫
      G.mapDerivedCategoryFactors.hom.app (𝟙_ _) =
    Functor.LaxMonoidal.ε DerivedCategory.Q ≫
      DerivedCategory.Q.map (Functor.LaxMonoidal.ε (G.mapHomologicalComplex (.up ℤ)))

/-- The monoidal structure and its specified tensor, symmetry and unit laws.
The subtype stores the same comparison data using the existing logical constructors.
Source: Stacks 06YU (blueprint: lem-sfb-constant-scalar-restriction-tensor). -/
def DerivedComparisonData
    (D : Type dU) (E : Type u) [Category.{dV} D] [Category.{v} E]
    [Abelian D] [Abelian E] [IsGrothendieckAbelian.{dV} D]
    [IsGrothendieckAbelian.{v} E]
    [HasColimitsOfSize.{0, 0} D] [HasColimitsOfSize.{0, 0} E]
    [MonoidalCategory D] [MonoidalCategory E]
    [MonoidalClosed D] [MonoidalClosed E]
    [MonoidalPreadditive D] [MonoidalPreadditive E]
    [BraidedCategory D] [BraidedCategory E]
    [Abelian.HasFunctorialFlatResolution D] [Abelian.HasFunctorialFlatResolution E]
    [HasDerivedCategory.{wR} D] [HasDerivedCategory.{wB} E]
    (G : D ⥤ E) [G.Additive] [G.IsEquivalence] [G.Monoidal]
    (κ : CochainComplex D ℤ → Prop) :=
  { monoidal : G.mapDerivedCategory.Monoidal //
    derivedTensorCompatibility D E G κ monoidal ∧
    derivedSymmetryCompatibility D E G monoidal ∧
    derivedUnitCompatibility D E G monoidal }

section DerivedComparisonProof

@[instance_reducible]
private def complexTensorStructMemo (D : Type dU) [Category.{dV} D] [Abelian D]
    [HasColimitsOfSize.{0, 0} D] [MonoidalCategory D] [MonoidalClosed D]
    [MonoidalPreadditive D] [BraidedCategory D] :
    MonoidalCategoryStruct (CochainComplex D ℤ) :=
  (complexTensorMemo D).toMonoidalCategoryStruct

@[instance_reducible]
private def derivedTensorStructMemo (D : Type dU) [Category.{dV} D] [Abelian D]
    [IsGrothendieckAbelian.{dV} D] [HasColimitsOfSize.{0, 0} D]
    [MonoidalCategory D] [MonoidalClosed D] [MonoidalPreadditive D] [BraidedCategory D]
    [Abelian.HasFunctorialFlatResolution D] [HasDerivedCategory.{dW} D] :
    MonoidalCategoryStruct (DerivedCategory D) :=
  (derivedTensorMemo D).toMonoidalCategoryStruct

attribute [local instance] complexTensorStructMemo derivedTensorStructMemo

set_option backward.isDefEq.respectTransparency true
open CategoryTheory.Category CategoryTheory.Functor CategoryTheory.Functor.LaxMonoidal
open CategoryTheory.Functor.OplaxMonoidal

private theorem monoidalSquare_tensor
    {A B D E : Type*} [Category* A] [Category* B] [Category* D] [Category* E]
    [MonoidalCategory A] [MonoidalCategory B] [MonoidalCategory D] [MonoidalCategory E]
    (Q : A ⥤ D) (L : B ⥤ E) (F : A ⥤ B) (G : D ⥤ E)
    [Q.LaxMonoidal] [L.LaxMonoidal] [F.Monoidal] [G.Monoidal]
    (e : Q ⋙ G ≅ F ⋙ L) [NatTrans.IsMonoidal e.hom] (X Y : A) :
    δ G (Q.obj X) (Q.obj Y) ≫ (e.hom.app X ⊗ₘ e.hom.app Y) ≫
        μ L (F.obj X) (F.obj Y) =
      G.map (μ Q X Y) ≫ e.hom.app (X ⊗ Y) ≫ L.map (δ F X Y) := by
  have h := NatTrans.IsMonoidal.tensor (τ := e.hom) X Y
  simp only [Functor.LaxMonoidal.comp_μ, assoc] at h
  apply (cancel_mono (L.map (μ F X Y))).1
  simp only [assoc, ← L.map_comp, Functor.Monoidal.δ_μ, Functor.map_id]
  rw [← h, Functor.Monoidal.δ_μ_assoc]
  exact congrArg (fun k ↦ G.map (μ Q X Y) ≫ k)
    (Category.comp_id (e.hom.app (X ⊗ Y))).symm

universe uD vD wD uE vE wE
variable {D : Type uD} [Category.{vD} D] [Abelian D] [IsGrothendieckAbelian.{vD} D]
  [MonoidalCategory D] [SymmetricCategory D] [MonoidalClosed D] [MonoidalPreadditive D]
  [Abelian.HasFunctorialFlatResolution D] [HasDerivedCategory.{wD} D]
  [HasColimitsOfSize.{0, 0} D]
  {E : Type uE} [Category.{vE} E] [Abelian E] [IsGrothendieckAbelian.{vE} E]
  [MonoidalCategory E] [SymmetricCategory E] [MonoidalClosed E] [MonoidalPreadditive E]
  [Abelian.HasFunctorialFlatResolution E] [HasDerivedCategory.{wE} E]
  [HasColimitsOfSize.{0, 0} E]

private theorem nativeTensorIso (P Q : CochainComplex D ℤ)
    (hQ : Q.IsKFlatForTotalTensor) : IsIso (μ DerivedCategory.Q P Q) := by
  have : IsIso (μ DerivedCategory.Qh
      ((HomotopyCategory.quotient D (.up ℤ)).obj P)
      ((HomotopyCategory.quotient D (.up ℤ)).obj Q)) :=
    DerivedMonoidal.isIso_counit_app_app_of_kFlat_right DerivedCategory.Qh
      (HomotopyCategory.quasiIso D (.up ℤ)) _ _
      ((HomotopyCategory.kFlat_quotient_obj_iff Q).2 hQ)
  change IsIso ((_ ⊗ₘ _) ≫
    (μ DerivedCategory.Qh _ _ ≫ DerivedCategory.Qh.map _) ≫ _)
  infer_instance

private theorem nativeUnitIso : IsIso (ε (DerivedCategory.Q (C := D))) := by
  exact RingedDerivedNative.localization_isIso_ε

omit [HasDerivedCategory D] in
private theorem nativeDerivability :
    (HomologicalComplex.quasiIso D (.up ℤ)).localizerMorphismKFlat.IsLeftDerivabilityStructure := by
  have : HasExactColimitsOfShape ℤ D := by
    have := AB5OfSize_of_univLE.{0, 0, vD, vD} D
    infer_instance
  have (X : D) : PreservesColimitsOfShape ℤ ((curriedTensor D).flip.obj X) :=
    preservesColimitsOfShape_of_natIso (F := tensorLeft X)
      (NatIso.ofComponents (fun Y ↦ β_ X Y) (by intros; simp [curriedTensor]))
  infer_instance

private theorem abstract_derived_comparison (F : D ⥤ E)
    [F.Additive] [F.Braided] [F.IsEquivalence]
    (κ : CochainComplex D ℤ → Prop)
    (hF : ∀ P : CochainComplex D ℤ, P.IsKFlatForTotalTensor →
      CochainComplex.IsKFlatForTotalTensor ((F.mapHomologicalComplex (.up ℤ)).obj P)) :
    Nonempty (DerivedComparisonData D E F κ) := by
  let Fc := F.mapHomologicalComplex (.up ℤ)
  let G := F.mapDerivedCategory
  let Q : CochainComplex D ℤ ⥤ DerivedCategory D := DerivedCategory.Q
  let L : CochainComplex E ℤ ⥤ DerivedCategory E := DerivedCategory.Q
  let W := HomologicalComplex.quasiIso D (.up ℤ)
  have : W.localizerMorphismKFlat.IsLeftDerivabilityStructure := nativeDerivability
  have : IsIso (ε Q) := nativeUnitIso
  have : IsIso (ε L) := nativeUnitIso
  have hmodels (X : DerivedCategory D) : ∃ a, W.kFlat a ∧ Nonempty (Q.obj a ≅ X) := by
    let R : W.localizerMorphismKFlat.LeftResolution (Q.objPreimage X) := Classical.arbitrary _
    exact ⟨R.X₁.obj, R.X₁.property,
      ⟨Localization.isoOfHom Q W R.w R.hw ≪≫ Q.objObjPreimageIso X⟩⟩
  have hQ (a b : CochainComplex D ℤ) (hb : W.kFlat b) : IsIso (μ Q a b) :=
    nativeTensorIso a b hb
  have hL (x : CochainComplex E ℤ) (b : CochainComplex D ℤ) (hb : W.kFlat b) :
      IsIso (μ L x (Fc.obj b)) := nativeTensorIso x _ (hF b hb)
  let : SymmetricCategory (DerivedCategory D) := RingedDerivedNative.derivedSymmetric
  let : SymmetricCategory (DerivedCategory E) := RingedDerivedNative.derivedSymmetric
  let : Q.LaxBraided := RingedDerivedNative.localizationLaxBraided
  let : L.LaxBraided := RingedDerivedNative.localizationLaxBraided
  let : Fc.Braided := Functor.OplaxMonoidal.cochainBraided F
  obtain ⟨bg, hm⟩ := CategoryTheory.normalizedBraidedLocalization Q L Fc G
    F.mapDerivedCategoryFactors W hmodels hQ hL
  let m := bg.toMonoidal
  let : G.Monoidal := m
  have : NatTrans.IsMonoidal F.mapDerivedCategoryFactors.hom := hm
  have hn (P Q : CochainComplex D ℤ) :
      δ G (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q) ≫
        (F.mapDerivedCategoryFactors.hom.app P ⊗ₘ F.mapDerivedCategoryFactors.hom.app Q) ≫
        μ DerivedCategory.Q (Fc.obj P) (Fc.obj Q) =
      G.map (μ DerivedCategory.Q P Q) ≫ F.mapDerivedCategoryFactors.hom.app (P ⊗ Q) ≫
        DerivedCategory.Q.map (F.mapCochainComplexμIso P Q).inv :=
    monoidalSquare_tensor _ _ _ _ F.mapDerivedCategoryFactors P Q
  refine Nonempty.intro (Subtype.mk m ?_)
  refine And.intro ?_ (And.intro ?_ ?_)
  · intro P Q _ _
    exact hn P Q
  · intro X Y
    change G.map (β_ X Y).hom ≫ δ G Y X =
      δ G X Y ≫ (β_ (G.obj X) (G.obj Y)).hom
    apply (cancel_epi (μ G X Y)).1
    rw [← assoc, bg.braided, assoc, Functor.Monoidal.μ_δ,
      comp_id, Functor.Monoidal.μ_δ_assoc]
  · dsimp only [derivedUnitCompatibility]
    change ε G ≫ G.map (ε DerivedCategory.Q) ≫
      F.mapDerivedCategoryFactors.hom.app (𝟙_ _) =
        ε DerivedCategory.Q ≫ DerivedCategory.Q.map (ε Fc)
    simpa only [Functor.LaxMonoidal.comp_ε, assoc] using
      NatTrans.IsMonoidal.unit (τ := F.mapDerivedCategoryFactors.hom)

end DerivedComparisonProof

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  (B : Type (max u v)) [CommRing B]

/-- The specified constant commutative ring sheaf, not an arbitrary coefficient ring.
Source: Stacks 0GMW (blueprint: lem-sfb-constant-scalar-restriction-tensor). -/
def ring := (constantSheaf J CommRingCat.{max u v}).obj (CommRingCat.of B)

/-- The existing ringed-site module category at the constant ring.
Source: Stacks 03CY (blueprint: lem-sfb-constant-scalar-restriction-tensor). -/
abbrev Modules := SheafOfModules.{max u v}
  ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj (ring J B))

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
/-- Exact fixed-coefficient sheafification, transported from the small model of the site.
Source: Stacks 03CY (blueprint: lem-sfb-constant-scalar-restriction-tensor). -/
instance fixedSheafify : HasSheafify J (ModuleCat.{max u v} B) :=
  letI : PreservesFilteredColimitsOfSize.{max u v, max u v}
      (CategoryTheory.forget (ModuleCat.{max u v} B)) :=
    ModuleCat.FilteredColimits.forget_preservesFilteredColimits (R := B)
  letI : HasSheafify ((equivSmallModel.{max u v} C).inverse.inducedTopology J)
      (ModuleCat.{max u v} B) :=
    inferInstance
  hasSheafifyEssentiallySmallSite J (ModuleCat.{max u v} B)

/-- The existing fixed-coefficient sheaf category.
Source: Stacks 03CY (blueprint: lem-sfb-constant-scalar-restriction-tensor). -/
abbrev Fixed := Sheaf J (ModuleCat.{max u v} B)

/-- Cache the existing abelian structure of module sheaves.
Source: Stacks 03DA (blueprint: lem-sfb-constant-scalar-restriction-tensor). -/
instance ringAbelian : Abelian (Modules J B) := inferInstance

/-- Cache the abelian structure supplied by exact sheafification.
Source: Stacks 03CY (blueprint: lem-sfb-constant-scalar-restriction-tensor). -/
instance fixedAbelian : Abelian (Fixed J B) := inferInstance

/-- Use the additive structure of this same abelian category throughout.
Source: Stacks 03DA (blueprint: lem-sfb-constant-scalar-restriction-tensor). -/
instance ringPreadditive : Preadditive (Modules J B) :=
  (ringAbelian J B).toPreadditive

/-- Use the additive structure of the fixed-coefficient abelian category throughout.
Source: Stacks 03DA (blueprint: lem-sfb-constant-scalar-restriction-tensor). -/
instance fixedPreadditive : Preadditive (Fixed J B) :=
  (fixedAbelian J B).toPreadditive

/-- The canonical additive zero morphisms, used uniformly in complex constructions.
Source: Stacks 03CY (blueprint: lem-sfb-constant-scalar-restriction-tensor). -/
instance ringZeroMorphisms : HasZeroMorphisms (Modules J B) :=
  Preadditive.preadditiveHasZeroMorphisms

/-- The canonical additive zero morphisms on fixed-coefficient module sheaves.
Source: Stacks 03CY (blueprint: lem-sfb-constant-scalar-restriction-tensor). -/
instance fixedZeroMorphisms : HasZeroMorphisms (Fixed J B) :=
  Preadditive.preadditiveHasZeroMorphisms

/-- The recorded restriction, with precisely the action induced by the sheafification unit.
Source: Stacks 03CY (blueprint: lem-sfb-constant-scalar-restriction-tensor). -/
def restriction : Modules J B ⥤ Fixed J B :=
  SheafOfModules.restrictScalars
    ((constantCommuteCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).inv.app
      (CommRingCat.of B)) ⋙ constantRingModuleRestriction J B

/-- Use the recorded sheafified objectwise tensor structure.
Source: Stacks 0GMW (blueprint: lem-sfb-constant-scalar-restriction-tensor). -/
instance fixedMonoidal : MonoidalCategory (Fixed J B) :=
  (sfbSheafTensorStructure (A := ModuleCat.{max u v} B) J).monoidal

/-- Use the symmetry of that same sheafified tensor.
Source: Stacks 0GMW (blueprint: lem-sfb-constant-scalar-restriction-tensor). -/
instance fixedSymmetric : SymmetricCategory (Fixed J B) :=
  (sfbSheafTensorStructure (A := ModuleCat.{max u v} B) J).symmetric

/-- Closedness of the recorded tensor, characterized by its tensor--Hom adjunction.
Source: sk-def-sfb-sheaf-tensor (blueprint: lem-sfb-constant-scalar-restriction-tensor). -/
instance fixedClosed : MonoidalClosed (Fixed J B) :=
  (sfbSheafTensor_properties.{u, v, (max u v) + 1, max u v, 0, 0}
    (A := ModuleCat.{max u v} B) J).2.1.some

/-- Tensoring preserves the coproducts used in the signed total.
Source: sk-def-sfb-sheaf-tensor (blueprint: lem-sfb-constant-scalar-restriction-tensor). -/
instance fixedLeftColimits (M : Fixed J B) :
    PreservesColimitsOfSize.{0, 0} (tensorLeft M) :=
  (sfbSheafTensor_properties.{u, v, (max u v) + 1, max u v, 0, 0}
    (A := ModuleCat.{max u v} B) J).2.2 M |>.1

/-- Tensoring on the other side preserves those coproducts.
Source: sk-def-sfb-sheaf-tensor (blueprint: lem-sfb-constant-scalar-restriction-tensor). -/
instance fixedRightColimits (M : Fixed J B) :
    PreservesColimitsOfSize.{0, 0} (tensorRight M) :=
  (sfbSheafTensor_properties.{u, v, (max u v) + 1, max u v, 0, 0}
    (A := ModuleCat.{max u v} B) J).2.2 M |>.2.1

/-- Cache additivity of the recorded sheaf tensor.
Source: blueprint sk-def-sfb-sheaf-tensor
(blueprint: lem-sfb-constant-scalar-restriction-tensor). -/
instance fixedTensorAdditive : MonoidalPreadditive (Fixed J B) :=
  sfbSheafTensor_monoidalPreadditive

/-- The canonical ringed tensor structure, cached before generator formulas.
Source: Stacks 0GMW (blueprint: lem-sfb-constant-scalar-restriction-tensor). -/
instance ringMonoidal : MonoidalCategory (Modules J B) := inferInstance

/-- Symmetry of the cached ringed tensor structure.
Source: Stacks 0GMW (blueprint: lem-sfb-constant-scalar-restriction-tensor). -/
instance ringSymmetric : SymmetricCategory (Modules J B) := inferInstance

/-- Restriction is additive. Source: Stacks 03CY
(blueprint: lem-sfb-constant-scalar-restriction-tensor).
Proof: the section homomorphisms are unchanged, so sums of maps are unchanged (step 1). -/
@[instance] theorem additive : (restriction J B).Additive := by
  constructor
  intro X Y f g
  ext U x
  rfl

private def restrictCancelIso {R S : Sheaf J RingCat.{max u v}}
    (α : R ⟶ S) (β : S ⟶ R) (h : α ≫ β = 𝟙 R) :
    SheafOfModules.restrictScalars β ⋙ SheafOfModules.restrictScalars α ≅
      𝟭 (SheafOfModules.{max u v} R) := by
  have hU (U : Cᵒᵖ) : (β.hom.app U).hom.comp (α.hom.app U).hom =
      RingHom.id (R.obj.obj U) :=
    congrArg RingCat.Hom.hom (congr_app (congrArg (fun k : R ⟶ R ↦ k.hom) h) U)
  refine NatIso.ofComponents (fun M ↦ (SheafOfModules.fullyFaithfulForget R).preimageIso
    (PresheafOfModules.isoMk (fun U ↦
      (ModuleCat.restrictScalarsComp'App (α.hom.app U).hom (β.hom.app U).hom
        (RingHom.id (R.obj.obj U)) (hU U).symm (M.val.obj U)).symm ≪≫
      (ModuleCat.restrictScalarsId (R.obj.obj U)).app (M.val.obj U)) ?_)) ?_
  · intro U V f
    ext x
    rfl
  · intro M N f
    ext U x
    rfl

/-- Restriction is an equivalence. Source: Stacks 03CY
(blueprint: lem-sfb-constant-scalar-restriction-tensor).
Proof: step 1 uses lem-cbc-constant-ring-module-sheaves. Extend the scalar action locally;
uniqueness on the original abelian sheaf gives the inverse and both inverse identities.
The CommRingCat presentation is identified with RingCat by constantCommuteCompose. -/
@[instance] theorem isEquivalence : (restriction J B).IsEquivalence := by
  obtain ⟨e, he, _, _, _⟩ := (constant_ring_module_sheaves J B).1
  have : (constantRingModuleRestriction J B).IsEquivalence := he ▸ e.isEquivalence_functor
  let c := (constantCommuteCompose J
    (forget₂ CommRingCat.{max u v} RingCat.{max u v})).app (CommRingCat.of B)
  let e' := Equivalence.mk (SheafOfModules.restrictScalars c.inv)
    (SheafOfModules.restrictScalars c.hom)
    (restrictCancelIso J c.hom c.inv c.hom_inv_id).symm
    (restrictCancelIso J c.inv c.hom c.inv_hom_id)
  have : (SheafOfModules.restrictScalars.{max u v} c.inv).IsEquivalence :=
    e'.isEquivalence_functor
  exact inferInstanceAs
    (SheafOfModules.restrictScalars c.inv ⋙ constantRingModuleRestriction J B).IsEquivalence

/-- Restriction is exact for the two abelian categories.
Source: Stacks 03CY and 0038 (blueprint: lem-sfb-constant-scalar-restriction-tensor).
Proof: step 1 applies lem-galois-equivalence-preserves-limits to the equivalence and
its inverse. In particular both preserve kernels and cokernels, hence finite limits
and finite colimits. -/
theorem exact : exactFunctor _ _ (restriction J B) := by
  exact ⟨inferInstanceAs (PreservesFiniteLimits (restriction J B)),
    inferInstanceAs (PreservesFiniteColimits (restriction J B))⟩

/-- The local pure tensor in the ordinary ringed-site tensor.
Source: Stacks 0GMW (blueprint: lem-sfb-constant-scalar-restriction-tensor). -/
def ringPure (M N : Modules J B) (U : Cᵒᵖ) (x : M.val.obj U) (y : N.val.obj U) :
    (M ⊗ N).val.obj U :=
  (SheafOfModules.tensorObjIsoSheafification M N).inv.val.app U
    (((PresheafOfModules.sheafificationAdjunction (𝟙 _)).unit.app (M.val ⊗ N.val)).app U
      (x ⊗ₜ[(ring J B).obj.obj U] y))

/-- The local pure tensor in the sheafified objectwise fixed-ring tensor.
Source: Stacks 0GMW (blueprint: lem-sfb-constant-scalar-restriction-tensor). -/
def fixedPure (M N : Fixed J B) (U : Cᵒᵖ) (x : M.obj.obj U) (y : N.obj.obj U) :
    (M ⊗ N).obj.obj U :=
  (sfbSheafTensor_comparison J M N).inv.hom.app U
    ((toSheafify J (M.obj ⊗ N.obj)).app U (x ⊗ₜ[B] y))

/-- Identify the fixed tensor unit with the recorded constant module sheaf.
Source: blueprint sk-def-sfb-sheaf-tensor
(blueprint: lem-sfb-constant-scalar-restriction-tensor). -/
def fixedUnitIso : 𝟙_ (Fixed J B) ≅ (constantSheaf J (ModuleCat B)).obj (ModuleCat.of B B) :=
  eqToIso (sfbSheafTensor_properties.{u, v, (max u v) + 1, max u v, 0, 0}
    (A := ModuleCat.{max u v} B) J).1

/-- The image of a constant scalar in the fixed tensor unit.
Source: Stacks 0GMW (blueprint: lem-sfb-constant-scalar-restriction-tensor). -/
def fixedUnitScalar (U : Cᵒᵖ) (b : B) : (𝟙_ (Fixed J B)).obj.obj U :=
  (fixedUnitIso J B).inv.hom.app U
    ((toSheafify J ((Functor.const Cᵒᵖ).obj (ModuleCat.of B B))).app U b)

/-- The normalized coherent ordinary comparison. Source: Stacks 0GMW
(blueprint: lem-sfb-constant-scalar-restriction-tensor).
The braided monoidal structure includes naturality, associators, both unitors and symmetry.
The generator equations determine its tensorator and unit, hence determine its data uniquely. -/
structure Ordinary where
  braided : (restriction J B).Braided
  tensor_hom : ∀ (M N : Modules J B) (U : Cᵒᵖ) (x : M.val.obj U) (y : N.val.obj U),
    ((@Functor.OplaxMonoidal.δ _ _ _ _ _ _ (restriction J B)
      braided.toMonoidal.toOplaxMonoidal M N).hom.app U) (ringPure J B M N U x y) =
        fixedPure J B ((restriction J B).obj M) ((restriction J B).obj N) U x y
  tensor_inv : ∀ (M N : Modules J B) (U : Cᵒᵖ) (x : M.val.obj U) (y : N.val.obj U),
    ((@Functor.LaxMonoidal.μ _ _ _ _ _ _ (restriction J B)
      braided.toMonoidal.toLaxMonoidal M N).hom.app U)
        (fixedPure J B ((restriction J B).obj M) ((restriction J B).obj N) U x y) =
      ringPure J B M N U x y
  unit_hom : ∀ (U : Cᵒᵖ) (b : B),
    ((@Functor.OplaxMonoidal.η _ _ _ _ _ _ (restriction J B)
      braided.toMonoidal.toOplaxMonoidal).hom.app U)
        ((toSheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of B))).app U b) =
      fixedUnitScalar J B U b

set_option warn.classDefReducibility false in
private def monoidalKeepingLax
    {D E : Type*} [Category* D] [Category* E]
    [MonoidalCategory D] [MonoidalCategory E]
    (F : D ⥤ E) [F.LaxMonoidal] [IsIso (Functor.LaxMonoidal.ε F)]
    [∀ X Y, IsIso (Functor.LaxMonoidal.μ F X Y)] : F.Monoidal :=
  { (Functor.Monoidal.ofLaxMonoidal F) with toLaxMonoidal := inferInstance }

section OrdinaryProof
set_option warn.classDefReducibility false
private def scalarUnit :
    (Functor.const Cᵒᵖ).obj (RingCat.of B) ⟶
      ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj (ring J B)).obj :=
  toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of B)) ≫
    ((constantCommuteCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).inv.app
      (CommRingCat.of B)).hom

private def scalarMap (U : Cᵒᵖ) : B →+* (ring J B).obj.obj U :=
  ((scalarUnit J B).app U).hom

attribute [local irreducible] ring

section GenericRaw

private def constantToFunctor :
    PresheafOfModules.{max u v}
      (((Functor.const Cᵒᵖ).obj (CommRingCat.of B)) ⋙ forget₂ CommRingCat RingCat) ⥤
        Cᵒᵖ ⥤ ModuleCat.{max u v} B where
  obj P :=
    { obj := P.obj
      map := fun f ↦ P.map f
      map_id := fun X ↦ by ext x; exact congrArg (fun f ↦ f x) (P.map_id X)
      map_comp := fun f g ↦ by ext x; exact P.map_comp_apply f g x }
  map f :=
    { app := f.app
      naturality := fun _ _ g ↦ by ext x; exact PresheafOfModules.naturality_apply f g x }

set_option backward.isDefEq.respectTransparency false in
private def constantToFunctorLax : (constantToFunctor (C := C) B).LaxMonoidal where
  ε := { app X := 𝟙 _ }
  μ M N := { app X := 𝟙 _ }
  μ_natural_left := by intros; ext X x; rfl
  μ_natural_right := by intros; ext X x; rfl
  associativity := by
    intro M N P
    apply NatTrans.ext
    funext X
    change (𝟙 _ ▷ P.obj X) ≫ 𝟙 _ ≫ (α_ M N P).hom.app X =
      (α_ (M.obj X) (N.obj X) (P.obj X)).hom ≫ (M.obj X ◁ 𝟙 _) ≫ 𝟙 _
    simpa only [Category.id_comp, Category.comp_id,
      MonoidalCategory.id_whiskerRight, MonoidalCategory.whiskerLeft_id] using
      (PresheafOfModules.associator_hom_app M N P X)
  left_unitality := by
    intro M
    apply NatTrans.ext
    funext X
    change (λ_ (M.obj X)).hom =
      (𝟙 _ ▷ M.obj X) ≫ 𝟙 _ ≫ (λ_ M).hom.app X
    simpa only [Category.id_comp, Category.comp_id,
      MonoidalCategory.id_whiskerRight] using
      (PresheafOfModules.leftUnitor_hom_app M X).symm
  right_unitality := by
    intro M
    apply NatTrans.ext
    funext X
    change (ρ_ (M.obj X)).hom =
      (M.obj X ◁ 𝟙 _) ≫ 𝟙 _ ≫ (ρ_ M).hom.app X
    simpa only [Category.id_comp, Category.comp_id,
      MonoidalCategory.whiskerLeft_id] using
      (PresheafOfModules.rightUnitor_hom_app M X).symm

attribute [local instance] constantToFunctorLax

set_option backward.isDefEq.respectTransparency false in
private def rawRestrictionGeneric
    (R : Cᵒᵖ ⥤ CommRingCat.{max u v})
    (ι : (Functor.const Cᵒᵖ).obj (RingCat.of B) ⟶ R ⋙ forget₂ CommRingCat RingCat) :
    PresheafOfModules.{max u v} (R ⋙ forget₂ CommRingCat RingCat) ⥤
      Cᵒᵖ ⥤ ModuleCat.{max u v} B :=
  PresheafOfModules.restrictScalars ι ⋙ constantToFunctor B

set_option backward.isDefEq.respectTransparency false in
private def rawLaxGeneric
    (R : Cᵒᵖ ⥤ CommRingCat.{max u v})
    (ι : (Functor.const Cᵒᵖ).obj (RingCat.of B) ⟶ R ⋙ forget₂ CommRingCat RingCat) :
    (rawRestrictionGeneric B R ι).LaxMonoidal :=
  letI : MonoidalCategory (PresheafOfModules.{max u v}
      ((Functor.const Cᵒᵖ).obj (RingCat.of B))) :=
    inferInstanceAs (MonoidalCategory (PresheafOfModules.{max u v}
      (((Functor.const Cᵒᵖ).obj (CommRingCat.of B)) ⋙ forget₂ CommRingCat RingCat)))
  letI := PresheafOfModules.restrictScalarsLaxMonoidal
    (R := (Functor.const Cᵒᵖ).obj (CommRingCat.of B)) (R' := R) ι
  letI : (constantToFunctor (C := C) B).LaxMonoidal := constantToFunctorLax B
  Functor.LaxMonoidal.comp
    (PresheafOfModules.restrictScalars ι) (constantToFunctor B)

attribute [local instance] rawLaxGeneric

private def rawTensorGeneric
    (R : Cᵒᵖ ⥤ CommRingCat.{max u v})
    (ι : (Functor.const Cᵒᵖ).obj (RingCat.of B) ⟶ R ⋙ forget₂ CommRingCat RingCat)
    (M N : PresheafOfModules.{max u v} (R ⋙ forget₂ CommRingCat RingCat)) :
    (rawRestrictionGeneric B R ι).obj M ⊗ (rawRestrictionGeneric B R ι).obj N ⟶
      (rawRestrictionGeneric B R ι).obj (M ⊗ N) :=
  Functor.LaxMonoidal.μ (rawRestrictionGeneric B R ι) M N

set_option backward.isDefEq.respectTransparency false in
private def rawBraidedGeneric
    (R : Cᵒᵖ ⥤ CommRingCat.{max u v})
    (ι : (Functor.const Cᵒᵖ).obj (RingCat.of B) ⟶ R ⋙ forget₂ CommRingCat RingCat) :
    (rawRestrictionGeneric B R ι).LaxBraided where
  braided M N := by
    apply NatTrans.ext
    funext X
    change (𝟙 _ ≫ Functor.LaxMonoidal.μ
        (ModuleCat.restrictScalars (ι.app X).hom) (M.obj X) (N.obj X)) ≫
        (ModuleCat.restrictScalars (ι.app X).hom).map (β_ (M.obj X) (N.obj X)).hom =
      (β_ _ _).hom ≫ (𝟙 _ ≫ Functor.LaxMonoidal.μ
        (ModuleCat.restrictScalars (ι.app X).hom) (N.obj X) (M.obj X))
    simpa only [Category.id_comp] using
      Functor.LaxBraided.braided
        (F := ModuleCat.restrictScalars (ι.app X).hom) (M.obj X) (N.obj X)

end GenericRaw

private def rawRestriction :
    PresheafOfModules.{max u v}
      ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj (ring J B)).obj ⥤
      Cᵒᵖ ⥤ ModuleCat.{max u v} B := rawRestrictionGeneric B (ring J B).obj (scalarUnit J B)

private def rawTensor
    (M N : PresheafOfModules.{max u v}
      ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj (ring J B)).obj) :
    (rawRestriction J B).obj M ⊗ (rawRestriction J B).obj N ⟶
      (rawRestriction J B).obj (M ⊗ N) :=
   rawTensorGeneric B (ring J B).obj (scalarUnit J B) M N

@[instance_reducible]
private def rawLax : (rawRestriction J B).LaxMonoidal :=
  rawLaxGeneric B (ring J B).obj (scalarUnit J B)

attribute [local instance] rawLax

@[instance_reducible]
private def rawBraided : (rawRestriction J B).LaxBraided :=
  rawBraidedGeneric B (ring J B).obj (scalarUnit J B)

private abbrev moduleInclusion : Modules J B ⥤
    PresheafOfModules.{max u v}
      ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj (ring J B)).obj :=
  SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars (𝟙 _)

@[instance_reducible]
private def moduleInclusionLax : (moduleInclusion J B).LaxMonoidal :=
  (PresheafOfModules.sheafificationAdjunction.{max u v}
    (𝟙 ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj
      (ring J B)).obj)).rightAdjointLaxMonoidal

attribute [local instance] moduleInclusionLax

private def moduleInclusionBraided : (moduleInclusion J B).LaxBraided :=
  (PresheafOfModules.sheafificationAdjunction.{max u v}
    (𝟙 ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj
      (ring J B)).obj)).rightAdjointLaxBraided

set_option backward.isDefEq.respectTransparency true in
private def restrictionPresheafIso :
    moduleInclusion J B ⋙ rawRestriction J B ≅
      restriction J B ⋙ sheafToPresheaf J (ModuleCat.{max u v} B) :=
  NatIso.ofComponents (fun M ↦
    { hom :=
        { app X := ModuleCat.ofHom
            (X := ((moduleInclusion J B ⋙ rawRestriction J B).obj M).obj X)
            (Y := ((restriction J B ⋙ sheafToPresheaf J
              (ModuleCat.{max u v} B)).obj M).obj X)
            { toFun := fun x ↦ x
              map_add' := fun _ _ ↦ rfl
              map_smul' := fun _ _ ↦ rfl }
          naturality _ _ _ := by ext x; rfl }
      inv :=
        { app X := ModuleCat.ofHom
            (X := ((restriction J B ⋙ sheafToPresheaf J
              (ModuleCat.{max u v} B)).obj M).obj X)
            (Y := ((moduleInclusion J B ⋙ rawRestriction J B).obj M).obj X)
            { toFun := fun x ↦ x
              map_add' := fun _ _ ↦ rfl
              map_smul' := fun _ _ ↦ rfl }
          naturality _ _ _ := by ext x; rfl }
      hom_inv_id := by ext X x; rfl
      inv_hom_id := by ext X x; rfl }) (fun _ ↦ by ext X x; rfl)

private def fixedSheafificationMonoidal :
    (presheafToSheaf J (ModuleCat.{max u v} B)).Monoidal :=
  (sfbSheafTensorStructure (A := ModuleCat.{max u v} B) J).sheafificationMonoidal

attribute [local instance] fixedSheafificationMonoidal

private def fixedSheafificationBraided :
    (presheafToSheaf J (ModuleCat.{max u v} B)).Braided :=
  (sfbSheafTensorStructure (A := ModuleCat.{max u v} B) J).sheafificationBraided

attribute [local instance] fixedSheafificationBraided

private def restrictionSheafifiedIso :
    (moduleInclusion J B ⋙ rawRestriction J B) ⋙ presheafToSheaf J (ModuleCat.{max u v} B) ≅
      restriction J B :=
  Functor.isoWhiskerRight (restrictionPresheafIso J B) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (asIso (sheafificationAdjunction J (ModuleCat.{max u v} B)).counit) ≪≫
    (restriction J B).rightUnitor

private def ordinaryLax : (restriction J B).LaxMonoidal := by
  letI := rawLax J B
  letI := moduleInclusionLax J B
  letI := fixedSheafificationMonoidal J B
  exact Functor.LaxMonoidal.transport (restrictionSheafifiedIso J B)

attribute [local instance] ordinaryLax

private theorem scalarUnit_surjective : Presheaf.IsLocallySurjective J (scalarUnit J B) := by
  unfold scalarUnit
  unfold ring
  infer_instance

attribute [local instance] scalarUnit_surjective

set_option backward.isDefEq.respectTransparency false in
private theorem pairing_smul_left (M N H : Modules J B)
    (b : ∀ X : Cᵒᵖ, ((restriction J B).obj M).obj.obj X →ₗ[B]
      ((restriction J B).obj N).obj.obj X →ₗ[B] ((restriction J B).obj H).obj.obj X)
    (hb : ∀ {X Y : Cᵒᵖ} (f : X ⟶ Y) (x : M.val.obj X) (y : N.val.obj X),
      b Y (M.val.map f x) (N.val.map f y) = H.val.map f (b X x y))
    (X : Cᵒᵖ) (r : (ring J B).obj.obj X) (x : M.val.obj X) (y : N.val.obj X) :
    b X (r • x) y = r • (show H.val.obj X from b X x y) := by
  apply H.isSheaf.isSeparated _ (Presheaf.imageSieve (scalarUnit J B) r)
    (Presheaf.imageSieve_mem J (scalarUnit J B) r)
  rintro Y f ⟨a, ha⟩
  change H.val.map f.op (b X (r • x) y) = H.val.map f.op (r • (show H.val.obj X from b X x y))
  rw [← hb, H.val.map_smul, M.val.map_smul, ← ha, ← hb]
  exact congrArg (fun k ↦ k (N.val.map f.op y))
    ((b (Opposite.op Y)).map_smul a (M.val.map f.op x))

set_option backward.isDefEq.respectTransparency false in
private def upgradePairing (M N H : Modules J B)
    (b : ∀ X : Cᵒᵖ, ((restriction J B).obj M).obj.obj X →ₗ[B]
      ((restriction J B).obj N).obj.obj X →ₗ[B] ((restriction J B).obj H).obj.obj X)
    (hb : ∀ {X Y : Cᵒᵖ} (f : X ⟶ Y) (x : M.val.obj X) (y : N.val.obj X),
      b Y (M.val.map f x) (N.val.map f y) = H.val.map f (b X x y))
    (X : Cᵒᵖ) : M.val.obj X →ₗ[(ring J B).obj.obj X]
      N.val.obj X →ₗ[(ring J B).obj.obj X] H.val.obj X where
  toFun x :=
    { toFun := b X x
      map_add' := (b X x).map_add
      map_smul' := fun r y ↦ by
        let b' := fun Y ↦ (b Y).flip
        exact pairing_smul_left J B N M H b' (fun f y x ↦ hb f x y) X r y x }
  map_add' := fun x x' ↦ by ext y; exact congrArg (fun k ↦ k y) ((b X).map_add x x')
  map_smul' := fun r x ↦ by ext y; exact pairing_smul_left J B M N H b hb X r x y

set_option backward.isDefEq.respectTransparency false in
private def ringTensorLift (M N H : Modules J B)
    (b : ∀ X : Cᵒᵖ, M.val.obj X →ₗ[(ring J B).obj.obj X]
      N.val.obj X →ₗ[(ring J B).obj.obj X] H.val.obj X)
    (hb : ∀ {X Y : Cᵒᵖ} (f : X ⟶ Y) (x : M.val.obj X) (y : N.val.obj X),
      b Y (M.val.map f x) (N.val.map f y) = H.val.map f (b X x y)) :
    M ⊗ N ⟶ H :=
  (SheafOfModules.CochainScalarConstruction.cochain_tensor_bilinear_universal
    (ring J B) M N H b hb).choose

set_option backward.isDefEq.respectTransparency false in
private theorem ringTensorLift_pure (M N H : Modules J B)
    (b : ∀ X : Cᵒᵖ, M.val.obj X →ₗ[(ring J B).obj.obj X]
      N.val.obj X →ₗ[(ring J B).obj.obj X] H.val.obj X)
    (hb : ∀ {X Y : Cᵒᵖ} (f : X ⟶ Y) (x : M.val.obj X) (y : N.val.obj X),
      b Y (M.val.map f x) (N.val.map f y) = H.val.map f (b X x y))
    (U : Cᵒᵖ) (x : M.val.obj U) (y : N.val.obj U) :
    (ringTensorLift J B M N H b hb).val.app U (ringPure J B M N U x y) = b U x y :=
  (SheafOfModules.CochainScalarConstruction.cochain_tensor_bilinear_universal
    (ring J B) M N H b hb).choose_spec.1 U x y

set_option backward.isDefEq.respectTransparency false in
private theorem ringTensor_ext (M N H : Modules J B) (f g : M ⊗ N ⟶ H)
    (h : ∀ (U : Cᵒᵖ) (x : M.val.obj U) (y : N.val.obj U),
      f.val.app U (ringPure J B M N U x y) =
        g.val.app U (ringPure J B M N U x y)) : f = g := by
  apply SheafOfModules.CochainScalarConstruction.pure_hom_ext (ring J B) M N H
  exact h

set_option backward.isDefEq.respectTransparency false in
private theorem fixedTensor_ext (M N H : Fixed J B) (f g : M ⊗ N ⟶ H)
    (h : ∀ (U : Cᵒᵖ) (x : M.obj.obj U) (y : N.obj.obj U),
      f.hom.app U (fixedPure J B M N U x y) =
        g.hom.app U (fixedPure J B M N U x y)) : f = g := by
  apply (cancel_epi (sfbSheafTensor_comparison J M N).inv).mp
  apply ((sheafificationAdjunction J (ModuleCat.{max u v} B)).homEquiv (M.obj ⊗ N.obj) H).injective
  apply NatTrans.ext
  funext U
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro x y
  exact h U x y

set_option backward.isDefEq.respectTransparency true in
private theorem ringPure_inclusion (M N : Modules J B) (U : Cᵒᵖ)
    (x : M.val.obj U) (y : N.val.obj U) :
    (Functor.LaxMonoidal.μ (moduleInclusion J B) M N).app U
      (x ⊗ₜ[(ring J B).obj.obj U] y) = ringPure J B M N U x y := by
  dsimp only [Functor.LaxMonoidal.μ, moduleInclusionLax]
  rw [Adjunction.homEquiv_unit]
  rfl

private def ordinaryLaxBraided : (restriction J B).LaxBraided := by
  letI := rawBraided J B
  letI := moduleInclusionBraided J B
  letI := Functor.LaxMonoidal.natTransIsMonoidal_of_transport
    (restrictionSheafifiedIso J B)
  exact Functor.LaxBraided.ofNatIso (restrictionSheafifiedIso J B)

private def fixedInclusionLax : (sheafToPresheaf J (ModuleCat.{max u v} B)).LaxMonoidal :=
  (sheafificationAdjunction J (ModuleCat.{max u v} B)).rightAdjointLaxMonoidal

attribute [local instance] fixedInclusionLax

set_option backward.isDefEq.respectTransparency false in
private theorem monoidalMate
    {X A D : Type*} [Category* X] [Category* A] [Category* D]
    [MonoidalCategory X] [MonoidalCategory A] [MonoidalCategory D]
    (H : X ⥤ A) (G : X ⥤ D) (a : A ⥤ D) (j : D ⥤ A)
    [H.LaxMonoidal] [a.Monoidal] [j.LaxMonoidal]
    (adj : a ⊣ j) [adj.IsMonoidal] [j.Full] [j.Faithful]
    (i : H ≅ G ⋙ j) :
    let e := Functor.isoWhiskerRight i a ≪≫ Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft G (asIso adj.counit) ≪≫ G.rightUnitor
    letI : G.LaxMonoidal := Functor.LaxMonoidal.transport e
    NatTrans.IsMonoidal i.hom := by
  dsimp only
  let e := Functor.isoWhiskerRight i a ≪≫ Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft G (asIso adj.counit) ≪≫ G.rightUnitor
  let : G.LaxMonoidal := Functor.LaxMonoidal.transport e
  have := Functor.LaxMonoidal.natTransIsMonoidal_of_transport e
  let τ : H ⟶ G ⋙ j :=
    H.rightUnitor.inv ≫ Functor.whiskerLeft H adj.unit ≫
      (Functor.associator H a j).inv ≫ Functor.whiskerRight e.hom j
  have ht : NatTrans.IsMonoidal τ := by dsimp [τ]; infer_instance
  have he : τ = i.hom := by
    apply NatTrans.ext
    funext M
    dsimp [τ, e]
    simp only [Category.id_comp, Category.comp_id, j.map_comp]
    erw [← Category.assoc, adj.unit_naturality]
    erw [Category.assoc, adj.right_triangle_components, Category.comp_id]
  exact he ▸ ht

set_option backward.isDefEq.respectTransparency false in
private theorem restrictionPresheafIso_monoidal :
    NatTrans.IsMonoidal (restrictionPresheafIso J B).hom := by
  exact monoidalMate (moduleInclusion J B ⋙ rawRestriction J B) (restriction J B)
    (presheafToSheaf J (ModuleCat.{max u v} B))
    (sheafToPresheaf J (ModuleCat.{max u v} B))
    (sheafificationAdjunction J (ModuleCat.{max u v} B)) (restrictionPresheafIso J B)

set_option backward.isDefEq.respectTransparency true in
private theorem fixedPure_inclusion (M N : Fixed J B) (U : Cᵒᵖ)
    (x : M.obj.obj U) (y : N.obj.obj U) :
    (Functor.LaxMonoidal.μ (sheafToPresheaf J (ModuleCat.{max u v} B)) M N).app U
      (x ⊗ₜ[B] y) = fixedPure J B M N U x y := by
  rfl

set_option backward.isDefEq.respectTransparency true in
private theorem restrictionPresheafIso_apply (M : Modules J B) (U : Cᵒᵖ)
    (x : ((moduleInclusion J B ⋙ rawRestriction J B).obj M).obj U) :
    ((restrictionPresheafIso J B).hom.app M).app U x = x := by rfl

set_option backward.isDefEq.respectTransparency false in
private theorem rawRestriction_map_apply
    {M N : PresheafOfModules.{max u v}
      ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj (ring J B)).obj}
    (f : M ⟶ N) (U : Cᵒᵖ) (x : M.obj U) :
    ((rawRestriction J B).map f).app U x = f.app U x := by rfl

set_option backward.isDefEq.respectTransparency false in
private theorem rawTensor_pure
    (M N : PresheafOfModules.{max u v}
      ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj (ring J B)).obj)
    (U : Cᵒᵖ) (x : M.obj U) (y : N.obj U) :
    (rawTensor J B M N).app U (x ⊗ₜ[B] y) = x ⊗ₜ[(ring J B).obj.obj U] y := by
  exact @ModuleCat.restrictScalars_μ_tmul B ((ring J B).obj.obj U) _ _
    (scalarMap J B U) (M.obj U) (N.obj U) x y

private theorem isoTensor_pure (M N : Modules J B) (U : Cᵒᵖ)
    (x : M.val.obj U) (y : N.val.obj U) : (((restrictionPresheafIso J B).hom.app M).app U ⊗ₘ
      ((restrictionPresheafIso J B).hom.app N).app U) (x ⊗ₜ[B] y) =
        (show ((restriction J B).obj M).obj.obj U from x) ⊗ₜ[B]
          (show ((restriction J B).obj N).obj.obj U from y) := by
  rfl

attribute [local irreducible] ordinaryLax ringPure fixedPure restrictionPresheafIso
set_option backward.isDefEq.respectTransparency false in
private theorem ordinary_μ_pure (M N : Modules J B) (U : Cᵒᵖ)
    (x : M.val.obj U) (y : N.val.obj U) :
    (Functor.LaxMonoidal.μ (restriction J B) M N).hom.app U
      (fixedPure J B ((restriction J B).obj M) ((restriction J B).obj N) U x y) =
      ringPure J B M N U x y := by
  have := restrictionPresheafIso_monoidal J B
  have h := NatTrans.IsMonoidal.tensor (τ := (restrictionPresheafIso J B).hom) M N
  have hh := congrArg (fun f ↦ f.app U (x ⊗ₜ[B] y)) h
  change ((restrictionPresheafIso J B).hom.app (M ⊗ N)).app U
    (((rawRestriction J B).map
      (Functor.LaxMonoidal.μ (moduleInclusion J B) M N)).app U
        ((rawTensor J B ((moduleInclusion J B).obj M)
          ((moduleInclusion J B).obj N)).app U (x ⊗ₜ[B] y))) =
    (Functor.LaxMonoidal.μ (restriction J B) M N).hom.app U
      ((Functor.LaxMonoidal.μ (sheafToPresheaf J (ModuleCat.{max u v} B))
        ((restriction J B).obj M) ((restriction J B).obj N)).app U
          ((((restrictionPresheafIso J B).hom.app M).app U ⊗ₘ
            ((restrictionPresheafIso J B).hom.app N).app U) (x ⊗ₜ[B] y))) at hh
  rw [rawTensor_pure, rawRestriction_map_apply, isoTensor_pure,
    restrictionPresheafIso_apply, ringPure_inclusion, fixedPure_inclusion] at hh
  exact hh.symm

attribute [local semireducible] ringPure fixedPure restrictionPresheafIso

set_option backward.isDefEq.respectTransparency true in
private def fixedPairing (M N : Fixed J B) (U : Cᵒᵖ) :
    M.obj.obj U →ₗ[B] N.obj.obj U →ₗ[B] (M ⊗ N).obj.obj U :=
  (TensorProduct.mk B _ _).compr₂
    (((sfbSheafTensor_comparison J M N).inv.hom.app U).hom.comp
      ((toSheafify J (M.obj ⊗ N.obj)).app U).hom)

set_option backward.isDefEq.respectTransparency true in
private theorem fixedPure_naturality (M N : Fixed J B) {U V : Cᵒᵖ} (f : U ⟶ V)
    (x : M.obj.obj U) (y : N.obj.obj U) :
    fixedPure J B M N V (M.obj.map f x) (N.obj.map f y) =
      (M ⊗ N).obj.map f (fixedPure J B M N U x y) := by
  let q := toSheafify J (M.obj ⊗ N.obj) ≫ (sfbSheafTensor_comparison J M N).inv.hom
  exact ConcreteCategory.congr_hom (q.naturality f) (x ⊗ₜ[B] y)

set_option backward.isDefEq.respectTransparency true in
private theorem restrictionTensor_ext (M N H : Modules J B)
    (f g : (restriction J B).obj (M ⊗ N) ⟶ (restriction J B).obj H)
    (h : ∀ (U : Cᵒᵖ) (x : M.val.obj U) (y : N.val.obj U),
      f.hom.app U (ringPure J B M N U x y) =
        g.hom.app U (ringPure J B M N U x y)) : f = g := by
  let F := restriction J B
  have hh : F.preimage f = F.preimage g := by
    apply ringTensor_ext J B M N H
    intro U x y
    change (F.map (F.preimage f)).hom.app U (ringPure J B M N U x y) =
      (F.map (F.preimage g)).hom.app U (ringPure J B M N U x y)
    simpa only [F.map_preimage] using h U x y
  simpa only [F.map_preimage] using congrArg F.map hh

set_option backward.isDefEq.respectTransparency false in
private theorem ordinary_μ_isIso (M N : Modules J B) :
    IsIso (Functor.LaxMonoidal.μ (restriction J B) M N) := by
  let F := restriction J B
  let H := F.objPreimage (F.obj M ⊗ F.obj N)
  let e : F.obj H ≅ F.obj M ⊗ F.obj N := F.objObjPreimageIso _
  let b (U : Cᵒᵖ) :=
    (fixedPairing J B (F.obj M) (F.obj N) U).compr₂ (e.inv.hom.app U).hom
  have hb {X Y : Cᵒᵖ} (f : X ⟶ Y) (x : M.val.obj X) (y : N.val.obj X) :
      b Y (M.val.map f x) (N.val.map f y) = H.val.map f (b X x y) := by
    change e.inv.hom.app Y
      (fixedPure J B (F.obj M) (F.obj N) Y (M.val.map f x) (N.val.map f y)) = _
    erw [fixedPure_naturality]
    exact ConcreteCategory.congr_hom (e.inv.hom.naturality f) _
  let q := ringTensorLift J B M N H (upgradePairing J B M N H b hb) hb
  have hq (U : Cᵒᵖ) (x : M.val.obj U) (y : N.val.obj U) :
      q.val.app U (ringPure J B M N U x y) = b U x y :=
    ringTensorLift_pure J B M N H _ hb U x y
  let r := F.map q ≫ e.hom
  have hr (U : Cᵒᵖ) (x : M.val.obj U) (y : N.val.obj U) :
      r.hom.app U (ringPure J B M N U x y) =
        fixedPure J B (F.obj M) (F.obj N) U x y := by
    change e.hom.hom.app U (q.val.app U (ringPure J B M N U x y)) = _
    rw [hq]
    exact ConcreteCategory.congr_hom
      (congr_app (congrArg (fun f ↦ f.hom) e.inv_hom_id) U) _
  refine ⟨⟨r, ?_, ?_⟩⟩
  · apply fixedTensor_ext J B
    intro U x y
    change r.hom.app U
      ((Functor.LaxMonoidal.μ F M N).hom.app U (fixedPure J B _ _ U x y)) = _
    rw [ordinary_μ_pure, hr]
    rfl
  · apply restrictionTensor_ext J B M N (M ⊗ N)
    intro U x y
    change (Functor.LaxMonoidal.μ F M N).hom.app U
      (r.hom.app U (ringPure J B M N U x y)) = _
    rw [hr, ordinary_μ_pure]
    rfl

set_option backward.isDefEq.respectTransparency true in
private theorem ordinary_ε_isIso : IsIso (Functor.LaxMonoidal.ε (restriction J B)) := by
  let F := restriction J B
  let X := F.objPreimage (𝟙_ (Fixed J B))
  let e := F.objObjPreimageIso (𝟙_ (Fixed J B))
  have := ordinary_μ_isIso J B (𝟙_ (Modules J B)) X
  have h : IsIso (Functor.LaxMonoidal.ε F ▷ F.obj X) := by
    have hh : IsIso ((Functor.LaxMonoidal.ε F ▷ F.obj X) ≫
        Functor.LaxMonoidal.μ F (𝟙_ _) X ≫ F.map (λ_ X).hom) := by
      rw [← Functor.LaxMonoidal.left_unitality]
      infer_instance
    exact IsIso.of_isIso_comp_right (Functor.LaxMonoidal.ε F ▷ F.obj X)
      (Functor.LaxMonoidal.μ F (𝟙_ _) X ≫ F.map (λ_ X).hom)
  let i : tensorRight (F.obj X) ≅ 𝟭 (Fixed J B) :=
    (tensoringRight (Fixed J B)).mapIso e ≪≫ rightUnitorNatIso (Fixed J B)
  have : (tensorRight (F.obj X)).IsEquivalence := Functor.isEquivalence_of_iso i.symm
  have : IsIso ((tensorRight (F.obj X)).map (Functor.LaxMonoidal.ε F)) := h
  exact isIso_of_reflects_iso (Functor.LaxMonoidal.ε F) (tensorRight (F.obj X))

attribute [local semireducible] ring

set_option backward.isDefEq.respectTransparency true in
private theorem ordinary_ε_scalar (U : Cᵒᵖ) (b : B) :
    (Functor.LaxMonoidal.ε (restriction J B)).hom.app U (fixedUnitScalar J B U b) =
      (toSheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of B))).app U b := by
  have := restrictionPresheafIso_monoidal J B
  have h := NatTrans.IsMonoidal.unit (τ := (restrictionPresheafIso J B).hom)
  have hh := congrArg (fun f ↦ f.app U b) h
  have hc := toSheafify_naturality J
    (Functor.constComp Cᵒᵖ (CommRingCat.of B) (forget₂ CommRingCat.{max u v} RingCat.{max u v})).inv
  have hu : (scalarUnit J B).app U b =
      (toSheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of B))).app U b := by
    change ((toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of B)) ≫
      sheafifyMap J
        (Functor.constComp Cᵒᵖ (CommRingCat.of B)
          (forget₂ CommRingCat.{max u v} RingCat.{max u v})).inv ≫
      (sheafifyComposeIso J (forget₂ CommRingCat.{max u v} RingCat.{max u v})
        ((Functor.const Cᵒᵖ).obj (CommRingCat.of B))).hom).app U) b = _
    erw [← Category.assoc, ← hc, Category.assoc, sheafComposeIso_hom_fac]
    rfl
  change (Functor.LaxMonoidal.ε (rawRestriction J B) ≫
      (rawRestriction J B).map (Functor.LaxMonoidal.ε (moduleInclusion J B)) ≫
      (restrictionPresheafIso J B).hom.app (𝟙_ (Modules J B))).app U b =
    (Functor.LaxMonoidal.ε (sheafToPresheaf J (ModuleCat.{max u v} B)) ≫
      (sheafToPresheaf J (ModuleCat.{max u v} B)).map
        (Functor.LaxMonoidal.ε (restriction J B))).app U b at hh
  simp only [NatTrans.comp_app, ModuleCat.comp_apply] at hh
  change (Functor.LaxMonoidal.ε (moduleInclusion J B)).app U
      (Functor.LaxMonoidal.ε
        (ModuleCat.restrictScalars (scalarMap J B U)) b) =
    (Functor.LaxMonoidal.ε (restriction J B)).hom.app U
      ((Functor.LaxMonoidal.ε (sheafToPresheaf J (ModuleCat.{max u v} B))).app U b) at hh
  erw [@ModuleCat.restrictScalars_η B ((ring J B).obj.obj U) _ _
    (scalarMap J B U)] at hh
  have hm := (PresheafOfModules.sheafificationAdjunction.{max u v}
    (𝟙 ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj
      (ring J B)).obj)).right_triangle_components (𝟙_ (Modules J B))
  have hmm := congrArg (fun f ↦ f.app U ((scalarMap J B U) b)) hm
  change (Functor.LaxMonoidal.ε (moduleInclusion J B)).app U ((scalarMap J B U) b) =
    (scalarMap J B U) b at hmm
  rw [hmm] at hh
  have hf : (Functor.LaxMonoidal.ε (sheafToPresheaf J (ModuleCat.{max u v} B))).app U b =
      fixedUnitScalar J B U b := by rfl
  rw [hf] at hh
  exact hh.symm.trans hu

@[instance_reducible]
private def ordinaryMonoidal : (restriction J B).Monoidal := by
  have := ordinary_ε_isIso J B
  have := ordinary_μ_isIso J B
  exact monoidalKeepingLax (restriction J B)

/-- Existence of the normalized ordinary tensor comparison.
Source: Stacks 03CY and 0GMW
(blueprint: lem-sfb-constant-scalar-restriction-tensor).
Proof: Compose sectionwise lax braided scalar restriction with the lax inclusion of
module sheaves and strong braided fixed-coefficient sheafification. Transport across the
sheafification counit to the literal restriction. The adjunction triangle identity makes
its presheaf identification monoidal and gives the normalized tensor and scalar equations.
A compatible B-bilinear pairing is ring-sheaf bilinear: on the covering image sieve of each
scalar, that scalar lifts to a constant, where B-linearity proves the equation; separatedness
then proves it globally. Apply this to the fixed pure pairing, transported to the inverse
image of its target, and extend through ringed tensor sheafification. Both composites fix
pure tensors, hence are identities. Finally choose a source object whose image is the tensor
unit. Lax unitality and the invertible tensorator show that tensoring the unit map with that
image is invertible. This tensor functor is isomorphic to the identity and reflects
isomorphisms. Thus the lax braided structure is strong, with the required inverse formulas. -/
theorem ordinary_exists : Nonempty (Ordinary J B) := by
  let := ordinaryMonoidal J B
  refine ⟨⟨{ toMonoidal := ordinaryMonoidal J B, braided := ?_ }, ?_, ?_, ?_⟩⟩
  · intro X Y
    exact (ordinaryLaxBraided J B).braided X Y
  · intro M N U x y
    have h := ConcreteCategory.congr_hom
      (congr_app (congrArg (fun f ↦ f.hom)
        (Functor.Monoidal.μ_δ (restriction J B) M N)) U)
      (fixedPure J B ((restriction J B).obj M) ((restriction J B).obj N) U x y)
    change (Functor.OplaxMonoidal.δ (restriction J B) M N).hom.app U
      ((Functor.LaxMonoidal.μ (restriction J B) M N).hom.app U
        (fixedPure J B ((restriction J B).obj M) ((restriction J B).obj N) U x y)) =
      fixedPure J B ((restriction J B).obj M) ((restriction J B).obj N) U x y at h
    rw [ordinary_μ_pure] at h
    exact h
  · exact ordinary_μ_pure J B
  · intro U b
    have h := ConcreteCategory.congr_hom
      (congr_app (congrArg (fun f ↦ f.hom)
        (Functor.Monoidal.ε_η (restriction J B))) U) (fixedUnitScalar J B U b)
    change (Functor.OplaxMonoidal.η (restriction J B)).hom.app U
      ((Functor.LaxMonoidal.ε (restriction J B)).hom.app U (fixedUnitScalar J B U b)) =
        fixedUnitScalar J B U b at h
    rw [ordinary_ε_scalar] at h
    exact h

end OrdinaryProof
/-- The canonical ordinary structure, uniquely determined by both pure-tensor equations
and the constant-scalar unit equation in `Ordinary`.
Source: Stacks 0GMW (blueprint: lem-sfb-constant-scalar-restriction-tensor). -/
def ordinary : Ordinary J B := (ordinary_exists J B).some

/-- The canonical normalized braided structure on restriction.
Source: Stacks 0GMW (blueprint: lem-sfb-constant-scalar-restriction-tensor). -/
instance restrictionBraided : (restriction J B).Braided := (ordinary J B).braided

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
/-- The existing Grothendieck structure of module sheaves.
Source: Stacks 03DA (blueprint: lem-sfb-constant-scalar-restriction-tensor). -/
instance ringGrothendieck : IsGrothendieckAbelian.{max u v} (Modules J B) :=
  SheafOfModules.isGrothendieckAbelian_coefficientUniverse _

/-- Transport the Grothendieck structure along the actual restriction equivalence.
Source: Stacks 03CY (blueprint: lem-sfb-constant-scalar-restriction-tensor). -/
instance fixedGrothendieck : IsGrothendieckAbelian.{max u v} (Fixed J B) :=
  IsGrothendieckAbelian.of_equivalence (restriction J B).asEquivalence

/-- Cache countable colimits in fixed-coefficient module sheaves.
Source: Stacks 03CY (blueprint: lem-sfb-constant-scalar-restriction-tensor). -/
instance fixedSmallColimits : HasColimitsOfSize.{0, 0} (Fixed J B) :=
  letI : HasColimitsOfSize.{max u v, max u v} (Fixed J B) :=
    IsGrothendieckAbelian.hasColimits (Fixed J B)
  hasColimitsOfSizeShrink.{0, 0, max u v, max u v} (Fixed J B)

/-- The discrete colimits used in signed totals, at their actual index size.
Source: Stacks 06YL (blueprint: lem-sfb-constant-scalar-restriction-tensor). -/
instance fixedDiscreteColimits (I : Type) : HasColimitsOfShape (Discrete I) (Fixed J B) :=
  (fixedSmallColimits J B).has_colimits_of_shape (Discrete I)

/-- Evaluate the preceding discrete-colimit instance without searching for a new size.
Source: Stacks 06YL (blueprint: lem-sfb-constant-scalar-restriction-tensor). -/
instance fixedDiscreteColimit {I : Type} (F : Discrete I ⥤ Fixed J B) : HasColimit F :=
  (fixedDiscreteColimits J B I).has_colimit F

/-- Countable coproducts for the two-sided quasi-isomorphism test.
Source: Stacks 06YP (blueprint: lem-sfb-constant-scalar-restriction-tensor). -/
instance fixedCountableCoproducts : HasCountableCoproducts (Fixed J B) where
  out I _ := fixedDiscreteColimits J B I

/-- Closedness of the existing ringed-site tensor at the independent site universes.
Source: Stacks 03EO (blueprint: lem-sfb-constant-scalar-restriction-tensor). -/
instance ringClosed : MonoidalClosed (Modules J B) :=
  (SheafOfModules.nonempty_monoidalClosed_independentCoefficients (R := ring J B)).some

/-- The termwise equivalence on unbounded cochain complexes.
Source: Stacks 015F (blueprint: lem-sfb-constant-scalar-restriction-tensor). -/
abbrev onComplexes : CochainComplex (Modules J B) ℤ ⥤ CochainComplex (Fixed J B) ℤ :=
  (restriction J B).mapHomologicalComplex (.up ℤ)

/-- The signed total comparison commutes with the Koszul symmetry.
Source: Stacks 06YL (blueprint: lem-sfb-constant-scalar-restriction-tensor).
Proof: step 4 checks on each (p,q) coproduct injection. Both paths exchange the
ordinary pure tensors and multiply by the same sign (-1)^(pq); additivity retains it.
The coproduct universal property then proves equality. -/
theorem total_symmetry :
    ComplexSymmetryCompatibility (Modules J B) (Fixed J B) (restriction J B) := by
  exact ⟨Functor.OplaxMonoidal.cochainBraided (restriction J B), rfl⟩

/-- Flatness is preserved and reflected.
Source: Stacks 03ER (blueprint: lem-sfb-constant-scalar-restriction-tensor).
Proof: step 5 conjugates right tensor by the normalized tensor isomorphism and the
exact equivalence from step 1. Exactness is invariant under these conjugations. -/
theorem flat_iff (M : Modules J B) :
    SheafOfModules.IsFlatOnSite (R := ring J B) M ↔
      exactFunctor _ _ (tensorRight ((restriction J B).obj M)) := by
  have hs : SheafOfModules.IsFlatOnSite (R := ring J B) M ↔
      exactFunctor _ _ (tensorRight M) :=
    ⟨(exactFunctor _ _).prop_of_iso (SheafOfModules.siteSheafTensorRightIso (ring J B) M),
      (exactFunctor _ _).prop_of_iso
        (SheafOfModules.siteSheafTensorRightIso (ring J B) M).symm⟩
  exact hs.trans ((rightFlat_iff M).symm.trans
    ((flat_equivalence (restriction J B) M).trans (rightFlat_iff _)))

/-- The acyclic-test K-flat condition agrees on both sides and agrees with the two-sided
quasi-isomorphism test.
Source: Stacks 06YN and 06YP (blueprint: lem-sfb-constant-scalar-restriction-tensor).
Proof: step 5 lifts every acyclic fixed-coefficient complex by the inverse exact
equivalence. Step 4 identifies its total tensor with the image of the ringed total tensor.
Step 6 uses lem-pc-tensor-mapping-cone-iso and lem-pur-quasi-iso-cone-acyclic to pass from
acyclic tests to quasi-isomorphism tests; conversely test the map 0 to an acyclic complex.
Symmetry supplies the other tensor argument in both categories. -/
theorem kflat_iff (P : CochainComplex (Modules J B) ℤ) :
    KFlatComparison (Modules J B) (Fixed J B) (restriction J B)
      (fun Q ↦ Q.IsKFlatIndependentCoefficients) P := by
  let : TensorPreservesCountableCoproducts (Modules J B) :=
    ⟨fun _ _ _ ↦ inferInstance, fun _ _ _ ↦ inferInstance⟩
  let : TensorPreservesCountableCoproducts (Fixed J B) :=
    ⟨fun _ _ _ ↦ inferInstance, fun _ _ _ ↦ inferInstance⟩
  exact abstract_kflat_comparison (restriction J B) P

/-- The recorded functorial flat resolutions for ringed-site modules.
Source: Stacks 06YS (blueprint: lem-sfb-constant-scalar-restriction-tensor). -/
instance ringFlatResolutions : Abelian.HasFunctorialFlatResolution (Modules J B) :=
  SheafOfModules.hasFunctorialFlatResolution_kfi (ring J B)

/-- Transport flat resolutions to fixed-coefficient module sheaves.
Source: Stacks 06YS (blueprint: lem-sfb-constant-scalar-restriction-tensor).
Proof: apply the inverse equivalence to a module sheaf, take the functorial flat cover
used in lem-pc-kflat-resolution, then restrict back. Step 5 identifies flatness and
step 1 preserves the epimorphic augmentation; naturality gives the resolution functor.
This supplies the canonical K-flat derived tensor API without adding a resolution hypothesis. -/
@[instance] theorem fixedFlatResolutions : Abelian.HasFunctorialFlatResolution (Fixed J B) := by
  exact flatResolutionTransport (restriction J B)

variable [HasDerivedCategory.{wR} (Modules J B)] [HasDerivedCategory.{wB} (Fixed J B)]

/-- The induced equivalence of ordinary unbounded derived categories.
Source: Stacks 015F and 05RT (blueprint: lem-sfb-constant-scalar-restriction-tensor). -/
def onDerived : DerivedCategory (Modules J B) ⥤ DerivedCategory (Fixed J B) :=
  (restriction J B).mapDerivedCategory

/-- The derived localization retains the exact equivalence and its termwise inverse.
Source: Stacks 015F and 05RT (blueprint: lem-sfb-constant-scalar-restriction-tensor).
Proof: step 7 descends the termwise unit and counit along quasi-isomorphisms; their
triangle identities descend as well, giving the inverse equivalence. -/
@[instance] theorem derived_isEquivalence : (onDerived J B).IsEquivalence := by
  change ((restriction J B).mapDerivedCategory).IsEquivalence
  infer_instance

/-- The normalized coherent comparison on ordinary unbounded K-flat derived tensors.
The monoidal structures here are the existing K-flat derived localization structures.
Source: Stacks 06YS, 0G7D, 06YT and 06YU
(blueprint: lem-sfb-constant-scalar-restriction-tensor).
The tensor square specifies the comparison on every pair of K-flat representatives,
using precisely `Functor.mapCochainComplexμIso` and the canonical localization maps.
The unit square fixes its normalization at the regular unit complex. -/
abbrev DerivedComparison :=
  DerivedComparisonData (Modules J B) (Fixed J B) (restriction J B)
    (fun P ↦ P.IsKFlatIndependentCoefficients)

/-- Restriction has the coherent derived tensor comparison computed by the total maps.
Source: Stacks 06YS, 0G7D, 06YT and 06YU
(blueprint: lem-sfb-constant-scalar-restriction-tensor).
Proof: step 7 applies lem-sf-exact-functor-derived-triangulated to the exact equivalence
and its inverse. Their termwise inverse identities descend to the derived localization.
For step 8 use lem-weil-pbc-site-derived-tensor-descent on flat-term K-flat complexes;
step 5 identifies the resolving subcategories. Localize the step-4 total tensor maps in
both variables. The descent node's extension and uniqueness clause gives the natural
comparison on all derived objects. Its inverse is the localized inverse total map.
Associativity, unit and symmetry diagrams hold on resolving representatives by steps 3--4,
and hence on all derived objects by successive localization. Finally step 6 permits
arbitrary K-flat representatives: their total tensor functors invert quasi-isomorphisms,
so comparison with flat-term resolutions gives the same square recorded above. -/
theorem derived_comparison : Nonempty (DerivedComparison J B) := by
  apply abstract_derived_comparison (restriction J B)
    (fun P ↦ P.IsKFlatIndependentCoefficients)
  intro P hP
  exact (kflat_iff J B P).2.2.mp ((kflat_iff J B P).2.1.mpr hP)

end CategoryTheory.ConstantScalarRestriction

