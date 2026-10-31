/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CompletedAdicKoszulConstruction
public import WeilConjectures.AlgebraicGeometry.CompletedAdicCoefficientDatumSupplement
public import WeilConjectures.AlgebraicGeometry.IntrinsicKoszulCompletion
public import WeilConjectures.AlgebraicGeometry.KoszulComplex
public import WeilConjectures.AlgebraicGeometry.KoszulDifferential
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
public import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone

import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Homology.DerivedCategory.TowerLimit
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import WeilConjectures.CategoryTheory.ConstantModuleKFlat
import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
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
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.CategoryTheory.Monoidal.Preadditive
import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatAllIndependentCoefficients
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap
import WeilConjectures.Algebra.Homology.ChangeOfRingsTensorCancellationIndependentCoefficientsSupplement
import WeilConjectures.AlgebraicGeometry.ProEtaleCountableProductsExact
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.AlgebraicGeometry.CompletedIntegralCoefficientsSupplement
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.CategoryTheory.Limits.Shapes.Countable
import WeilConjectures.AlgebraicGeometry.ProEtaleAffineWeaklyContractibleCover
import WeilConjectures.AlgebraicGeometry.ProEtaleAffineContractibleExtension
import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
import WeilConjectures.AlgebraicGeometry.ProEtaleWeaklyContractibleEvaluationColimitsSupplement
import Mathlib.CategoryTheory.Sites.CompatibleSheafification
import Mathlib.CategoryTheory.Limits.Types.Products
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.CategoryTheory.Sites.Abelian

/-! # Independence of the completed Koszul complex representative

The Koszul construction is in `CompletedAdicKoszulConstruction`. Bounded flat factors,
exact countable products and localization give its unit-compatible representative
comparison. Source: blueprint def-weil-pbc-intrinsic-completion.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe t w

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped ChangeOfRings

namespace AlgebraicGeometry.Scheme

variable {A : Type t} [CommRing A]

section AdicTensorNaturality
variable {M : Type*} [Category* M] [Preadditive M] [MonoidalCategory M]
  [MonoidalPreadditive M]
  (C D K L : CochainComplex M ℤ)
  [HomologicalComplex.HasMapBifunctor C K (curriedTensor M) (.up ℤ)]
  [HomologicalComplex.HasMapBifunctor C L (curriedTensor M) (.up ℤ)]
  [HomologicalComplex.HasMapBifunctor D K (curriedTensor M) (.up ℤ)]

private theorem adicTensorUnit_natural (u : 𝟙_ M ⟶ K.X 0) (α : C ⟶ D) (p : ℤ) :
    α.f p ≫ (ρ_ (D.X p)).inv ≫ D.X p ◁ u ≫
        HomologicalComplex.ιMapBifunctor D K (curriedTensor M) (.up ℤ) p 0 p (add_zero p) =
      ((ρ_ (C.X p)).inv ≫ C.X p ◁ u ≫
        HomologicalComplex.ιMapBifunctor C K (curriedTensor M) (.up ℤ) p 0 p (add_zero p)) ≫
          (HomologicalComplex.mapBifunctorMap α (𝟙 K) (curriedTensor M) (.up ℤ)).f p := by
  rw [Category.assoc, Category.assoc, HomologicalComplex.ι_mapBifunctorMap]
  simp only [HomologicalComplex.id_f, curriedTensor_map_app, curriedTensor_obj_map,
    whiskerLeft_id]
  rw [whisker_exchange_assoc, ← rightUnitor_inv_naturality_assoc]
  simp

private theorem adicTensorMap_id :
    HomologicalComplex.mapBifunctorMap (𝟙 C) (𝟙 K) (curriedTensor M) (.up ℤ) = 𝟙 _ := by
  apply HomologicalComplex.hom_ext
  intro i
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q hpq
  simp

private theorem adicTensorMap_comp (E : CochainComplex M ℤ)
    [HomologicalComplex.HasMapBifunctor E K (curriedTensor M) (.up ℤ)]
    (α : C ⟶ D) (β : D ⟶ E) :
    HomologicalComplex.mapBifunctorMap (α ≫ β) (𝟙 K) (curriedTensor M) (.up ℤ) =
      HomologicalComplex.mapBifunctorMap α (𝟙 K) (curriedTensor M) (.up ℤ) ≫
        HomologicalComplex.mapBifunctorMap β (𝟙 K) (curriedTensor M) (.up ℤ) := by
  apply HomologicalComplex.hom_ext
  intro i
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q hpq
  simp [Category.assoc]

private theorem adicTensorMap_exchange
    [HomologicalComplex.HasMapBifunctor D L (curriedTensor M) (.up ℤ)]
    (α : C ⟶ D) (τ : K ⟶ L) :
    HomologicalComplex.mapBifunctorMap α (𝟙 K) (curriedTensor M) (.up ℤ) ≫
        HomologicalComplex.mapBifunctorMap (𝟙 D) τ (curriedTensor M) (.up ℤ) =
      HomologicalComplex.mapBifunctorMap (𝟙 C) τ (curriedTensor M) (.up ℤ) ≫
        HomologicalComplex.mapBifunctorMap α (𝟙 L) (curriedTensor M) (.up ℤ) := by
  apply HomologicalComplex.hom_ext
  intro i
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q hpq
  simp [whisker_exchange_assoc, whiskerLeft_id]

end AdicTensorNaturality

section AdicCompletionDescent
attribute [local irreducible] completedAdicRing HasDerivedCategory.standard
variable (T : Scheme.{t}) (d : AdicCoefficientDatum A)

private local instance adicComparisonLocallyBijective :
    (ProEt.topology T).WEqualsLocallyBijective AddCommGrpCat.{t + 1} :=
  WeilConjectures.integralCoefficientAbLocallyBijective.{t, 0} T

private local instance adicComparisonMonoidal : MonoidalCategory (CompletedAdicModules T d) :=
  SheafOfModules.monoidalCategory.{t, t + 1, t + 1} (completedAdicCommRing T d)
private local instance adicComparisonTensorZero :
    (curriedTensor (CompletedAdicModules T d)).PreservesZeroMorphisms :=
  SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients
    (completedAdicCommRing T d)
private local instance adicComparisonTensorObjZero (M : CompletedAdicModules T d) :
    ((curriedTensor (CompletedAdicModules T d)).obj M).PreservesZeroMorphisms :=
  SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients
    (completedAdicCommRing T d) M
private local instance adicComparisonTensorAdditive :
    MonoidalPreadditive (CompletedAdicModules T d) :=
  SheafOfModules.tensorPreadditive.{t + 1, t, t + 1} (completedAdicCommRing T d)

private local instance adicComparisonCoproducts :
    HasColimitsOfSize.{0, 0} (CompletedAdicModules T d) :=
  @SheafOfModules.instHasColimitsOfSizeOfPresheafOfModulesObjFunctorOppositeRingCatIsSheaf.{
    0, 0, t + 1, t, t + 1, t + 1} _ _ _ (completedAdicRing T d)
    (inferInstance : HasWeakSheafify (ProEt.topology T) AddCommGrpCat.{t + 1})
    (WeilConjectures.integralCoefficientAbLocallyBijective.{t, 0} T)
    (inferInstance : HasColimitsOfSize.{0, 0}
      (_root_.PresheafOfModules.{t + 1} (completedAdicRing T d).obj))

private theorem adicKoszulPower_flat (r : ℕ) (a : Fin r → A) (m : ℕ) (i : ℤ) :
    Module.Flat (ULift.{t + 1} A) ((koszulPower A r a m).X i) := by
  classical
  have (n : ℕ) : CategoryTheory.Projective
      ((ExteriorAlgebra.koszulComplex (ULift.{t + 1} A) r
        (fun j ↦ ULift.up (a j ^ (m + 1)))).X n) := by
    change CategoryTheory.Projective
      (ModuleCat.of (ULift.{t + 1} A) (⋀[ULift.{t + 1} A]^n (Fin r →₀ ULift.{t + 1} A)))
    infer_instance
  have : CategoryTheory.Projective ((koszulPower A r a m).X i) := by
    change CategoryTheory.Projective
      (((ExteriorAlgebra.koszulComplex (ULift.{t + 1} A) r
        (fun j ↦ ULift.up (a j ^ (m + 1)))).extend ComplexShape.embeddingDownNat).X i)
    infer_instance
  have : Module.Projective (ULift.{t + 1} A) ((koszulPower A r a m).X i) :=
    ModuleCat.projective_of_module_projective _
  infer_instance

private theorem adicKoszulPower_bounded (r : ℕ) (a : Fin r → A) (m : ℕ) :
    (koszulPower A r a m).IsStrictlyLE 0 := by
  apply (CochainComplex.isStrictlyLE_iff _ 0).2
  intro i hi
  apply HomologicalComplex.isZero_extend_X
  intro n
  change -(n : ℤ) ≠ i
  omega

private theorem adicKoszulPowerSheaf_kflat (r : ℕ) (a : Fin r → A) (m : ℕ) :
    CochainComplex.IsKFlatIndependentCoefficients.{t + 1, t, t + 1}
      (J := ProEt.topology T)
      (R := completedAdicCommRing T d) (completedAdicKoszul T d r a m) := by
  let P := koszulPower A r a m
  have : P.IsStrictlyLE 0 := adicKoszulPower_bounded r a m
  have hf (i : ℤ) : Module.Flat (ULift.{t + 1} A) (P.X i) := adicKoszulPower_flat r a m i
  have hb : (HomologicalComplex.quasiIso (ModuleCat.{t + 1} (ULift.{t + 1} A))
      (.up ℤ)).kFlat P :=
    CochainComplex.kFlat_of_isStrictlyLE_of_flat P 0
      (fun i ↦ (ModuleCat.flat_iff_flat (P.X i)).2 (hf i))
  have hk : CochainComplex.IsKFlatIndependentCoefficients.{t + 1, t, t + 1}
      (J := ProEt.topology T) (R := adicConstantRing T A)
      (koszulPowerSheaf T A r a m) :=
    CategoryTheory.isKFlat_constantModule.{t + 1, t} (ProEt.topology T)
      (ULift.{t + 1} A) P ⟨fun s hs ↦ hb.1 s hs, fun s hs ↦ hb.2 s hs⟩ hf
  let hE : (completedAdicScalarExtension T d).Additive :=
    completedAdicScalarExtension_additive T d
  exact SheafOfModules.changeOfRings_isKFlat_independentCoefficients.{t + 1, t, t + 1}
    (R := adicConstantRing T A) (S := completedAdicCommRing T d)
    (completedAdicScalar T d)
    (koszulPowerSheaf T A r a m) (completedAdicScalarExtension T d)
    (completedAdicScalarExtensionData T d).choose_spec.choose
    (fun g ↦ (completedAdicScalarExtensionData T d).choose_spec.choose_spec.choose g) hk

private def adicCompletedTensorMap (r : ℕ) (f : Fin r → A)
    {C D : CochainComplex (CompletedAdicModules T d) ℤ} (α : C ⟶ D) (m : ℕ) :
    completedAdicKoszulTensor T d r f C m ⟶ completedAdicKoszulTensor T d r f D m :=
  HomologicalComplex.mapBifunctorMap
    (C₁ := CompletedAdicModules T d) (C₂ := CompletedAdicModules T d)
    (D := CompletedAdicModules T d) α (𝟙 (completedAdicKoszul T d r f m))
    (curriedTensor (CompletedAdicModules T d)) (.up ℤ)

private theorem adicCompletedTensorMap_id (r : ℕ) (f : Fin r → A)
    (C : CochainComplex (CompletedAdicModules T d) ℤ) (m : ℕ) :
    adicCompletedTensorMap T d r f (𝟙 C) m = 𝟙 _ := by
  exact adicTensorMap_id (M := CompletedAdicModules T d) C (completedAdicKoszul T d r f m)

private theorem adicCompletedTensorMap_comp (r : ℕ) (f : Fin r → A)
    {C D E : CochainComplex (CompletedAdicModules T d) ℤ}
    (α : C ⟶ D) (β : D ⟶ E) (m : ℕ) :
    adicCompletedTensorMap T d r f (α ≫ β) m =
      adicCompletedTensorMap T d r f α m ≫ adicCompletedTensorMap T d r f β m := by
  exact adicTensorMap_comp (M := CompletedAdicModules T d) C D (completedAdicKoszul T d r f m) E α β

private def adicCompletedProductMap (r : ℕ) (f : Fin r → A)
    {C D : CochainComplex (CompletedAdicModules T d) ℤ} (α : C ⟶ D) :
    completedAdicKoszulProduct T d r f C ⟶ completedAdicKoszulProduct T d r f D :=
  Pi.lift (fun m ↦ Pi.π (completedAdicKoszulTensor T d r f C) m ≫
    adicCompletedTensorMap T d r f α m)

private theorem adicCompletedProductMap_id (r : ℕ) (f : Fin r → A)
    (C : CochainComplex (CompletedAdicModules T d) ℤ) :
    adicCompletedProductMap T d r f (𝟙 C) = 𝟙 _ := by
  apply Pi.hom_ext
  intro n
  simp [adicCompletedProductMap, adicCompletedTensorMap_id]

private theorem adicCompletedProductMap_comp (r : ℕ) (f : Fin r → A)
    {C D E : CochainComplex (CompletedAdicModules T d) ℤ} (α : C ⟶ D) (β : D ⟶ E) :
    adicCompletedProductMap T d r f (α ≫ β) =
      adicCompletedProductMap T d r f α ≫ adicCompletedProductMap T d r f β := by
  apply Pi.hom_ext
  intro n
  simp [adicCompletedProductMap, adicCompletedTensorMap_comp, Category.assoc]

private theorem adicCompletedTensor_transition_natural (r : ℕ) (f : Fin r → A)
    {C D : CochainComplex (CompletedAdicModules T d) ℤ} (α : C ⟶ D) (m : ℕ) :
    adicCompletedTensorMap T d r f α (m + 1) ≫ completedAdicKoszulTensorStep T d r f D m =
      completedAdicKoszulTensorStep T d r f C m ≫ adicCompletedTensorMap T d r f α m := by
  exact adicTensorMap_exchange (M := CompletedAdicModules T d) C D
    (completedAdicKoszul T d r f (m + 1))
    (completedAdicKoszul T d r f m) α _

private theorem adicCompletedProduct_shift_natural (r : ℕ) (f : Fin r → A)
    {C D : CochainComplex (CompletedAdicModules T d) ℤ} (α : C ⟶ D) :
    completedAdicKoszulOneSubShift T d r f C ≫ adicCompletedProductMap T d r f α =
      adicCompletedProductMap T d r f α ≫ completedAdicKoszulOneSubShift T d r f D := by
  dsimp only [completedAdicKoszulProduct]
  apply Pi.hom_ext
  intro n
  simp only [completedAdicKoszulOneSubShift, adicCompletedProductMap, Preadditive.sub_comp,
    Preadditive.comp_sub, Category.assoc, Pi.lift_π_assoc, Pi.lift_π,
    Category.id_comp, Category.comp_id]
  rw [adicCompletedTensor_transition_natural]

private abbrev adicCompletedArrowFunctor (r : ℕ) (f : Fin r → A) :
    CochainComplex (CompletedAdicModules T d) ℤ ⥤
      Arrow (CochainComplex (CompletedAdicModules T d) ℤ) where
  obj C := Arrow.mk (-completedAdicKoszulOneSubShift T d r f C)
  map α := Arrow.homMk (adicCompletedProductMap T d r f α) (adicCompletedProductMap T d r f α)
    (by simpa only [Arrow.mk_hom, Preadditive.neg_comp, Preadditive.comp_neg] using
      congrArg Neg.neg (adicCompletedProduct_shift_natural T d r f α).symm)
  map_id C := by
    apply Arrow.hom_ext <;> exact adicCompletedProductMap_id T d r f C
  map_comp α β := by
    apply Arrow.hom_ext <;> exact adicCompletedProductMap_comp T d r f α β

private abbrev adicCompletedConeFunctor (M : Type*) [Category* M] [Abelian M] :
    Arrow (CochainComplex M ℤ) ⥤ CochainComplex M ℤ where
  obj a := CochainComplex.mappingCone a.hom
  map α := CochainComplex.mappingCone.map _ _ α.left α.right α.w.symm
  map_id a := CochainComplex.mappingCone.map_id a.hom
  map_comp α β := CochainComplex.mappingCone.map_comp _ _ _ _ _ α.w.symm _ _ β.w.symm

private abbrev adicCompletedFiberFunctor (r : ℕ) (f : Fin r → A) :
    CochainComplex (CompletedAdicModules T d) ℤ ⥤ CochainComplex (CompletedAdicModules T d) ℤ :=
  adicCompletedArrowFunctor T d r f ⋙ adicCompletedConeFunctor (CompletedAdicModules T d) ⋙
    shiftFunctor _ (-1 : ℤ)

private theorem adicCompletedTensorUnit_natural (r : ℕ) (f : Fin r → A)
    {C D : CochainComplex (CompletedAdicModules T d) ℤ} (α : C ⟶ D) (m : ℕ) :
    α ≫ completedAdicKoszulTensorUnit T d r f D m =
      completedAdicKoszulTensorUnit T d r f C m ≫ adicCompletedTensorMap T d r f α m := by
  apply HomologicalComplex.hom_ext
  intro p
  exact adicTensorUnit_natural (M := CompletedAdicModules T d) C D (completedAdicKoszul T d r f m)
    (completedAdicKoszulUnitZero T d r f m) α p

private theorem adicCompletedProductUnit_natural (r : ℕ) (f : Fin r → A)
    {C D : CochainComplex (CompletedAdicModules T d) ℤ} (α : C ⟶ D) :
    α ≫ completedAdicKoszulProductUnit T d r f D =
      completedAdicKoszulProductUnit T d r f C ≫ adicCompletedProductMap T d r f α := by
  apply Pi.hom_ext
  intro m
  simp only [completedAdicKoszulProductUnit, adicCompletedProductMap, Category.assoc,
    Pi.lift_π, Pi.lift_π_assoc]
  exact adicCompletedTensorUnit_natural T d r f α m

private theorem adicCompletedTensorMap_quasiIso (r : ℕ) (f : Fin r → A)
    {C D : CochainComplex (CompletedAdicModules T d) ℤ} (α : C ⟶ D)
    [QuasiIso α] (m : ℕ) : QuasiIso (adicCompletedTensorMap T d r f α m) := by
  have hc := (CochainComplex.mappingCone.quasiIso_iff_acyclic α).1 inferInstance
  have ht := adicKoszulPowerSheaf_kflat T d r f m
    (CochainComplex.mappingCone α) hc
  apply (CochainComplex.mappingCone.quasiIso_iff_acyclic _).2
  intro i
  exact (ht i).of_iso (CochainComplex.mapBifunctorMappingCone₁Iso α
    (completedAdicKoszul T d r f m) (curriedTensor (CompletedAdicModules T d)))

private theorem adicProductMap_quasiIso (M : Type*) [Category* M] [Abelian M]
    [HasCountableProducts M]
    (hprod : ∀ (F G : ℕ → M) (a : ∀ n, F n ⟶ G n),
      (∀ n, Epi (a n)) → Epi (Limits.Pi.map a))
    {C D : ℕ → CochainComplex M ℤ} (α : ∀ n, C n ⟶ D n)
    [∀ n, QuasiIso (α n)] :
    QuasiIso (Pi.lift (fun n ↦ Pi.π C n ≫ α n)) := by
  have : (lim (J := Discrete ℕ) (C := M)).PreservesEpimorphisms :=
    { preserves := by
        intro F G a ha
        have := hprod (fun n ↦ F.obj ⟨n⟩) (fun n ↦ G.obj ⟨n⟩)
          (fun n ↦ a.app ⟨n⟩) (fun n ↦ inferInstance)
        have he : lim.map a = (Pi.isoLimit _).inv ≫
            Limits.Pi.map (fun n ↦ a.app ⟨n⟩) ≫ (Pi.isoLimit _).hom := by
          apply limit.hom_ext
          intro ⟨n⟩
          simp
        rw [he]
        infer_instance }
  have := hasExactLimitsOfShape_of_preservesEpi M (Discrete ℕ)
  let a : Discrete.functor C ⟶ Discrete.functor D :=
    Discrete.natTrans (fun n ↦ α n.as)
  have (n : Discrete ℕ) : QuasiIso (a.app n) := by
    change QuasiIso (α n.as)
    infer_instance
  exact HomologicalComplex.quasiIso_limMap a

private theorem adicCompletedProductMap_quasiIso (r : ℕ) (f : Fin r → A)
    {C D : CochainComplex (CompletedAdicModules T d) ℤ} (α : C ⟶ D)
    [QuasiIso α] : QuasiIso (adicCompletedProductMap T d r f α) := by
  have (n : ℕ) : QuasiIso (adicCompletedTensorMap T d r f α n) :=
    adicCompletedTensorMap_quasiIso T d r f α n
  exact adicProductMap_quasiIso (CompletedAdicModules T d)
    ((ProEt.countableProducts_exact.{t, t, 0} T (completedAdicCommRing T d)).2.2 ℕ)
    (fun n ↦ adicCompletedTensorMap T d r f α n)

private theorem adicCompletedConeMap_quasiIso (M : Type*) [Category* M] [Abelian M]
    [HasDerivedCategory M] {a b : Arrow (CochainComplex M ℤ)} (α : a ⟶ b)
    [QuasiIso α.left] [QuasiIso α.right] :
    QuasiIso ((adicCompletedConeFunctor M).map α) := by
  let τ := DerivedCategory.Q.mapTriangle.map
    (CochainComplex.mappingCone.triangleMap a.hom b.hom α.left α.right α.w.symm)
  have h₁ : IsIso τ.hom₁ :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso M α.left).2 inferInstance
  have h₂ : IsIso τ.hom₂ :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso M α.right).2 inferInstance
  have := Pretriangulated.isIso₃_of_isIso₁₂ τ
    (DerivedCategory.mappingCone_triangle_distinguished a.hom)
    (DerivedCategory.mappingCone_triangle_distinguished b.hom) h₁ h₂
  exact (DerivedCategory.isIso_Q_map_iff_quasiIso M _).1 this

private theorem adicCompletedFiberMap_quasiIso (r : ℕ) (f : Fin r → A)
    {C D : CochainComplex (CompletedAdicModules T d) ℤ} (α : C ⟶ D)
    [QuasiIso α] : QuasiIso ((adicCompletedFiberFunctor T d r f).map α) := by
  have := adicCompletedProductMap_quasiIso T d r f α
  have : QuasiIso (((adicCompletedArrowFunctor T d r f).map α).left) :=
    adicCompletedProductMap_quasiIso T d r f α
  have : QuasiIso (((adicCompletedArrowFunctor T d r f).map α).right) :=
    adicCompletedProductMap_quasiIso T d r f α
  have := adicCompletedConeMap_quasiIso (CompletedAdicModules T d)
    ((adicCompletedArrowFunctor T d r f).map α)
  exact (CochainComplex.quasiIso_shift_iff
    ((adicCompletedConeFunctor _).map ((adicCompletedArrowFunctor T d r f).map α)) (-1)).2 this

private theorem adicCompletedFiberUnit_natural (r : ℕ) (f : Fin r → A)
    {C D : CochainComplex (CompletedAdicModules T d) ℤ} (α : C ⟶ D) :
    α ≫ completedAdicKoszulUnitComplex T d r f D =
      completedAdicKoszulUnitComplex T d r f C ≫ (adicCompletedFiberFunctor T d r f).map α := by
  apply HomologicalComplex.hom_ext
  intro p
  have hi :
      HomologicalComplex.homotopyCofiber.inlX (-completedAdicKoszulOneSubShift T d r f C)
        p (p + (-1)) (by change p + (-1) + 1 = p; omega) ≫
          ((adicCompletedFiberFunctor T d r f).map α).f p =
      (adicCompletedProductMap T d r f α).f p ≫
        HomologicalComplex.homotopyCofiber.inlX (-completedAdicKoszulOneSubShift T d r f D)
          p (p + (-1)) (by change p + (-1) + 1 = p; omega) := by
    change (CochainComplex.mappingCocone.inl
      (-completedAdicKoszulOneSubShift T d r f C)).v p p (add_zero p) ≫ _ =
      _ ≫ (CochainComplex.mappingCocone.inl
        (-completedAdicKoszulOneSubShift T d r f D)).v p p (add_zero p)
    simp [adicCompletedFiberFunctor, adicCompletedConeFunctor, adicCompletedArrowFunctor,
      CochainComplex.mappingCocone.inl,
      CochainComplex.HomComplex.Cochain.rightShift_v _ _ _ _ _ _ _ _ rfl,
      CochainComplex.mappingCone.map]
  change α.f p ≫ (completedAdicKoszulProductUnit T d r f D).f p ≫ _ =
    ((completedAdicKoszulProductUnit T d r f C).f p ≫ _) ≫ _
  rw [Category.assoc, hi, ← Category.assoc]
  exact congrArg (fun z : C ⟶ completedAdicKoszulProduct T d r f D ↦ z.f p ≫
    HomologicalComplex.homotopyCofiber.inlX (-completedAdicKoszulOneSubShift T d r f D)
      p (p + (-1)) (by change p + (-1) + 1 = p; omega))
    (adicCompletedProductUnit_natural T d r f α)

private theorem adicCompletedLocalization (M : Type*) [Category* M] [Abelian M]
    [HasDerivedCategory M] (G : CochainComplex M ℤ ⥤ CochainComplex M ℤ)
    (τ : 𝟭 _ ⟶ G)
    (hG : ∀ {C D : CochainComplex M ℤ} (α : C ⟶ D),
      QuasiIso α → QuasiIso (G.map α)) :
    ∃ (F : DerivedCategory M ⥤ DerivedCategory M) (η : 𝟭 _ ⟶ F),
      ∀ C : CochainComplex M ℤ,
        ∃ e : F.obj (DerivedCategory.Q.obj C) ≅ DerivedCategory.Q.obj (G.obj C),
          η.app (DerivedCategory.Q.obj C) ≫ e.hom = DerivedCategory.Q.map (τ.app C) := by
  let Q := DerivedCategory.Q (C := M)
  let W := HomologicalComplex.quasiIso M (.up ℤ)
  have h : W.IsInvertedBy (G ⋙ Q) := by
    intro C D α hα
    exact (DerivedCategory.isIso_Q_map_iff_quasiIso M (G.map α)).2 (hG α hα)
  let F := Localization.lift (G ⋙ Q) h Q
  let σ : Q ⟶ G ⋙ Q :=
    { app := fun C ↦ Q.map (τ.app C)
      naturality := by
        intro C D α
        simp only [Functor.comp_map, ← Q.map_comp]
        exact congrArg Q.map (τ.naturality α) }
  let : Localization.Lifting Q W Q (𝟭 _) := ⟨Functor.rightUnitor Q⟩
  let η := Localization.liftNatTrans Q W Q (G ⋙ Q) (𝟭 _) F σ
  refine ⟨F, η, fun C ↦ ⟨(Localization.fac (G ⋙ Q) h Q).app C, ?_⟩⟩
  dsimp only [η]
  rw [Localization.liftNatTrans_app]
  change ((𝟙 _) ≫ σ.app C ≫ (Localization.fac (G ⋙ Q) h Q).inv.app C) ≫
    (Localization.fac (G ⋙ Q) h Q).hom.app C = _
  rw [Category.assoc, Category.assoc, Iso.inv_hom_id_app,
    Category.comp_id, Category.id_comp]

/-- The explicit completion and its unit are independent of the complex representative.
Source: blueprint def-weil-pbc-intrinsic-completion
(blueprint: def-weil-pbc-intrinsic-completion).
Proof: the Koszul factors are bounded finite free complexes, so total tensor with them
preserves quasi-isomorphisms. Exact countable products on the pro-etale site
(lem-weil-proetale-countable-products-exact) preserve their levelwise quasi-isomorphisms;
the resulting maps of mapping fibres are quasi-isomorphisms by the cone triangle.
The tensor units commute with all these maps. Localization therefore gives the asserted
unit-compatible isomorphism for any representative and its identification with K. -/
theorem completedAdicIntrinsicCompletion_comparison (T : Scheme.{t}) (d : AdicCoefficientDatum A)
    (r : ℕ) (a : Fin r → A) (K : DerivedCategory (CompletedAdicModules T d))
    (C : CochainComplex (CompletedAdicModules T d) ℤ) (e : DerivedCategory.Q.obj C ≅ K) :
    ∃ j : DerivedCategory.Q.obj (completedAdicKoszulFibre T d r a C) ≅
        completedAdicIntrinsicCompletion T d r a K,
      DerivedCategory.Q.map (completedAdicKoszulUnitComplex T d r a C) ≫ j.hom =
        e.hom ≫ completedAdicIntrinsicUnit T d r a K := by
  let G := adicCompletedFiberFunctor T d r a
  let τ : 𝟭 _ ⟶ G :=
    { app := completedAdicKoszulUnitComplex T d r a
      naturality := fun _ _ α ↦ adicCompletedFiberUnit_natural T d r a α }
  obtain ⟨F, η, hη⟩ := adicCompletedLocalization (CompletedAdicModules T d) G τ
    (by
      intro C D α hα
      let := hα
      exact adicCompletedFiberMap_quasiIso T d r a α)
  let P := DerivedCategory.Q.objPreimage K
  let eP := DerivedCategory.Q.objObjPreimageIso K
  obtain ⟨jC, hjC⟩ := hη C
  obtain ⟨jP, hjP⟩ := hη P
  refine ⟨jC.symm ≪≫ F.mapIso e ≪≫ F.mapIso eP.symm ≪≫ jP, ?_⟩
  have hC : DerivedCategory.Q.map (τ.app C) ≫ jC.inv = η.app (DerivedCategory.Q.obj C) := by
    rw [← hjC, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  change DerivedCategory.Q.map (τ.app C) ≫
    jC.inv ≫ F.map e.hom ≫ F.map eP.inv ≫ jP.hom =
      e.hom ≫ eP.inv ≫ DerivedCategory.Q.map (τ.app P)
  rw [← Category.assoc _ jC.inv, hC, ← F.map_comp_assoc,
    ← η.naturality_assoc (e.hom ≫ eP.inv), hjP]
  simp only [Functor.id_map, Category.assoc]

end AdicCompletionDescent


end AlgebraicGeometry.Scheme
