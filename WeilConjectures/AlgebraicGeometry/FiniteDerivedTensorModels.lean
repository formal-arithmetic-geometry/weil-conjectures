/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.RingedDerivedComparisonData
public import WeilConjectures.AlgebraicGeometry.PullbackTensorCanonicalShiftUnit
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
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
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

/-! # Comparing the two presentations of normalized tensor models

Source: Stacks 07A4, 0G7E and 03EL. These are explicit identifications of the
ordinary comparison, its single-complex unit and the recorded K-flat tensor model.
(blueprint: lem-pur-finite-derived-tensor-model-bridge).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option backward.defeqAttrib.useBackward false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u w
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor MonoidalCategory
open CategoryTheory.CochainPullback CategoryTheory.RingedDerivedComparisons
open WeilConjectures

attribute [-instance] CategoryTheory.hasSheafCompose_of_preservesMulticospan
attribute [local instance 100000] HomologicalComplex.monoidalCategoryStruct
attribute [local irreducible] CommRingCat.hasForgetToRingCat sheafCompose
  CommRingCat.instConcreteCategoryRingHomCarrier RingCat.instConcreteCategoryRingHomCarrier
  SheafOfModules.monoidalCategory SheafOfModules.instPreadditive
  HomologicalComplex.instPreadditive SheafOfModules.siteSheafTensorRight
  DerivedCategory instCategoryDerivedCategory
  HomologicalComplex₂.total CategoryTheory.CochainPullback.comparison
  HomologicalComplex.single

namespace CategoryTheory.FiniteDerivedTensorModels

/-- The homotopy and cochain comparison maps have the same components.
Source: Stacks 07A4, 0G7E and 03EL.
(blueprint: lem-pur-finite-derived-tensor-model-bridge). -/
theorem complexComparison_eq_component
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
    (F : A ⥤ B) [F.Additive] (L : DerivedCategory A ⥤ DerivedCategory B)
    (ε : DerivedCategory.Qh ⋙ L ⟶ F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (M : CochainComplex A ℤ) :
    derivedPullbackComplexComparison F L ε M =
      ε.app ((HomotopyCategory.quotient A (.up ℤ)).obj M) := by
  have hi : L.map ((DerivedCategory.quotientCompQhIso A).inv.app M) = 𝟙 _ := by
    have h : (DerivedCategory.quotientCompQhIso A).inv.app M = 𝟙 _ := by
      with_unfolding_all rfl
    exact (congrArg L.map h).trans (L.map_id _)
  have hj : DerivedCategory.Qh.map
      ((F.mapHomotopyCategoryFactors (.up ℤ)).hom.app M) = 𝟙 _ := by
    have h : (F.mapHomotopyCategoryFactors (.up ℤ)).hom.app M = 𝟙 _ := by
      with_unfolding_all rfl
    exact (congrArg DerivedCategory.Qh.map h).trans (DerivedCategory.Qh.map_id _)
  have hk : (DerivedCategory.quotientCompQhIso B).hom.app
      ((F.mapHomologicalComplex (.up ℤ)).obj M) = 𝟙 _ := by
    with_unfolding_all rfl
  unfold derivedPullbackComplexComparison
  rw [hi, hj, hk]
  with_unfolding_all
    change (𝟙 _ ≫ ε.app ((HomotopyCategory.quotient A (.up ℤ)).obj M) ≫ 𝟙 _ ≫ 𝟙 _) =
      ε.app ((HomotopyCategory.quotient A (.up ℤ)).obj M)
  simp only [Category.id_comp, Category.comp_id]

/-- The ordinary comparison with its identical insertion and tensor maps.
Source: Stacks 07A4, 0G7E and 03EL.
(blueprint: lem-pur-finite-derived-tensor-model-bridge). -/
def legacyComparison {X Y : Site.{u, w}}
    (f : RingedPullback.{u, u, u, u, u} Y.A X.A) (k : Comparison f) :
    SheafOfModules.CanonicalRingedTensorComparison Y.A X.A f.RI f.uInv f.I
      f.coefficient f.L f.hobj where
  q := k.q
  q_one := k.q_one
  mu := k.mu
  naturality := k.naturality
  pure := k.pure

/-- The independent coefficient and native flat representative predicates agree.
Source: Stacks 07A4, 0G7E and 03EL.
(blueprint: lem-pur-finite-derived-tensor-model-bridge). -/
theorem resolving_native (X : Site.{u, w})
    (P : CochainComplex X.modules ℤ) :
    (CochainComplex.IsKFlatIndependentCoefficients (J := X.J) (R := X.A) P ∧
      ∀ n : ℤ, SheafOfModules.IsFlatOnSite (J := X.J) (R := X.A) (P.X n)) ↔
        X.corner.mateFlat P := by
  constructor
  · intro h
    refine ⟨(CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat P).1 h.1, ?_⟩
    intro n
    exact (exactFunctor _ _).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso X.A (P.X n)) (h.2 n)
  · intro h
    refine ⟨(CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat P).2 h.1, ?_⟩
    intro n
    exact (exactFunctor _ _).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso X.A (P.X n)).symm (h.2 n)

/-- Restrict the recorded tensor model to flat-term K-flat complexes.
Source: Stacks 07A4, 0G7E and 03EL.
(blueprint: lem-pur-finite-derived-tensor-model-bridge). -/
def canonical_model (X : Site.{u, w}) : SheafOfModules.RingedTensorModel X.corner :=
  let ι : X.corner.mateFlat.FullSubcategory ⥤
      ObjectProperty.FullSubcategory
        (CochainComplex.IsKFlatIndependentCoefficients (J := X.J) (R := X.A)) := {
    obj := fun P ↦ ⟨P.obj, ((resolving_native X P.obj).2 P.property).1⟩
    map := fun a ↦ ObjectProperty.homMk a.hom }
  { representative := isoWhiskerLeft (ι.prod ι) X.model.comparison }

/-- The restricted model retains the recorded representative components.
Source: Stacks 07A4, 0G7E and 03EL.
(blueprint: lem-pur-finite-derived-tensor-model-bridge). -/
theorem canonical_model_eq (X : Site.{u, w})
    (P Q : CochainComplex X.modules ℤ) (hp : X.corner.mateFlat P)
    (hq : X.corner.mateFlat Q) :
    (canonical_model X).representative.hom.app (⟨P, hp⟩, ⟨Q, hq⟩) =
      (X.model.iso X.J X.A X.closed P Q
      ((resolving_native X P).2 hp).1 ((resolving_native X Q).2 hq).1).hom := rfl

/-- The legacy total comparison is the inverse cochain pullback comparison.
Source: Stacks 07A4, 0G7E and 03EL.
(blueprint: lem-pur-finite-derived-tensor-model-bridge). -/
theorem legacy_comparison_eq {X Y : Site.{u, w}}
    (f : RingedPullback.{u, u, u, u, u} Y.A X.A) (k : Comparison f)
    (P Q : CochainComplex Y.modules ℤ) :
    ((legacyComparison f k).totalIso Y.A X.A f.RI f.uInv f.I f.coefficient f.L f.hobj
      f.V f.moduleAdj P Q).inv = (CochainPullback.comparison f k P Q).hom := by
  unfold CochainPullback.comparison
  congr 1

section LegacyUnit
attribute [local semireducible] SheafOfModules.monoidalCategory

/-- The ordinary normalized unit has the specified single-complex comparison.
Source: Stacks 07A4, 0G7E and 03EL.
(blueprint: lem-pur-finite-derived-tensor-model-bridge). -/
theorem unit_presentation {X Y : Site.{u, w}}
    (f : RingedPullback.{u, u, u, u, u} Y.A X.A) (k : Comparison f) :
    ∃ j : f.L.obj (SheafOfModules.unit Y.ring) ≅ SheafOfModules.unit X.ring,
      (∀ M : Y.modules,
        ((legacyComparison f k).mu M (SheafOfModules.unit Y.ring)).hom ≫
            (SheafOfModules.monoidalCategory X.A).tensorHom (𝟙 _) j.hom ≫
            ((SheafOfModules.monoidalCategory X.A).rightUnitor (f.L.obj M)).hom =
          f.L.map ((SheafOfModules.monoidalCategory Y.A).rightUnitor M).hom) ∧
      (HomologicalComplex.singleMapHomologicalComplex f.L (.up ℤ) 0).hom.app
          (SheafOfModules.unit Y.ring) ≫
        (CochainComplex.singleFunctor X.modules 0).map j.hom = (unit f k).hom := by
  refine ⟨moduleUnit f k, ?_, ?_⟩
  · exact (Classical.choose_spec
      (SheafOfModules.CochainTensorComparison.canonicalRingedTensorComparison_unit
        Y.A X.A f.RI f.uInv f.I f.coefficient f.L f.hobj f.hmap k)).1
  · rfl

end LegacyUnit




end CategoryTheory.FiniteDerivedTensorModels
