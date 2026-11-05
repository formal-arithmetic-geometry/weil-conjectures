/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Ringed.Slice.RingedSliceEvaluationModels
public import Mathlib.Algebra.Homology.BifunctorShift
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
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
import all WeilConjectures.Algebra.Homology.KFlatFixedTensor.KFlatFixedTensorTriangulatedSupplement

/-! # Integer shifts of the normalized slice tensor comparison

Source: Stacks Project, more-algebra.tex, Tag 0FNH, item-shift-tensor;
sites-cohomology.tex, Tags 06YS, 06YU and 07A4. The slice squares and their
representative-independent descent are the agent-written refinement in the DAG.
(blueprint: lem-weil-pbc-slice-tensor-integer-shift-compatibility).
-/

@[expose] public noncomputable section

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.checkUnivs false
set_option Elab.async true
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe c v u w w' a b

open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures
open MonoidalCategory

namespace CategoryTheory

attribute [local instance 1000001] cachedCompose

@[no_expose] private def tensor_shifts_data {D : Type*} [Category D] [Preadditive D]
    (F : D ⥤ D ⥤ D) [F.Additive] [∀ X, (F.obj X).Additive]
    [∀ (P Q : CochainComplex D ℤ), CochainComplex.HasMapBifunctor P Q F] :
    TensorIntegerShiftComparisons (Functor.uncurry.obj F.map₂CochainComplex) :=
  ⟨tensorFirstShiftIso F.map₂CochainComplex, tensorSecondShiftIso F.map₂CochainComplex⟩

attribute [local irreducible] tensor_shifts_data

attribute [local irreducible] SheafOfModules.monoidalCategory
  derivedInternalHomOfUniverses CoefficientClosedStructure.tensor
  Functor.mapHomologicalComplexUpToQuasiIso
  Functor.mapHomologicalComplexUpToQuasiIsoFactors

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max c v u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v u}]
  (A : Sheaf J CommRingCat.{max c v u})

set_option hygiene false in
set_option quotPrecheck false in
local notation "Mod" => SheafOfModules.{max c v u}
  ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj A)

attribute [local irreducible] coefficientTotalTensor coefficientTensorGenerator
  SheafOfModules.forget SheafOfModules.instPreadditive
  CochainComplex.IsKFlatIndependentCoefficients
  SheafOfModules.IsFlatOnSite

variable [HasDerivedCategory.{w} (SheafOfModules.{max c v u} ((sheafCompose J
    (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj A))]

end CategoryTheory
