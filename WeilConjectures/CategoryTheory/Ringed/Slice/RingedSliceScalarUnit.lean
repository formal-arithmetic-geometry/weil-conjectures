/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.Ringed.Slice.RingedSliceEvaluationModels
public import WeilConjectures.CategoryTheory.Ringed.RingedDerivedClosedSymmetricMonoidal
import all WeilConjectures.CategoryTheory.Ringed.Tensor.RingedTensorConstraintCompletion
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
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
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Monoidal.Preadditive
import WeilConjectures.SecSmoothPurity.ModuleTensorGenerators
import WeilConjectures.SecSmoothPurity.CochainCoefficientArrowsSupplement

/-! # Scalar-unit coherence of normalized slice tensor comparison

Source: Stacks Project, Tags 07A4 and 0FPT
(blueprint: lem-sfb-ringed-slice-scalar-unit).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe c v r w w'
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open SheafOfModules WeilConjectures
namespace CategoryTheory
section TotalMapGeneric
universe a b
variable {A : Type a} [Category.{b} A] [Preadditive A]
  (G : A ⥤ A ⥤ A) [G.PreservesZeroMorphisms]
  [∀ X, (G.obj X).PreservesZeroMorphisms]
  [∀ P Q : CochainComplex A ℤ, HomologicalComplex.HasMapBifunctor P Q G (.up ℤ)]
end TotalMapGeneric
section Generic
universe a b x y
variable {D : Type a} [Category.{x} D] {E : Type b} [Category.{y} E]
  {H : Dᵒᵖ × D ⥤ D} {HU : Eᵒᵖ × E ⥤ E}
  (S : CoefficientClosedStructure H) (SU : CoefficientClosedStructure HU)
  {r : D ⥤ E} {K : Prop}
  (d : RingedSliceEvaluationComparisons H HU r S SU K)

end Generic
variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  (R : Sheaf J CommRingCat.{max c v r})
  [HasDerivedCategory.{w} (RingedTensorModules.{c, v, r} J R)]
  (U : C)
  [HasSheafify (J.over U) AddCommGrpCat.{max c v r}]
  [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  [HasDerivedCategory.{w'} (RingedTensorModules.{max c v, v, r} (J.over U) (R.over U))]
  (S : CoefficientClosedStructure (derivedInternalHomOfUniverses.{c, v, r, w} J R))
  (T : CoefficientTensorModels.{r, c, v, w} J R S)
  (s : @SymmetricCategory (DerivedCategory (RingedTensorModules.{c, v, r} J R))
    _ S.monoidal)
  (K : RingedDerivedTensorCoherence.{c, v, r, w} J R S T s)
  (SU : CoefficientClosedStructure
    (derivedInternalHomOfUniverses.{max c v, v, r, w'} (J.over U) (R.over U)))
  (TU : CoefficientTensorModels.{r, max c v, v, w'} (J.over U) (R.over U) SU)
  (sU : @SymmetricCategory
    (DerivedCategory (RingedTensorModules.{max c v, v, r} (J.over U) (R.over U)))
    _ SU.monoidal)
  (KU : RingedDerivedTensorCoherence.{max c v, v, r, w'} (J.over U) (R.over U) SU TU sU)
  (d : RingedSliceEvaluationComparisons (derivedInternalHomOfUniverses.{c, v, r, w} J R)
    (derivedInternalHomOfUniverses.{max c v, v, r, w'} (J.over U) (R.over U))
    (ringedSliceDerivedRestriction.{c, v, r, w, w'} J R U) S SU
    (RingedSliceFlatRestriction.{c, v, r} J R U))
  (hd : RingedSliceEvaluationNormalized.{c, v, r, w, w'} J R U S T SU TU d)

attribute [local irreducible] coefficientTotalTensor ringedSliceDerivedRestriction

end CategoryTheory
