/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.KFlatFixedTensor.KFlatFixedTensorTriangulatedSupplement
public import WeilConjectures.SecSmoothPurity.CochainPullbackTensorCoherenceSupplement
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import WeilConjectures.SecSmoothPurity.CochainComparisonMonoidalEquationsSupplement
import WeilConjectures.Algebra.Homology.KFlatTotalTensorModel.KFlatTotalTensorModelSupplement
import WeilConjectures.CategoryTheory.RightKanExtensionCoherentShift
import WeilConjectures.Algebra.Homology.PullbackTensorResolving.PullbackTensorResolvingComputation
import WeilConjectures.SecSmoothPurity.CochainPullbackTensorShift
import WeilConjectures.CategoryTheory.ProperBaseChange.ResolvingRepresentativeWhiskeringSupplement
import WeilConjectures.AlgebraicGeometry.TensorPullbackRepresentativeDescent
import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.CategoryTheory.AlgebraicInverseImage
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Sites.Whiskering
import Mathlib.CategoryTheory.Sites.Equivalence
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Homology.Additive
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
import WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
import Mathlib.CategoryTheory.Types.Basic
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import Mathlib.LinearAlgebra.TensorProduct.Vanishing
import Mathlib.RingTheory.TensorProduct.DirectLimitFG
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import Mathlib.CategoryTheory.Functor.EpiMono
import Mathlib.CategoryTheory.Limits.Types.Equalizers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
import WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Mathlib.CategoryTheory.Limits.Preserves.Limits
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.RingTheory.Flat.CategoryTheory
import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import Mathlib.CategoryTheory.Monoidal.Preadditive
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import Mathlib.CategoryTheory.ObjectProperty.Shift
import WeilConjectures.Mathlib.CategoryTheory.Shift.CommShift

/-! # Canonical shifts and action units of derived tensor pullback

Source: Stacks Project, sites-cohomology.tex, Tags 06YY and 07A4;
more-algebra.tex, Tag 0FNH, item-shift-tensor; sites-modules.tex, Tag 03EL.
(blueprint: lem-weil-pbc-pullback-tensor-canonical-shift-unit).

The helper predicates spell out the normalizations in this node. All tensors,
representative comparisons, cochain unitors and pullback maps are existing ones.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 512
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

-- Keep the signed-shift data folded when checking the resolving comparison squares.
attribute [local irreducible] CategoryTheory.CommShift₂Setup.int
attribute [local irreducible]
  CategoryTheory.Functor.instCommShiftCochainComplexIntObjMap₂CochainComplex
  CategoryTheory.Functor.instCommShiftCochainComplexIntObjFlipMap₂CochainComplex

universe uC vC uD vD r wR wS

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits MonoidalCategory
open CategoryTheory.CochainPullback hiding Modules
open SheafOfModules.KFlatFixedTensor

namespace SheafOfModules.PullbackTensorCanonical

attribute [-instance] CategoryTheory.hasSheafCompose_of_preservesMulticospan

attribute [local irreducible] SheafOfModules.monoidalCategory
attribute [local irreducible] siteDerivedTensorIndependentCoefficients
attribute [local irreducible] representativeIso
attribute [local irreducible] DerivedCategory.Q DerivedCategory.Qh
attribute [local irreducible] Functor.curry
attribute [local irreducible] Functor.mapHomologicalComplex
attribute [local irreducible] Functor.mapBifunctorHomologicalComplex
attribute [local irreducible] HomologicalComplex₂.total
attribute [local irreducible] CategoryTheory.CochainPullback.comparison
attribute [local irreducible] CategoryTheory.CochainPullback.unit
attribute [local irreducible] HomologicalComplex.single
attribute [local irreducible] HomologicalComplex.rightUnitor HomologicalComplex.leftUnitor

variable {C : Type uC} [Category.{vC} C] [EssentiallySmall.{r} C]
  {D : Type uD} [Category.{vD} D] [EssentiallySmall.{r} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  {R : Sheaf J CommRingCat.{r}} {S : Sheaf K CommRingCat.{r}}
  [HasDerivedCategory.{wR} (Modules.{uC, vC, r} R)]
  [HasDerivedCategory.{wS} (Modules.{uD, vD, r} S)]

local notation "MR" => Modules (C := C) (J := J) R
local notation "MS" => Modules (C := D) (J := K) S

attribute [local instance] canonicalDerivedTensorCommShift

local notation "TR" => canonicalDerivedTensor (C := C) (J := J) R
local notation "TS" => canonicalDerivedTensor (C := D) (J := K) S
local notation "tR₀" => totalTensor (C := C) (J := J) R
local notation "tS₀" => totalTensor (C := D) (J := K) S
local notation "DR" => derivedTensor (C := C) (J := J) R
local notation "DS" => derivedTensor (C := D) (J := K) S

variable (f : RingedPullback.{r, uC, vC, uD, vD} R S)
  (k : Comparison.{r, uC, vC, uD, vD} (J := J) (K := K) (R := R) (S := S) f)
  (L : DerivedCategory (Modules.{uC, vC, r} R) ⥤
    DerivedCategory (Modules.{uD, vD, r} S))

variable (epsilon : DerivedCategory.Q ⋙ L ⟶
  pull.{r, uC, vC, uD, vD} (J := J) (K := K) (R := R) (S := S) f ⋙ DerivedCategory.Q)

local notation "pullF" => pull (J := J) (K := K) (R := R) (S := S) f

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

attribute [local irreducible] canonicalDerivedTensor canonicalRepresentativeIso

omit [HasDerivedCategory.{wR} (Modules.{uC, vC, r} R)] in
@[no_expose] private abbrev resolvingProperty : ObjectProperty (CochainComplex (MR) ℤ) :=
  fun P ↦ P.IsKFlatIndependentCoefficients ∧
    ∀ n, IsFlatOnSite (J := J) (R := R) (P.X n)

set_option maxHeartbeats 1000000 in
-- Comparing the total-tensor and monoidal cochain presentations needs extra heartbeats.
set_option maxHeartbeats 1000000 in
-- Comparing the total-tensor and monoidal cochain presentations needs extra heartbeats.
set_option maxHeartbeats 1000000 in
-- Converting the published total tensor to its cochain monoidal presentation is costly.
set_option maxHeartbeats 1000000 in
-- Converting the published total tensor to its cochain monoidal presentation is costly.
attribute [local irreducible] HasCanonicalTensorShifts IsNormalized

-- The statement combines independently sized derived and total-tensor presentations.
end SheafOfModules.PullbackTensorCanonical

-- Restore Mathlib's original instance and priority for importing modules.
attribute [instance high] CategoryTheory.hasSheafCompose_of_preservesMulticospan
