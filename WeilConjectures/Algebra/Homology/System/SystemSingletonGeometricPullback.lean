/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
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
public import Mathlib.CategoryTheory.Limits.Final
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Homology.System.SystemOrdinarySingleExtension
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import WeilConjectures.Algebra.Homology.System.SystemRingedSequenceSite
public import WeilConjectures.Algebra.Homology.System.SystemEvaluationTopos
public import WeilConjectures.Algebra.Homology.System.SystemLevelLeftExtension
public import WeilConjectures.Algebra.Homology.System.SystemSingleDerivedExtension
public import WeilConjectures.Algebra.Homology.System.SystemSingleDerivedEvaluation
public import WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
public import WeilConjectures.CategoryTheory.AlgebraicInverseImage
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Sites.Whiskering
public import WeilConjectures.CategoryTheory.Sites.GeometricMorphism
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import WeilConjectures.CategoryTheory.Grothendieck.GrothendieckTopos
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import all WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all WeilConjectures.CategoryTheory.AlgebraicInverseImage
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.Algebra.Category.Grp.Limits
import all Mathlib.CategoryTheory.Sites.Whiskering
import all Mathlib.CategoryTheory.Sites.Equivalence
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import all Mathlib.CategoryTheory.Limits.ExactFunctor
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import all Mathlib.Algebra.Homology.HomologicalComplex
import all Mathlib.Algebra.Homology.Additive
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
import all WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
import all Mathlib.CategoryTheory.Types.Basic
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import all WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import all Mathlib.LinearAlgebra.TensorProduct.Vanishing
import all Mathlib.RingTheory.TensorProduct.DirectLimitFG
import all Mathlib.LinearAlgebra.TensorProduct.Finiteness
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import all Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import all WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
import all Mathlib.CategoryTheory.Sites.Sheaf
import all Mathlib.CategoryTheory.Sites.LocallyBijective
import all Mathlib.CategoryTheory.Sites.Limits
import all Mathlib.CategoryTheory.Adjunction.Limits
import all Mathlib.CategoryTheory.Limits.Types.Pullbacks
import all Mathlib.CategoryTheory.Functor.EpiMono
import all Mathlib.CategoryTheory.Limits.Types.Equalizers
import all Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
import all Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import all Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import all Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import all WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import all Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import all Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import all WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
import all WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all Mathlib.CategoryTheory.Sites.PreservesSheafification
import all Mathlib.CategoryTheory.Limits.Preserves.Limits
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import all Mathlib.RingTheory.Flat.CategoryTheory
import all Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import all Mathlib.Algebra.Homology.Embedding.CochainComplex
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import all Mathlib.Algebra.Category.Grp.AB
import all WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
import all WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import all Mathlib.CategoryTheory.Monoidal.Preadditive
import all WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import all Mathlib.CategoryTheory.Monoidal.Closed.Basic
import all WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.Algebra.Homology.System.SystemSingletonScalarExtension
import WeilConjectures.Algebra.Homology.System.SystemScalarCoherence

import WeilConjectures.Algebra.Homology.System.SystemGeometricDerivedLift

/-! # Geometric inverse image and derived singleton extension

Source: Zheng, Six Operations and Lefschetz--Verdier, Construction 4.1, printed p. 21,
and the base-change sentence before Lemma 4.10, printed p. 23
(blueprint: lem-pur-system-singleton-geometric-pullback).

The comparison includes its common flat-term K-flat model, transported tensor generators,
actual strict transitions, multiplication normalization and lower-singleton square.
The index `n : ℕ` represents positive level `n + 1`.
-/

set_option Elab.async false

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe uC vC uD vD w
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite
namespace SheafOfModules
open MonoidalCategory
open scoped TensorProduct ChangeOfRings

variable {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [EssentiallySmall.{w} C] [EssentiallySmall.{w} D]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [K.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]
  [K.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify K AddCommGrpCat.{w}]
  (BY : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) (BX : ℕᵒᵖ ⥤ Sheaf K CommRingCat.{w})
  (u : GeometricMorphism (Sheaf K (Type w)) (Sheaf J (Type w)))
  (I : ∀ n : ℕ, AlgebraicInverseImage u.inverse (BY.obj (op n)) (BX.obj (op n)))

/-- The ordinary underlying-set functor at a coefficient level, used only to express
transport of the actual semilinear transition. Source: Zheng, Construction 4.1, p. 21;
Stacks 03D2 (blueprint: lem-pur-system-singleton-geometric-pullback). -/
abbrev systemGeometricUnderlying (n : ℕ) :=
  toSheaf (derivedChangeRingIndependentCoefficients J (BY.obj (op n))) ⋙
    sheafCompose J (CategoryTheory.forget AddCommGrpCat.{w})

set_option genInjectivity false in
set_option genSizeOfSpec false in
/-- An exact termwise inverse image with its specified underlying transition maps.
The transition equation fixes the functor on systems, rather than merely specifying
unrelated level objects. All exactness fields are conclusions of the existence theorem.
Source: Zheng, Construction 4.1 and the sentence before Lemma 4.10; Stacks 03D2
(blueprint: lem-pur-system-singleton-geometric-pullback). -/
structure SystemGeometricInverseImageData where
  functor : StrictRingSystem BY ⥤ StrictRingSystem BX
  [additive : functor.Additive]
  [limits : PreservesFiniteLimits functor]
  [colimits : PreservesFiniteColimits functor]
  [levelAdditive : ∀ n : ℕ, (I n).modules.Additive]
  [levelLimits : ∀ n : ℕ, PreservesFiniteLimits (I n).modules]
  [levelColimits : ∀ n : ℕ, PreservesFiniteColimits (I n).modules]
  evaluation : ∀ n : ℕ,
    functor ⋙ systemEvaluation BX n ≅ systemEvaluation BY n ⋙ (I n).modules
  transition : ∀ (M : StrictRingSystem BY) {m n : ℕ} (h : m ≤ n),
    (systemGeometricUnderlying BX n).map ((evaluation n).hom.app M) ≫
        (I n).moduleUnderlying.hom.app (M.level n) ≫
        u.inverse.map ((systemGeometricUnderlying BY n).map (M.transition h)) ≫
        (I m).moduleUnderlying.inv.app (M.level m) =
      (systemGeometricUnderlying BX n).map ((functor.obj M).transition h) ≫
        (systemGeometricUnderlying BX m).map ((evaluation m).hom.app M)

attribute [instance] SystemGeometricInverseImageData.additive
  SystemGeometricInverseImageData.limits SystemGeometricInverseImageData.colimits

variable {BY BX u I}

/-- The specified level inverse image, retaining the exactness witness in its interface.
Source: Stacks 03D2 (blueprint: lem-pur-system-singleton-geometric-pullback). -/
def SystemGeometricInverseImageData.levelFunctor
    (_F : SystemGeometricInverseImageData BY BX u I) (n : ℕ) := (I n).modules

/-- Additivity of the level inverse image. Source: Stacks 03D2
(blueprint: lem-pur-system-singleton-geometric-pullback). -/
instance SystemGeometricInverseImageData.levelFunctorAdditive
    (F : SystemGeometricInverseImageData BY BX u I) (n : ℕ) :
    (F.levelFunctor n).Additive := F.levelAdditive n

/-- Left exactness of the level inverse image. Source: Stacks 03DA
(blueprint: lem-pur-system-singleton-geometric-pullback). -/
instance SystemGeometricInverseImageData.levelFunctorLimits
    (F : SystemGeometricInverseImageData BY BX u I) (n : ℕ) :
    PreservesFiniteLimits (F.levelFunctor n) := F.levelLimits n

/-- Right exactness of the level inverse image. Source: Stacks 03DB
(blueprint: lem-pur-system-singleton-geometric-pullback). -/
instance SystemGeometricInverseImageData.levelFunctorColimits
    (F : SystemGeometricInverseImageData BY BX u I) (n : ℕ) :
    PreservesFiniteColimits (F.levelFunctor n) := F.levelColimits n

/-- The canonical localization of the termwise evaluation square.
Source: Zheng, Construction 4.1; Stacks 015F
(blueprint: lem-pur-system-singleton-geometric-pullback). -/
def SystemGeometricInverseImageData.derivedEvaluation
    (F : SystemGeometricInverseImageData BY BX u I) (n : ℕ) :
    F.functor.mapDerivedCategory ⋙ derivedSystemEvaluation BX n ≅
      derivedSystemEvaluation BY n ⋙ (F.levelFunctor n).mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso F.functor (systemEvaluation BX n)).symm ≪≫
    Functor.mapDerivedCategoryNatIso
      (G := systemEvaluation BY n ⋙ F.levelFunctor n)
      (F.evaluation n : F.functor ⋙ systemEvaluation BX n ≅
        systemEvaluation BY n ⋙ F.levelFunctor n) ≪≫
    Functor.mapDerivedCategoryCompIso (systemEvaluation BY n) (F.levelFunctor n)

variable (SY : SystemScalarAssignment (J := J)) (TY : SystemTensorCoherence SY)
  (SX : SystemScalarAssignment (J := K)) (TX : SystemTensorCoherence SX)

set_option linter.unusedVariables false in
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

include SX in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
end SheafOfModules
