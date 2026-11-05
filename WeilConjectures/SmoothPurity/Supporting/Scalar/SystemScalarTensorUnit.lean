/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.ScalarExtensionTower.ScalarExtensionTowerRealizationData
public import WeilConjectures.SmoothPurity.Completed.CompletedPullbackTowerCore
import all WeilConjectures.SmoothPurity.Finite.FinitePullbackTensorUnitRepresentatives
import all WeilConjectures.CategoryTheory.Ringed.Slice.RingedSliceScalarUnit
import all WeilConjectures.SmoothPurity.ScalarExtensionTower.ScalarExtensionTowerComparisonData
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
import all WeilConjectures.CategoryTheory.Ringed.Tensor.RingedTensorConstraintCompletion
import all WeilConjectures.CategoryTheory.Scalar.ScalarHomTensorCoherence
import all WeilConjectures.TraceFormula.Integral.IntegralComparisonSequenceSystems
import all WeilConjectures.SmoothPurity.ScalarExtensionTower.ScalarExtensionTowerRealizationData
import WeilConjectures.Algebra.Homology.KFlatTotalTensorModel
import WeilConjectures.SixFunctors.CoefficientClosedStructure.CoefficientRingedTensorHomModelSupplement

/-! # Scalar extension of coherent systems is unital and associative

The whole-system scalar tensorator `ScalarExtensionTower.derivedSigma` is compatible with the
associators and unitors of the published coherent system monoidal structures.

Source: Stacks Project, Tags 03EL and 07A4.
(blueprint: lem-pur-system-scalar-tensor-braiding).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme MonoidalCategory
namespace WeilConjectures

attribute [local irreducible] HasDerivedCategory.standard pullbackTensorCalculus
  Functor.leftAdjoint Functor.mapDerivedCategory Functor.mapDerivedCategoryFactors
  integralComparisonSequenceScalarModel
attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall

variable (l : ℕ) [Fact l.Prime]
  (E L : Type u) [Field E] [Field L]
  [Algebra (Padic l) E] [Algebra (Padic l) L]
  [FiniteDimensional (Padic l) E] [FiniteDimensional (Padic l) L]
  (ι : E →ₐ[Padic l] L) (W : Scheme.{u})

/-- Pasting the six pure-section equations requires only function congruence. -/
private theorem scalarAssoc_sectionSquare
    {A B C D E F G H : Type*}
    (σ : A → B) (ηB : B → C) (κB : C → D) (tB : D → H)
    (ηA : A → E) (κA : E → F) (tA : F → G) (τ : G → H)
    (x : A) (b : B) (d : D) (h : H) (f : F) (g : G)
    (hσ : σ x = b) (hκB : κB (ηB b) = d) (htB : tB d = h)
    (hκA : κA (ηA x) = f) (htA : tA f = g) (hτ : τ g = h) :
    tB (κB (ηB (σ x))) = τ (tA (κA (ηA x))) := by
  rw [hσ, hκB, htB, hκA, htA, hτ]

section Representatives
attribute [local implicit_reducible] coefficientSequenceInternalHom coefficientSequenceHasDerived
  CoefficientClosedStructure.tensor
attribute [local irreducible]
  DerivedCategory _root_.instCategoryDerivedCategory DerivedCategory.Q
  SheafOfModules.monoidalCategory CochainComplex.IsKFlatIndependentCoefficients
  derivedInternalHomOfUniverses coefficientTotalTensor Functor.mapHomologicalComplex

end Representatives

end WeilConjectures
