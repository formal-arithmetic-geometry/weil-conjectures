/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedFourierTransform
public import WeilConjectures.AlgebraicGeometry.GroupScheme.CondensedFibreLinearCurrent.CondensedFibreLinearOperationsStatement
public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeCondensedWeil.NativeCondensedWeilReality
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ConstantWeil.CondensedConstantWeilTwist
public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeL2.NativeL2MiddleImage
public import WeilConjectures.DeligneLaumon.CondensedWeil.CondensedOpenClosedLocalizationMapsCore
public import WeilConjectures.CategoryTheory.InverseMateEquivalence
import WeilConjectures.Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.CategoryTheory.Monoidal.Mod
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
import WeilConjectures.CategoryTheory.ModuleObjects.Abelian
import WeilConjectures.CategoryTheory.ModuleObjects.ProjectionFormulaAdjunction
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.FullyFaithful
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.OpenClosed
import WeilConjectures.AlgebraicGeometry.CoefficientHeartGeneralStatement
import WeilConjectures.AlgebraicGeometry.CondensedArtinSchreierLisse

/-! # Reality of the condensed realified Fourier kernel

Source: literature/blueprint/latest/blueprint/part-weights-riemann-hypothesis/
sec-deligne-laumon-a1/sec-purity-of-the-lisse-part-of-the-fourier-transform/
sk-p-dl-a1-some-weight/lem-fd-realified-kernel-real.md and its proof, Steps 1--2
(blueprint: lem-fd-realified-kernel-real).

We state the general assertion for every pure lisse Weil sheaf. The first assertion
of the source is its specialization. All Weil data below are the canonical descent,
pullback, adjunction-mate, tensor and contragredient data, with no free comparison map.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj

namespace WeilConjectures.CondensedRealified

attribute [local irreducible] CondensedRing.upperStar

variable (D : FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime]

/-- The model affine line. Source: the affine-line setup
(blueprint: lem-fd-realified-kernel-real). -/
abbrev lineModel : Over (Spec (.of D.k₀)) :=
  Over.mk (AffineSpace PUnit (Spec (.of D.k₀)) ↘ Spec (.of D.k₀))

variable {U₀ X₀ Y₀ : Over (Spec (.of D.k₀))}
  [LocallyOfFiniteType U₀.hom] [QuasiCompact U₀.hom]
  [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
  [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]

/-- The open comparison is the inverse mate of the inverse-image compositor.
Its invertibility follows from the existing inverse-mate theorem for equivalences.
Source: proof Step 1, canonical extension by zero
(blueprint: lem-fd-realified-kernel-real). -/
def openComparison (j₀ : U₀ ⟶ X₀) [IsOpenImmersion j₀.left] :
    CondensedWeil.openModuleExtension D ell j₀ ⋙
        CondensedRing.upperStar (Profinite.padicAlgClRingObj ell)
          (D.geometricFrobenius X₀).hom ≅
      CondensedRing.upperStar (Profinite.padicAlgClRingObj ell)
          (D.geometricFrobenius U₀).hom ⋙ CondensedWeil.openModuleExtension D ell j₀ :=
  let adj := CondensedRing.openImmersionLowerShriekUpperStarAdjunction
    (Profinite.padicAlgClRingObj ell) (NativeL2.geometricMap D j₀)
  let beta := (CondensedRing.upperStarSquareComparison (Profinite.padicAlgClRingObj ell)
    (NativeL2.frobeniusSquare D j₀)).symm
  letI := isIso_inverseMate_of_equivalences adj adj beta
  (asIso (((mateEquiv adj adj).symm beta.hom).natTrans)).symm

set_option maxHeartbeats 800000 in
-- Canonical pullback comparisons and derived tensor instances need a larger checking budget.
set_option synthInstance.maxHeartbeats 100000 in
set_option maxRecDepth 2048 in
set_option maxHeartbeats 800000 in
-- Canonical pullback comparisons and derived tensor instances need a larger checking budget.
set_option synthInstance.maxHeartbeats 100000 in
set_option maxRecDepth 2048 in
set_option maxHeartbeats 800000 in
-- Canonical pullback comparisons and derived tensor instances need a larger checking budget.
set_option synthInstance.maxHeartbeats 100000 in
set_option maxRecDepth 2048 in
end WeilConjectures.CondensedRealified
