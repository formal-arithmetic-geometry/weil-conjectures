/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.GeneratorReduction.GeneratorReductionStatement
public import WeilConjectures.AlgebraicGeometry.Sf.SfCbcCompactSupportCompositionLimit
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
import WeilConjectures.AlgebraicGeometry.Standard.StandardQuotientsPerfectSupplement
import Mathlib.GroupTheory.OrderOfElement
import WeilConjectures.SmoothPurity.Pur.PurNormalizedReconstructionAdjunctionCalculus
import WeilConjectures.SmoothPurity.Sf.SfDerivedCompleteLegacyComparison
import Mathlib.Data.Nat.Prime.Infinite
import all WeilConjectures.AlgebraicGeometry.Completed.Pullback.CompletedPullbackAdjunctionSupplement
import all WeilConjectures.AlgebraicGeometry.Sf.SfCbcExtensionZeroCompletion
import WeilConjectures.AlgebraicGeometry.Constant.ConstantOpenRestrictionModelComparison
import WeilConjectures.SixFunctors.Sf.SfIntegralReductionTowerSupplement
import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses

/-! # Constant semilinear comparison for a single proper or open operation

Source: Stacks Project, Tag 0E48, remark-compatible-with-diagram;
blueprint fix-lem-exchanges, Step 5
(blueprint: lem-sf-constant-semilinear-generator-comparison).

The constant tower is over the constant valuation-ring sheaf, rather than the completed
ring sheaf. All derived categories localize strict diagrams before taking evaluations.
Proper and open operations are single letters, not structural `GeneratorKind` values.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOfSpec false
set_option genInjectivity false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u s i vB vC wB wC dB dC a₁ a₂ a₃ a₄ h₁ h₂ h₃ h₄ d₁ d₂ d₃ d₄
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures
namespace WeilConjectures.GeneratorReduction

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The actual valuation ring. Source: blueprint coefficient convention
(blueprint: lem-sf-constant-semilinear-generator-comparison). -/
abbrev constantRing := Padic.coefficientExtensionIntegers l E

/-- Ordinary restriction from completed scalars, followed by the published small-site model.
Source: Stacks 099I and 00VC
(blueprint: lem-sf-constant-semilinear-generator-comparison). -/
@[irreducible] def ordinaryH (T : Scheme.{u}) :
    scalarReductionSource l E T ⥤ ConstantCompletion.Mod (sfCbcModelRing T (constantRing l E)) :=
  SheafOfModules.restrictScalars (integralConstantToCompletionOfUniverses l E T) ⋙
    sfCbcModelModules T (constantRing l E)

/-- `T_T`, the strict constant-ring tower, in the published equivalent small model.
Source: Stacks 0941 (blueprint: lem-sf-constant-semilinear-generator-comparison). -/
abbrev constantTowerCategory (T : Scheme.{u}) :=
  ℕᵒᵖ ⥤ ConstantCompletion.Mod (sfCbcModelRing T (constantRing l E))

/-- The actual termwise restriction from varying-ring systems to constant-ring towers.
Source: Stacks 0941 (blueprint: lem-sf-constant-semilinear-generator-comparison). -/
def ordinaryU (T : Scheme.{u}) : coefficientSequenceModules l E T ⥤
    constantTowerCategory l E T :=
  coefficientSequenceRestriction l E T ⋙
    (Functor.whiskeringRight ℕᵒᵖ _ _).obj (ordinaryH l E T)

/-- `U_T`, derived termwise scalar restriction on the strict diagram.
Source: Stacks 0941 (blueprint: lem-sf-constant-semilinear-generator-comparison). -/
def U (T : Scheme.{u}) : coefficientSequenceDerived l E T ⥤
    (sfCbcSite T).towerDerived (ULift.{u + 1} (constantRing l E)) :=
  (ordinaryU l E T).mapDerivedCategory

attribute [local irreducible] ordinaryU

end WeilConjectures.GeneratorReduction
