# WeilConjectures.PurityFiniteSetting.purityPowerAdd

## Reason

The unchanged direct-sum consumer exceeded the 60-second single-file limit both
against this delivery and against the published library without its overlay.
Diagnostics located repeated expansion of the single-degree embedding while
comparing tensor-unit objects. Keep that embedding folded locally and use
transparency-respecting unification. This is an unclaimed module's compilation
repair, not a change of a statement, definition body or public declaration attribute.
No source-library module is modified.

The original check reports `timeout after 60 s`. With only these annotations, the
actual module compiles in 30.3 seconds; the item compiles in the same batch in 21.2
seconds. No limit, heartbeat or linter setting is increased or suppressed.

## Old

The original module prefix is:

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.VectorPurityBaseChange
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition

/-! # Ordered vector purity direct-sum equation

Source: main-20261015 sec-smooth-purity/sk-prop-an, integration and Steps 4--6
(blueprint: def-pur-vector-purity-direct-sum).

## Main definitions

This module gives the canonical comparisons and their displayed source equation.
Every map is constructed before the compatibility proposition is stated.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u v₁ v₂ w₁ w₂
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
namespace WeilConjectures.PurityFiniteSetting

/-- Additive ranks use the ordered tensor-power associator. The base case uses the
coefficient UNIT OBJECT, and each successor is the monoidal associator.
Source: sk-prop-an, Step 5 (blueprint: def-pur-vector-purity-direct-sum). -/
def purityPowerAdd (A : Type (u + 1)) [CommRing A] (N : ℕ) (hA : (N : A) = 0)
    (B : Scheme.{u}) (r : ℕ) : ∀ s : ℕ,
    Etale.affineLinearBaseCoefficient A N hA B (r + s) ≅
      Etale.affineLinearBaseCoefficient A N hA B r ⊗
        Etale.affineLinearBaseCoefficient A N hA B s
  | 0 => (ρ_ _).symm ≪≫
      (Iso.refl _ ⊗ᵢ (Etale.singleFunctorObjUnitIso (ModuleCat.{u + 1} A) B).symm)
  | s + 1 => (purityPowerAdd A N hA B r s ⊗ᵢ Iso.refl _) ≪≫ α_ _ _ _

```

## New

The new module prefix is:

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.VectorPurityBaseChange
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition

/-! # Ordered vector purity direct-sum equation

Source: main-20261015 sec-smooth-purity/sk-prop-an, integration and Steps 4--6
(blueprint: def-pur-vector-purity-direct-sum).

## Main definitions

This module gives the canonical comparisons and their displayed source equation.
Every map is constructed before the compatibility proposition is stated.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
universe u v₁ v₂ w₁ w₂
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
namespace WeilConjectures.PurityFiniteSetting

-- Preserve the single-degree embedding while comparing its tensor-unit objects.
-- Unfolding it here expands the derived localization before comparing the sheaves.
attribute [local irreducible] _root_.DerivedCategory.singleFunctors

/-- Additive ranks use the ordered tensor-power associator. The base case uses the
coefficient UNIT OBJECT, and each successor is the monoidal associator.
Source: sk-prop-an, Step 5 (blueprint: def-pur-vector-purity-direct-sum). -/
def purityPowerAdd (A : Type (u + 1)) [CommRing A] (N : ℕ) (hA : (N : A) = 0)
    (B : Scheme.{u}) (r : ℕ) : ∀ s : ℕ,
    Etale.affineLinearBaseCoefficient A N hA B (r + s) ≅
      Etale.affineLinearBaseCoefficient A N hA B r ⊗
        Etale.affineLinearBaseCoefficient A N hA B s
  | 0 => (ρ_ _).symm ≪≫
      (Iso.refl _ ⊗ᵢ (Etale.singleFunctorObjUnitIso (ModuleCat.{u + 1} A) B).symm)
  | s + 1 => (purityPowerAdd A N hA B r s ⊗ᵢ Iso.refl _) ≪≫ α_ _ _ _

```

Every declaration, signature, visibility, public attribute and data body after this
prefix is byte-for-byte identical. The irreducibility annotation is local to this
file and is not exported. In particular, purityPowerAdd, purityGammaUnit,
purityOrderedAssociator, puritySecondFactorGamma and PurityDirectSumEquation are
unchanged. No target meaning changes.

## Users

`tools/downstream.py Sheaf.Paper.VectorPurityDirectSum --uses purityPowerAdd
purityGammaUnit purityOrderedAssociator puritySecondFactorGamma PurityDirectSumEquation`
lists the following transitive importers. Only VectorBundlePurity uses one of these
names outside the module itself (PurityDirectSumEquation); its complete definition
and type remain identical. No downstream adaptation is needed.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.VectorPurityDirectSum | unclaimed | Local elaboration annotations only; compiled. |
| Sheaf.EtaleCohomology.Purity.RealSheaves.TateTwistWeightShift | unclaimed | Same public declarations and bodies; no adaptation. |
| Sheaf.Paper.AdicPurityExceptionalReduction | unclaimed | Same public declarations and bodies; no adaptation. |
| Sheaf.Paper.AdicPurityFiniteTensor | unclaimed | Same public declarations and bodies; no adaptation. |
| Sheaf.Paper.AdicPurityObjects | unclaimed | Same public declarations and bodies; no adaptation. |
| Sheaf.Paper.AdicPurityRootComparisons | unclaimed | Same public declarations and bodies; no adaptation. |
| Sheaf.Paper.AdicPuritySourceReduction | unclaimed | Same public declarations and bodies; no adaptation. |
| Sheaf.Paper.AdicPurityTwistReduction | unclaimed | Same public declarations and bodies; no adaptation. |
| Sheaf.Paper.AdicSmoothDualizingComplexes | unclaimed | Same public declarations and bodies; no adaptation. |
| Sheaf.Paper.DualizingObjectPurity | unclaimed | Same public declarations and bodies; no adaptation. |
| Sheaf.Paper.FiniteAdjointMateCompatibility | unclaimed | Same public declarations and bodies; no adaptation. |
| Sheaf.Paper.FiniteCoefficientSmoothPurity | unclaimed | Same public declarations and bodies; no adaptation. |
| Sheaf.Paper.FiniteDncNormalizationReduction | unclaimed | Same public declarations and bodies; no adaptation. |
| Sheaf.Paper.FiniteReductionAffineOrientation | unclaimed | Same public declarations and bodies; no adaptation. |
| Sheaf.Paper.FiniteReductionChartCalculus | unclaimed | Same public declarations and bodies; no adaptation. |
| Sheaf.Paper.FiniteReductionComparisons | unclaimed | Same public declarations and bodies; no adaptation. |
| Sheaf.Paper.FiniteReductionOfPurity | unclaimed | Same public declarations and bodies; no adaptation. |
| Sheaf.Paper.FiniteReductionRootCharts | unclaimed | Same public declarations and bodies; no adaptation. |
| Sheaf.Paper.FiniteSmoothPullbackExchange | unclaimed | Same public declarations and bodies; no adaptation. |
| Sheaf.Paper.FiniteUniversalSmoothTrace | unclaimed | Same public declarations and bodies; no adaptation. |
| Sheaf.Paper.PurAdicReconstruction | unclaimed | Same public declarations and bodies; no adaptation. |
| Sheaf.Paper.PurityCompositionCoherence | unclaimed | Same public declarations and bodies; no adaptation. |
| Sheaf.Paper.PurityDiagonalDualizingObject | unclaimed | Same public declarations and bodies; no adaptation. |
| Sheaf.Paper.RationalSmoothPurityCanonical | unclaimed | Same public declarations and bodies; no adaptation. |
| Sheaf.Paper.SmoothPurityMap | unclaimed | Same public declarations and bodies; no adaptation. |
| Sheaf.Paper.SmoothTrace | unclaimed | Same public declarations and bodies; no adaptation. |
| Sheaf.Paper.TwistFrobeniusScalar | unclaimed | Same public declarations and bodies; no adaptation. |
| Sheaf.Paper.VectorBundlePurity | unclaimed | Same public declarations and bodies; no adaptation. |
| Sheaf.SecSmoothPurity.FiniteGeneralRing | unclaimed | Same public declarations and bodies; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionCompatibilities | unclaimed | Same public declarations and bodies; no adaptation. |
| Sheaf.SecSmoothPurity.SmoothPurityNaturality | unclaimed | Same public declarations and bodies; no adaptation. |

## Status

landed 20261020T221141-L-4149524 2026-10-20 (merge of deliver/F1/Sheaf.AlgebraicGeometry.VectorBundleIntegration)
