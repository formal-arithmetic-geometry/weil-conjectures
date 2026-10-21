/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q50
-/
module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.LaurentSeries

/-! # Compatible Laurent coordinates for a discrete valuation subalgebra

Source: Tate, Residues of differentials on curves, §3, Theorems 2 and 4;
the completion and Laurent coordinate construction in steps 7–11 of
lem-pc-tate-dvr-residue-calculus (blueprint: def-pc-dvr-laurent-coordinates).
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace TateResidue

/-- A coefficient-field coordinate on the completed DVR, its extension to the fraction
field, and its embedding in Laurent series. The residue
normalization fixes the identification of the coefficient field with the residue field.
The compatibility on the original DVR determines the fraction-field map uniquely.

Source: Tate, §3, Theorems 2 and 4, with the separable coefficient-field construction
in steps 7–11 of lem-pc-tate-dvr-residue-calculus
(blueprint: def-pc-dvr-laurent-coordinates). -/
structure DVRLaurentCoordinates {k : Type u} {K : Type v} [Field k] [Field K]
    [Algebra k K] (O : Subalgebra k K) [IsDiscreteValuationRing O] (t : O) where
  /-- The coefficient-field identification of the maximal-ideal-adic completion. -/
  completionEquiv : AdicCompletion (IsLocalRing.maximalIdeal O) O ≃ₐ[k]
    PowerSeries (IsLocalRing.ResidueField O)
  /-- The specified uniformizer is sent to the power-series variable. -/
  uniformizer_eq : completionEquiv
    (algebraMap O (AdicCompletion (IsLocalRing.maximalIdeal O) O) t) = PowerSeries.X
  /-- Reduction of the completion agrees with taking the constant coefficient. -/
  residue_eq : ∀ z : AdicCompletion (IsLocalRing.maximalIdeal O) O,
    PowerSeries.constantCoeff (completionEquiv z) =
      AdicCompletion.evalOneₐ (IsLocalRing.maximalIdeal O) z
  /-- The induced map from the fraction field into the Laurent-series field. -/
  fieldMap : K →ₐ[k] LaurentSeries (IsLocalRing.ResidueField O)
  /-- The fraction-field map extends the completed coordinate on the original DVR. -/
  fieldMap_eq : ∀ x : O, fieldMap (x : K) =
    HahnSeries.ofPowerSeries ℤ (IsLocalRing.ResidueField O)
      (completionEquiv (algebraMap O (AdicCompletion (IsLocalRing.maximalIdeal O) O) x))

end TateResidue
