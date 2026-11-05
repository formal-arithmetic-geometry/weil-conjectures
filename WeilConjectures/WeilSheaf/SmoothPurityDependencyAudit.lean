/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import all WeilConjectures.CategoryTheory.Native.NativeOpenTensorDescentData
import all WeilConjectures.CategoryTheory.Native.NativeWeilTensorConstraintLifts
import all WeilConjectures.WeilSheaf.CompactProjectionFormula
import all WeilConjectures.WeilSheaf.SmoothPurityThomFromTate
import all WeilConjectures.WeilSheaf.Native.NativeCompactProjectionFormula
import all WeilConjectures.WeilSheaf.Native.NativeDerivedWeilTensorConstructible
import all WeilConjectures.WeilSheaf.Native.NativeForgetNormalizedBinaryModels
import all WeilConjectures.WeilSheaf.Native.NativeGeometricTensorComparison
import all WeilConjectures.WeilSheaf.Native.NativeNormalizedTensorModels
import all WeilConjectures.WeilSheaf.Native.NativeRestrictionForgetTotalModel
import all WeilConjectures.WeilSheaf.Native.Open.NativeOpenDerivedTensor
import all WeilConjectures.WeilSheaf.Native.Open.NativeOpenTensorComparisonData
import all WeilConjectures.WeilSheaf.Native.Open.NativeOpenTensorExtensionDescent
import all WeilConjectures.WeilSheaf.Native.Open.NativeOpenTensorForgetNormalization
import all WeilConjectures.WeilSheaf.Native.Open.NativeOpenTensorLocalization
import all WeilConjectures.WeilSheaf.Native.Open.NativeOpenTensorNormalization
import all WeilConjectures.WeilSheaf.Native.Open.NativeOpenTensorNormalizedRestrictionDescent
import all WeilConjectures.WeilSheaf.Native.Open.NativeOpenTensorOperations
import all WeilConjectures.WeilSheaf.Native.Open.NativeOpenTensorPresentationExistence
import all WeilConjectures.WeilSheaf.Native.Open.NativeOpenTensorRestrictionForget
import all WeilConjectures.WeilSheaf.Native.Open.NativeOpenTensorRestrictionForgetKFlat
import all WeilConjectures.WeilSheaf.Native.Open.NativeOpenTensorUnitNormalization
import all WeilConjectures.WeilSheaf.Native.Ordinary.NativeOrdinaryOpenTensorSupport
import all WeilConjectures.WeilSheaf.Native.Ordinary.NativeOrdinaryRestrictionTensor
import all WeilConjectures.WeilSheaf.Native.Ordinary.NativeOrdinaryRestrictionTotalModel
import all WeilConjectures.WeilSheaf.Native.Weil.NativeWeilClosedForgetful
import all WeilConjectures.WeilSheaf.Native.Weil.NativeWeilRingedTensorModel
import all WeilConjectures.WeilSheaf.Native.Weil.NativeWeilUnitMateIsIso
import all WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorAdjoints
import all WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorCoherence
import all WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorGeometry
import all WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorLift
import all WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorRingedDerivedSquare
import all WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorRingedDerivedSquareNative
import all WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorRingedDerivedSquareNativeCoherence
import all WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorRingedSwapLocalization
import all WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorRingedTransport
import all WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorRingedUnitSymmetryRepresentatives
import all WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorTransport
import all WeilConjectures.WeilSheaf.ProperProjectionFormula
import all WeilConjectures.WeilSheaf.SixFunctors.DerivedWeilTensorOperations
import all WeilConjectures.WeilSheaf.SmoothPurityAffineLineConstant
import all WeilConjectures.WeilSheaf.SmoothPurityCompactConstant
import all WeilConjectures.WeilSheaf.SmoothPurityCompactHomotopy
import all WeilConjectures.WeilSheaf.SmoothPurityNativeHomShift
import all WeilConjectures.WeilSheaf.SmoothPurityNativeHomSingle
import all WeilConjectures.WeilSheaf.SmoothPurityNativeTensorTate
import all WeilConjectures.WeilSheaf.SmoothPurityNativeTensorTateShift
import all WeilConjectures.WeilSheaf.SmoothPurityThom
import all WeilConjectures.WeilSheaf.SmoothPurityThomDescent
import all WeilConjectures.WeilSheaf.VerdierDual
import all WeilConjectures.WeilSheaf.VerdierDualLocalization
import all WeilConjectures.WeilSheaf.VerdierExchange
import Lean

/-! # Declaration dependency audit for the absolute-purity Thom route

This command reports the declarations containing a direct use of `sorryAx`
reachable from the final Thom theorem. It creates no mathematical
declaration and does not participate in its proof.
-/

open Lean in
run_elab do
  let root :=
    `AlgebraicGeometry.WeilComplex.purity_nonempty_trivialLineThom
  let env ← getEnv
  logInfo m!"Root: {root}; axioms: {← collectAxioms root}"
  let mut pending := #[root]
  let mut seen : NameSet := {}
  let mut leaves : Array Name := #[]
  let mut unavailable : Array Name := #[]
  let mut inspected : NameSet := {}
  while !pending.isEmpty do
    let name := pending.back!
    pending := pending.pop
    if seen.contains name then
      continue
    seen := seen.insert name
    unless (← collectAxioms name).contains `sorryAx do
      continue
    if let some idx := env.getModuleIdxFor? name then
      inspected := inspected.insert env.header.moduleNames[idx.toNat]!
    match env.checked.get.find? name with
    | none => unavailable := unavailable.push name
    | some info =>
      if info.isAxiom then
        unavailable := unavailable.push name
        continue
      let deps := info.type.getUsedConstants ++
        ((info.value? true).map Expr.getUsedConstants).getD #[]
      if deps.contains `sorryAx then
        leaves := leaves.push name
      else if deps.isEmpty then
        unavailable := unavailable.push name
      else
        pending := pending ++ deps
  logInfo m!"Direct sorry dependencies: {leaves.qsort Name.lt}"
  logInfo m!"Unavailable dependency bodies: {unavailable.qsort Name.lt}"
  logInfo m!"Visited declarations: {seen.toArray.size}"
  let mut modules : NameSet := {}
  for name in unavailable do
    if let some idx := env.getModuleIdxFor? name then
      modules := modules.insert env.header.moduleNames[idx.toNat]!
  for name in modules.toArray.qsort Name.lt do
    logInfo m!"Missing import all: {name}"
  for name in inspected.toArray.qsort Name.lt do
    logInfo m!"Proof import all: {name}"
  let forbidden := #[
    `AlgebraicGeometry.WeilComplex.exists_forget_upperShriek_adicConstant_iso_comm_derivedStrIso,
    `AlgebraicGeometry.WeilComplex.nonempty_upperShriek_iso_of_smoothOfRelativeDimension,
    `AlgebraicGeometry.WeilComplex.nonempty_derivedLowerShriek_adjunction_of_smooth,
    `AlgebraicGeometry.WeilComplex.exists_natTrans_upperShriek_isIso_forget_of_smooth]
  for name in forbidden do
    if seen.contains name then
      throwError "The Thom proof uses the relative-purity declaration {name}"
  let allowed := #[
    `AlgebraicGeometry.ProEtaleWeilSheaf.native_weil_tensor_ringed_swap_localization,
    `AlgebraicGeometry.WeilComplex.nonempty_rightDerivedLowerStar_nativeDerivedTensor_iso]
  for name in leaves do
    unless allowed.contains name do
      throwError "Unexpected sorry dependency: {name}"
  unless unavailable.isEmpty do
    throwError "The dependency audit needs the imported proof bodies listed above"
