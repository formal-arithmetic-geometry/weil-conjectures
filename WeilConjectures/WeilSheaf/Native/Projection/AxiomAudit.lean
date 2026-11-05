/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import all WeilConjectures.WeilSheaf.ProperProjectionFormula
import all WeilConjectures.WeilSheaf.Native.Projection.ProperProjectionIso
import all WeilConjectures.WeilSheaf.Native.NativeCondensedRealizationCoherence
import all WeilConjectures.WeilSheaf.Native.Projection.NativeDerivedTensorSquare
import all WeilConjectures.WeilSheaf.Native.Projection.NativeDerivedTensorSquareOfTotal
import all WeilConjectures.WeilSheaf.Native.Projection.NativeDerivedCoherenceOfSquare
import all WeilConjectures.WeilSheaf.Native.Projection.NativeTotalTensorSquare
import all WeilConjectures.WeilSheaf.Native.Projection.NativeTotalTensorSquareOfSheaf
import all WeilConjectures.WeilSheaf.Native.Projection.NativeSheafTensorSquare
import all WeilConjectures.WeilSheaf.Native.Projection.NativeSheafTensorCore
import all WeilConjectures.WeilSheaf.Native.Projection.AdicSheafTensorSquare
import all WeilConjectures.WeilSheaf.Native.Projection.SheafTensorUnit
import all WeilConjectures.WeilSheaf.Native.Projection.NativeTotalTensorCore
import all WeilConjectures.WeilSheaf.Native.Projection.TensorSquareCompatibility
import all WeilConjectures.WeilSheaf.Native.Projection.DerivedSquareFromModelFamilies
import all WeilConjectures.WeilSheaf.Native.Projection.NativeDerivedSquareFromNativeModels
import all WeilConjectures.WeilSheaf.Native.Projection.NativeDerivedSquareFromNativeRestriction
import all WeilConjectures.WeilSheaf.Native.Projection.NativeDerivedSquareFromNativeComparisons
import all WeilConjectures.WeilSheaf.Native.Projection.NativeDerivedSquareFromOrdinaryComparison
import all WeilConjectures.WeilSheaf.Native.Projection.DerivedModelNormalizations
import all WeilConjectures.WeilSheaf.Native.Projection.NativeModelFamilyNormalization
import all WeilConjectures.WeilSheaf.Native.Projection.DerivedSquareFromTotalFunctors
import all WeilConjectures.WeilSheaf.Native.Projection.NativeDerivedSquareOfRepresentatives
import all WeilConjectures.WeilSheaf.Native.Projection.DerivedSquareFromModels
import all WeilConjectures.WeilSheaf.Native.Projection.NativeModelNormalization
import all WeilConjectures.WeilSheaf.Native.Projection.NativePullTensorNormalization
import all WeilConjectures.WeilSheaf.Native.Projection.ModelSquareCancellation
import all WeilConjectures.WeilSheaf.Native.Projection.TotalSquareToModel
import Lean.Util.CollectAxioms

/-! # Dependency audit for the native proper projection formula

The remote build records the remaining proof leaves reachable from the theorem.
-/

#print axioms
  AlgebraicGeometry.WeilComplex.nonempty_rightDerivedLowerStar_nativeDerivedTensor_iso

#print axioms AlgebraicGeometry.WeilComplex.rightDerivedLowerStarNativeDerivedTensorIso
#print axioms AlgebraicGeometry.WeilComplex.map_rightDerivedLowerStarNativeDerivedTensorIso_hom_app
#print axioms AlgebraicGeometry.ProEtaleWeilSheaf.condensedRealizationTensor_pull_square
#print axioms AlgebraicGeometry.ProEtaleWeilSheaf.condensedRealizationSheafTensor_pull_square
#print axioms AlgebraicGeometry.ProEtaleWeilSheaf.native_two_sided_kflat_representatives
#print axioms AlgebraicGeometry.ProEtaleWeilSheaf.isIso_projectionMap_derivedCondensedRealization

open Lean in
run_cmd do
  let env ← getEnv
  let mut seen : NameSet := {}
  let target := `AlgebraicGeometry.WeilComplex.nonempty_rightDerivedLowerStar_nativeDerivedTensor_iso
  let mut pending := #[target]
  let mut leaves : Array Name := #[]
  let mut unavailable : Array Name := #[]
  while !pending.isEmpty do
    let name := pending.back!
    pending := pending.pop
    if seen.contains name then
      continue
    seen := seen.insert name
    unless (← collectAxioms name).contains ``sorryAx do
      continue
    if let some info := (env.setExporting false).find? name then
      if info.value? true |>.isNone then
        unavailable := unavailable.push name
      let deps := info.type.getUsedConstants ++
        ((info.value? true).map Expr.getUsedConstants).getD #[]
      if deps.contains ``sorryAx then
        leaves := leaves.push name
      pending := pending ++ deps.filter (· != ``sorryAx)
    else
      unavailable := unavailable.push name
  for name in leaves.qsort Name.lt do
    logInfo m!"K5 existing proof leaf: {name}"
  for name in unavailable.qsort Name.lt do
    logInfo m!"K5 imported dependency with unavailable proof body: {name}"
  logInfo <| m!"K5 visible direct sorry dependencies: {leaves.size}; " ++
    m!"unavailable bodies: {unavailable.size}"
