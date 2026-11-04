/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import WeilConjectures.WeilSheaf.ProperProjectionFormula
import Lean.Util.CollectAxioms

/-! # Dependency audit for the native proper projection formula

The remote build records the remaining proof leaves reachable from the theorem.
-/

#print axioms
  AlgebraicGeometry.WeilComplex.nonempty_rightDerivedLowerStar_nativeDerivedTensor_iso

open Lean in
run_cmd do
  let env ← getEnv
  let mut seen : NameSet := {}
  let mut pending := #[`AlgebraicGeometry.WeilComplex.nonempty_rightDerivedLowerStar_nativeDerivedTensor_iso]
  let mut leaves : Array Name := #[]
  while !pending.isEmpty do
    let name := pending.back!
    pending := pending.pop
    if seen.contains name then
      continue
    seen := seen.insert name
    unless (← collectAxioms name).contains ``sorryAx do
      continue
    if let some info := env.checked.get.find? name then
      let deps := info.type.getUsedConstants ++
        ((info.value? true).map Expr.getUsedConstants).getD #[]
      if deps.contains ``sorryAx then
        leaves := leaves.push name
      pending := pending ++ deps.filter (· != ``sorryAx)
  for name in leaves.qsort Name.lt do
    logInfo m!"K5 existing proof leaf: {name}"
  logInfo m!"K5 remaining proof leaves: {leaves.size}"
