/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import all WeilConjectures.LeanEval.WeilConjectures
import all WeilConjectures.Statement
import WeilConjectures.WeilSheaf.SmoothPurityDependencyAudit
import Lean

/-! # Declaration closure of the Weil conjectures after absolute purity

The audit rejects every relative-purity declaration and reports all remaining
sorry leaves, including leaves assigned to other workers.
-/

open Lean in
run_elab do
  let roots := #[
    `AlgebraicGeometry.Scheme.weil_conjectures,
    `LeanEval.AlgebraicGeometry.WeilConjectures.weil_conjectures]
  let env ← getEnv
  for root in roots do
    logInfo m!"Root: {root}; axioms: {← collectAxioms root}"
  let mut pending := roots
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
      throwError "The main theorem uses the relative-purity declaration {name}"
  unless unavailable.isEmpty do
    throwError "The dependency audit needs the imported proof bodies listed above"
