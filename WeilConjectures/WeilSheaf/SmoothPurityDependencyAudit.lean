/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import all WeilConjectures.WeilSheaf.SmoothPurityThomDescent
import Lean

/-! # Declaration dependency audit for the absolute-purity Thom route

This command reports the declarations containing a direct use of `sorryAx`
reachable from the final conditional Thom theorem. It creates no mathematical
declaration and does not participate in its proof.
-/

open Lean in
run_elab do
  let root :=
    `AlgebraicGeometry.WeilComplex.nonempty_trivialLineThom_of_tate_encoding
  let env ← getEnv
  logInfo m!"Root: {root}; axioms: {← collectAxioms root}"
  let mut pending := #[root]
  let mut seen : NameSet := {}
  let mut leaves : Array Name := #[]
  let mut unavailable : Array Name := #[]
  while !pending.isEmpty do
    let name := pending.back!
    pending := pending.pop
    if seen.contains name then
      continue
    seen := seen.insert name
    unless (← collectAxioms name).contains `sorryAx do
      continue
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
  let forbidden := #[
    `AlgebraicGeometry.WeilComplex.nonempty_upperShriek_iso_of_smoothOfRelativeDimension,
    `AlgebraicGeometry.WeilComplex.nonempty_derivedLowerShriek_adjunction_of_smooth,
    `AlgebraicGeometry.WeilComplex.exists_natTrans_upperShriek_isIso_forget_of_smooth]
  for name in forbidden do
    if seen.contains name then
      throwError "The Thom proof uses the relative-purity declaration {name}"
  unless unavailable.isEmpty do
    logWarning "The dependency audit needs the imported proof bodies listed above"
