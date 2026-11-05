/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Init
public import WeilConjectures.Tactic.FirstOrderApply
public meta import Lean.Elab.Tactic.BuiltinTactic

/-! # Stop model assembly at the first failed proof interface -/

public meta section

open Lean Meta Elab Tactic

/-- Propagate nested proof errors immediately instead of checking a partially recovered term. -/
elab "projection_strict " ts:tacticSeq : tactic =>
  Term.withoutErrToSorry <| withoutRecover <| evalTactic ts

/-- Check an interface as an auxiliary theorem without recomputing a minimal local closure. -/
elab "projection_seal " ts:tacticSeq : tactic => withMainContext do
  let g ← getMainGoal
  let target ← g.getType
  let hole ← mkFreshExprMVar target
  let rest := (← getGoals).tail!
  setGoals [hole.mvarId!]
  evalTactic ts
  unless (← getGoals).isEmpty do
    throwError "projection_seal: the interface proof has remaining goals"
  let pf ← instantiateMVars hole
  if pf.hasExprMVar then
    throwError "projection_seal: the interface proof has unassigned metavariables"
  let target ← instantiateMVars target
  g.assign (← Mathlib.Tactic.FirstOrderApply.sealProof target pf)
  setGoals rest
