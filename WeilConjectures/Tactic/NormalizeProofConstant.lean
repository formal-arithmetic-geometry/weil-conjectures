/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Init
public meta import Lean.Elab.Tactic.ElabTerm

/-!
# The tactic `normalize_proof_constant`

`normalize_proof_constant c` replaces, in the goal, every occurrence of the constant `c` (an
auxiliary proof constant, such as an instance proof abstracted out of a definition body) by the
instance of its type found by type class synthesis. The new goal is definitionally equal to the
old one by proof irrelevance.

Terms elaborated in theorem statements and terms elaborated in proofs may carry different proofs
of the same `Prop`-valued instance (an imported auxiliary proof constant, resp. the synthesized
instance) deep inside implicit arguments; comparing them can make the unifier and the kernel unfold
large definitions. Normalizing the goal first makes both sides syntactically equal.
-/

public meta section

namespace NormalizeProofConstant

open Lean Meta Elab Tactic

/-- Replace every occurrence of the constant `c` in the main goal by the synthesized instance of
its type. -/
def normalizeProofConstant (c : Name) : TacticM Unit := withMainContext do
  let g ← getMainGoal
  let t ← instantiateMVars (← g.getType)
  let t' ← Meta.transform t (pre := fun e => do
    match e with
    | .const m _ =>
      if m == c then
        return .done (← synthInstance (← inferType e))
      return .continue
    | _ => return .continue)
  replaceMainGoal [← g.replaceTargetDefEq t']

/-- Replace every occurrence of the constant `c` in the type of the hypothesis `h` by the
synthesized instance of its type. -/
def normalizeProofConstantAt (c : Name) (h : FVarId) : TacticM Unit := withMainContext do
  let g ← getMainGoal
  let t ← instantiateMVars (← h.getType)
  let t' ← Meta.transform t (pre := fun e => do
    match e with
    | .const m _ =>
      if m == c then
        return .done (← synthInstance (← inferType e))
      return .continue
    | _ => return .continue)
  replaceMainGoal [← g.replaceLocalDeclDefEq h t']

/-- Replace every closed application of the constant `d` whose type is that of the constant `c`
(two proofs of the same proposition) in the type of the hypothesis `h` by `c`. -/
def toProofConstantAt (c d : Name) (h : FVarId) : TacticM Unit := withMainContext do
  let g ← getMainGoal
  let cE ← mkConstWithLevelParams c
  let cT ← inferType cE
  let t ← instantiateMVars (← h.getType)
  let t' ← Meta.transform t (pre := fun e => do
    if e.hasLooseBVars || e == cE then return .continue
    if e.getAppFn.isConstOf d then
      let cE' ← mkConstWithFreshMVarLevels c
      if (← isDefEq (← inferType e) (← inferType cE')) then
        return .done (← instantiateMVars cE')
    return .continue)
  replaceMainGoal [← g.replaceLocalDeclDefEq h t']

/-- `normalize_proof_constant c` replaces the auxiliary proof constant `c` in the goal by the
synthesized instance of its type. -/
elab "normalize_proof_constant " c:ident : tactic => do
  normalizeProofConstant (← realizeGlobalConstNoOverload c)

/-- `to_proof_constant c at h` replaces every closed proof of the type of the auxiliary proof
constant `c` in the type of `h` by `c`. -/
elab "to_proof_constant " c:ident " from " d:ident " at " h:ident : tactic => withMainContext do
  toProofConstantAt (← realizeGlobalConstNoOverload c) (← realizeGlobalConstNoOverload d)
    (← getFVarId h)

/-- `normalize_proof_constant c at h` replaces the auxiliary proof constant `c` in the type of `h` by
the synthesized instance of its type. -/
elab "normalize_proof_constant " c:ident " at " h:ident : tactic => withMainContext do
  normalizeProofConstantAt (← realizeGlobalConstNoOverload c) (← getFVarId h)

end NormalizeProofConstant

namespace NormalizeProofConstant
open Lean Meta Elab Tactic

partial def diffs (a b : Expr) (acc : Array (Expr × Expr)) : MetaM (Array (Expr × Expr)) := do
  let a := a.consumeMData.headBeta
  let b := b.consumeMData.headBeta
  if a == b || acc.size > 5 then return acc
  match a, b with
  | .app .., .app .. =>
    let as := a.getAppArgs
    let bs := b.getAppArgs
    if as.size != bs.size || a.getAppFn != b.getAppFn then return acc.push (a, b)
    let mut acc := acc
    for i in [:as.size] do
      acc ← diffs as[i]! bs[i]! acc
    return acc
  | .lam _ ta ba _, .lam _ tb bb _ => diffs ba bb (← diffs ta tb acc)
  | _, _ => return acc.push (a, b)

elab "diff_with " h:term : tactic => withMainContext do
  let e ← elabTerm h none
  let t ← instantiateMVars (← inferType e)
  let g ← instantiateMVars (← (← getMainGoal).getType)
  for (a, b) in ← diffs t g #[] do
    logInfo m!"DIFF{indentExpr a}\nvs{indentExpr b}"
end NormalizeProofConstant

namespace NormalizeProofConstant
open Lean Meta Elab Tactic

/-- Replace, in the goal, every closed application of the constant `d` whose type is that of
the constant `c` by `c`. -/
def toProofConstant (c d : Name) : TacticM Unit := withMainContext do
  let g ← getMainGoal
  let t ← instantiateMVars (← g.getType)
  let t' ← Meta.transform t (pre := fun e => do
    if e.hasLooseBVars then return .continue
    if e.getAppFn.isConstOf d then
      let cE ← mkConstWithFreshMVarLevels c
      if (← isDefEq (← inferType e) (← inferType cE)) then
        return .done (← instantiateMVars cE)
    return .continue)
  replaceMainGoal [← g.replaceTargetDefEq t']

/-- `to_proof_constant c from d` replaces, in the goal, every closed application of `d` which is a
proof of the type of the auxiliary proof constant `c` by `c`. -/
elab "to_proof_constant " c:ident " from " d:ident : tactic => withMainContext do
  toProofConstant (← realizeGlobalConstNoOverload c) (← realizeGlobalConstNoOverload d)

end NormalizeProofConstant
