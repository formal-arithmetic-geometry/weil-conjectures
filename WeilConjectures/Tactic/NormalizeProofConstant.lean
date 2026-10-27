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

partial def diffs (a b : Expr) (acc : Array (Expr × Expr)) (path : List Name := []) :
    MetaM (Array (Expr × Expr)) := do
  let a := a.consumeMData.headBeta
  let b := b.consumeMData.headBeta
  if a == b || acc.size > 200 then return acc
  match a, b with
  | .app .., .app .. =>
    let as := a.getAppArgs
    let bs := b.getAppArgs
    if as.size != bs.size || a.getAppFn != b.getAppFn then return acc.push (a, b)
    let mut acc := acc
    for i in [:as.size] do
      let n := acc.size
      acc ← diffs as[i]! bs[i]! acc ((a.getAppFn.constName?.getD `_) :: path)
      if acc.size > n && as[i]!.isFVar && bs[i]!.isFVar then
        logInfo m!"PATH {path.reverse} {a.getAppFn} arg {i}"
    return acc
  | .lam _ ta ba _, .lam _ tb bb _ => diffs ba bb (← diffs ta tb acc)
  | _, _ => return acc.push (a, b)

elab "diff_with " h:term : tactic => withMainContext do
  let e ← elabTerm h none
  let t ← instantiateMVars (← inferType e)
  let g ← instantiateMVars (← (← getMainGoal).getType)
  let mut seen : Array (Expr × Expr) := #[]
  for (a, b) in ← diffs t g #[] do
    unless seen.contains (a, b) do
      seen := seen.push (a, b)
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

namespace NormalizeProofConstant
open Lean Meta Elab Tactic

/-- `whnfR_apps d at h` replaces, in the type of `h`, every application of the constant `d`, and
every projection out of one, by its weak head normal form (for reducible, resp. default,
transparency). -/
elab "whnfR_apps " d:ident " at " h:ident : tactic => withMainContext do
  let dn ← realizeGlobalConstNoOverload d
  let fv ← getFVarId h
  let g ← getMainGoal
  let t ← instantiateMVars (← fv.getType)
  let t' ← Meta.transform t (pre := fun e => do
    if e.hasLooseBVars then return .continue
    match e with
    | .proj _ _ s =>
      if s.getAppFn.isConstOf dn then
        let e' ← whnf e
        if e' != e then return .done e'
      return .continue
    | _ =>
      if let .const f _ := e.getAppFn then
        if (← getEnv).isProjectionFn f && e.getAppNumArgs > 0 &&
            e.appArg!.getAppFn.isConstOf dn then
          let e' ← whnf e
          if e' != e then return .done e'
      if e.getAppFn.isConstOf dn then
        let e' ← whnfR e
        if e' != e then return .done e'
      return .continue)
  replaceMainGoal [← g.replaceLocalDeclDefEq fv t']

end NormalizeProofConstant

namespace NormalizeProofConstant
open Lean Meta Elab Tactic

/-- `replace_defeq a with b at h` replaces every occurrence of the term `a` in the type of `h` by
the definitionally equal term `b`. -/
elab "replace_defeq " a:term " with " b:term " at " h:ident : tactic => withMainContext do
  let a ← instantiateMVars (← elabTerm a none)
  let b ← instantiateMVars (← elabTerm b none)
  unless ← isDefEq a b do throwError "replace_defeq: the terms are not definitionally equal"
  let fv ← getFVarId h
  let g ← getMainGoal
  let t ← instantiateMVars (← fv.getType)
  let t' := t.replace fun e => if e == a then some b else none
  replaceMainGoal [← g.replaceLocalDeclDefEq fv t']

end NormalizeProofConstant

namespace NormalizeProofConstant
open Lean Meta Elab Tactic

/-- `exact_kernel h` closes the goal with `h` without checking that the type of `h` and the
goal agree: the definitional equality is left to the kernel. Use only when the elaborator's
check is known to unfold large definitions while the kernel's is cheap. -/
elab "exact_kernel " h:term : tactic => withMainContext do
  let g ← getMainGoal
  g.assign (← elabTerm h none)
  replaceMainGoal []

end NormalizeProofConstant

namespace NormalizeProofConstant
open Lean Meta Elab Tactic

/-- The closed proofs occurring in `e` (outermost ones), with their types. -/
partial def closedProofs (e : Expr) (acc : Std.HashMap Expr Expr) :
    MetaM (Std.HashMap Expr Expr) := do
  if !e.hasLooseBVars && (← (try isProof e catch _ => pure false)) then
    let T ← instantiateMVars (← inferType e)
    if acc.contains T then return acc else return acc.insert T e
  match e with
  | .app f a => closedProofs a (← closedProofs f acc)
  | .lam _ t b _ | .forallE _ t b _ => closedProofs b (← closedProofs t acc)
  | .mdata _ b => closedProofs b acc
  | .proj _ _ b => closedProofs b acc
  | _ => return acc

/-- Replace every closed proof in `e` whose type is a key of `rep` by the representative. -/
def replaceProofs (rep : Std.HashMap Expr Expr) (e : Expr) : MetaM Expr :=
  Meta.transform e (pre := fun t => do
    if t.hasLooseBVars then return .continue
    if (← (try isProof t catch _ => pure false)) then
      let T ← instantiateMVars (← inferType t)
      if let some r := rep[T]? then return .done r
      return .done t
    return .continue)

/-- `unify_proofs_with h` replaces, in the goal and in the type of `h`, every closed proof by the
first closed proof of the same proposition occurring in the goal. -/
elab "unify_proofs_with " h:ident : tactic => withMainContext do
  let fv ← getFVarId h
  let g ← getMainGoal
  let G ← instantiateMVars (← g.getType)
  let H ← instantiateMVars (← fv.getType)
  let rep ← closedProofs H (← closedProofs G {})
  let G' ← replaceProofs rep G
  let H' ← replaceProofs rep H
  let g ← g.replaceTargetDefEq G'
  let g ← g.replaceLocalDeclDefEq fv H'
  replaceMainGoal [g]

end NormalizeProofConstant
