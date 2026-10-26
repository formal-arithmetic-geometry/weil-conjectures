/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Tactic.Basic

/-!

# First-order instantiation of lemmas

`fo_have h := lemma using a₁, …, aₙ` and `fo_apply lemma using a₁, …, aₙ` instantiate the
implicit arguments of `lemma` by *first-order matching* of the types of its explicit hypotheses
against the types of the given terms `aᵢ` (and, for `fo_apply`, of its conclusion against the
goal), instead of by unification.

On large terms (for instance composites of derived functors), the unifier may unfold definitions
as soon as two subterms are not syntactically equal, even when they only differ by proofs or by
the instance path of an instance, and then run out of heartbeats. First-order matching assigns a
metavariable of the pattern directly to the corresponding subterm, compares applications with
the same head argument by argument, accepts any two proofs (proof irrelevance), and only falls
back to `isDefEq` on the smallest subterms where the two sides differ.

-/

public meta section

open Lean Meta Elab Tactic

namespace Mathlib.Tactic.FirstOrderApply

/-- First-order matching of a pattern `p` (containing unassigned metavariables) against `e`. The
`cache` records the pairs already matched, so that shared subterms are visited once. -/
partial def foMatchAux (cache : IO.Ref (Std.HashSet (Expr × Expr))) (p e : Expr)
    (bound : Array FVarId) : MetaM Bool := do
  let p := p.consumeMData
  let e := e.consumeMData
  if p == e then return true
  if (← cache.get).contains (p, e) then return true
  if !p.isMVar then
    if ← isProof e then return true
  let fallback : MetaM Bool := do
    if ← isProof e then return true
    trace[debug] "isDefEq fallback: {p.getAppFn} vs {e.getAppFn}"
    let r ← isDefEq p e
    trace[debug] "  -> {r}"
    return r
  let r ← do
    match p with
    | .mvar m =>
      if ← m.isAssigned then
        let v ← instantiateMVars p
        if v == e then pure true else foMatchAux cache v e bound
      else if ← m.isDelayedAssigned then
        fallback
      else if !bound.isEmpty && (← bound.anyM fun x => exprDependsOn e x) then
        fallback
      else
        m.assign e
        pure true
    | .forallE n d₁ b₁ bi =>
      match e with
      | .forallE _ d₂ b₂ _ =>
        if ← foMatchAux cache d₁ d₂ bound then
          withLocalDecl n bi (← instantiateMVars d₂) fun x => do
            foMatchAux cache (b₁.instantiate1 x) (b₂.instantiate1 x) (bound.push x.fvarId!)
        else pure false
      | _ => fallback
    | .app .. =>
      let fp := p.getAppFn
      let fe := e.getAppFn
      let ap := p.getAppArgs
      let ae := e.getAppArgs
      let sameHead : Bool := ap.size == ae.size && match fp, fe with
        | .const n₁ l₁, .const n₂ l₂ => n₁ == n₂ && l₁.length == l₂.length
        | .fvar f₁, .fvar f₂ => f₁ == f₂
        | _, _ => false
      if sameHead then
        let ok ← commitWhen do
          for (u, v) in fp.constLevels!.zip fe.constLevels! do
            unless ← isLevelDefEq u v do return false
          for i in (List.range ap.size).reverse do
            unless ← foMatchAux cache ap[i]! ae[i]! bound do return false
          return true
        if ok then pure true else fallback
      else if fp.isConst && fe.isConst then
        trace[debug] "foMatch: head mismatch {fp} vs {fe}"
        let unfoldAbbrev (x : Expr) : MetaM (Option Expr) := do
          let .const n _ := x.getAppFn | return none
          unless ← isReducible n do return none
          if (← getProjectionFnInfo? n).isSome then return none
          if (← isInstance n) then return none
          unfoldDefinition? x
        if let some p' ← unfoldAbbrev p then foMatchAux cache p' e bound
        else if let some e' ← unfoldAbbrev e then foMatchAux cache p e' bound
        else fallback
      else fallback
    | .sort u => match e with
      | .sort v => isLevelDefEq u v
      | _ => fallback
    | .const n₁ l₁ => match e with
      | .const n₂ l₂ =>
        if n₁ == n₂ && l₁.length == l₂.length then
          (l₁.zip l₂).allM fun (u, v) => isLevelDefEq u v
        else fallback
      | _ => fallback
    | _ => fallback
  if r then cache.modify (·.insert (p, e))
  return r

/-- First-order matching of a pattern `p` (containing unassigned metavariables) against `e`. -/
def foMatch (p e : Expr) : MetaM Bool := do
  foMatchAux (← IO.mkRef {}) p e #[]

/-- Elaborate a lemma name to its constant (with fresh universe metavariables), keeping all its
binders; other terms are elaborated as usual. -/
def elabLemma (f : Term) : TacticM Expr := do
  if f.raw.isIdent then
    if let some c := (← resolveGlobalName f.raw.getId).head? then
      if c.2.isEmpty then return ← mkConstWithFreshMVarLevels c.1
  elabTerm f none

/-- Instantiate the explicit hypotheses of `fe` by the terms `args` (in order, `_` leaving the
hypothesis open), after matching the conclusion against `target?` if given. Returns the
instantiated proof and the remaining hypotheses. -/
def foInstantiate (fe : Expr) (args : Array Term) (target? : Option Expr) :
    TacticM (Expr × Array MVarId) := do
  let fty ← inferType fe
  let (mvs, bis, concl) ← forallMetaTelescopeReducing fty
  if let some target := target? then
    unless ← foMatch concl target do
      throwError "fo_apply: the conclusion{indentExpr concl}\ndoes not match the goal"
  -- the explicit binders, with the given terms
  let mut given : Array (Nat × Nat) := #[]
  let mut newGoals : Array MVarId := #[]
  let mut k := 0
  for i in [:mvs.size] do
    if bis[i]! == .default then
      if h : k < args.size then
        if args[k].raw.isOfKind ``Lean.Parser.Term.hole then
          newGoals := newGoals.push mvs[i]!.mvarId!
        else
          given := given.push (i, k)
        k := k + 1
      else
        newGoals := newGoals.push mvs[i]!.mvarId!
  -- elaborate the given terms; match the proofs first, then the data
  let mut elabd : Array (Nat × Nat × Expr × Bool) := #[]
  for (i, k') in given do
    let a ← elabTerm args[k']! none
    elabd := elabd.push (i, k', a, ← isProof a)
  for pass in [true, false] do
    for (i, k', a, isPf) in elabd do
      if isPf == pass then
        let ty ← instantiateMVars (← inferType mvs[i]!)
        let aty ← instantiateMVars (← inferType a)
        unless ← foMatch ty aty do
          throwError "fo_apply: could not match argument {k' + 1} of type{indentExpr aty}"
        mvs[i]!.mvarId!.assign a
  for i in [:mvs.size] do
    if bis[i]! == .instImplicit then
      unless ← mvs[i]!.mvarId!.isAssigned do
        let inst ← synthInstance (← instantiateMVars (← inferType mvs[i]!))
        mvs[i]!.mvarId!.assign inst
  let goals ← newGoals.filterM fun g => return !(← g.isAssigned)
  return (← instantiateMVars (mkAppN fe mvs), goals)

/-- `fo_have h := lemma using a₁, …, aₙ` adds `h : (the conclusion of lemma)`, where the
explicit hypotheses of `lemma` are the `aᵢ` (`_` for a hypothesis left as a new goal) and the
implicit arguments are found by first-order matching of the types. -/
elab "fo_have " h:ident " := " f:term:max " using " args:term,* : tactic =>
  withMainContext do
    let fe ← elabLemma f
    let (pf, newGoals) ← foInstantiate fe args.getElems none
    let ty ← instantiateMVars (← inferType pf)
    let g' ← (← getMainGoal).assert h.getId ty pf
    let (_, g'') ← g'.intro1P
    replaceMainGoal (g'' :: newGoals.toList)

/-- `fo_apply lemma using a₁, …, aₙ` closes the goal by `lemma`, matching its conclusion against
the goal and its explicit hypotheses against the `aᵢ` first-order (`_` for a hypothesis left as
a new goal). -/
elab "fo_apply " f:term:max " using " args:term,* : tactic =>
  withMainContext do
    let g ← getMainGoal
    let fe ← elabLemma f
    let (pf, newGoals) ← foInstantiate fe args.getElems (some (← instantiateMVars (← g.getType)))
    g.assign pf
    replaceMainGoal newGoals.toList

end Mathlib.Tactic.FirstOrderApply
