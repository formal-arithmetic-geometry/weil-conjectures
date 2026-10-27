module

public meta import Lean

public meta section

open Lean Meta Elab Tactic in
partial def diffExprs (a b : Expr) (path : List String) (acc : IO.Ref (Array (List String × Expr × Expr))) : MetaM Unit := do
  if a == b then return
  if (← isProof a) then
    let ta ← instantiateMVars (← inferType a); let tb ← instantiateMVars (← inferType b)
    if ta != tb then acc.modify (·.push ("PROOFTYPE" :: path, ta, tb))
    return
  let fa := a.getAppFn; let fb := b.getAppFn
  let aa := a.getAppArgs; let ab := b.getAppArgs
  if fa == fb && aa.size == ab.size && aa.size > 0 && path.length < 80 then
    let nm := match fa with | .const n _ => n.toString | _ => "?"
    for i in [0:aa.size] do diffExprs aa[i]! ab[i]! (s!"{nm}#{i}" :: path) acc
  else
    match a, b with
    | .mdata _ x, _ => diffExprs x b path acc
    | _, .mdata _ y => diffExprs a y path acc
    | .proj _ i x, .proj _ j y => if i == j then diffExprs x y (s!"proj{i}" :: path) acc else acc.modify (·.push (path, a, b))
    | _, _ => acc.modify (·.push (path, a, b))

open Lean Meta Elab Tactic in
elab "diff_with " t:term : tactic => withMainContext do
  let g ← getMainGoal
  let tgt ← instantiateMVars (← g.getType)
  let e ← elabTerm t none
  let ty ← instantiateMVars (← inferType e)
  let acc ← IO.mkRef #[]
  diffExprs ty tgt [] acc
  for (p, x, y) in ← acc.get do
    let p' := p.reverse.filter (fun s => !s.startsWith "?")
    logInfo m!"DIFF at {p'}:\n{x}\n=====\n{y}"

open Lean Meta Elab Tactic in
elab "diff_sub " t:term : tactic => withMainContext do
  let g ← getMainGoal
  let tgt ← instantiateMVars (← g.getType)
  let e ← elabTerm t none
  let ty ← instantiateMVars (← inferType e)
  let some (_, lhs, _) := ty.eq? | throwError "not an eq"
  let fn := lhs.getAppFn
  let n := lhs.getAppNumArgs
  let cands : Array Expr := Id.run <| tgt.foldlM (init := #[]) fun (acc : Array Expr) s =>
    pure (if s.getAppFn == fn && s.getAppNumArgs == n then acc.push s else acc)
  logInfo m!"{cands.size} candidates"
  for s in cands do
    let acc ← IO.mkRef #[]
    diffExprs lhs s [] acc
    let ds ← acc.get
    logInfo m!"candidate with {ds.size} diffs"
    for (p, x, y) in ds.toList.take 6 do
      let p' := p.reverse.filter (fun s => !s.startsWith "?")
      logInfo m!"DIFF at {p'}:\n{x}\n=====\n{y}"

open Lean Meta Elab Tactic in
elab "show_heads " c:ident : tactic => do
  let tgt ← instantiateMVars (← getMainTarget)
  let nm := c.getId
  let r ← IO.mkRef (0 : Nat)
  tgt.forEach fun s => do
    if s.getAppFn.constName? == some nm then
      r.modify (· + 1)
      if (← r.get) ≤ 3 then
        logInfo m!"{s.getAppNumArgs} args: {← ppExpr s}\nARGS: {s.getAppArgs.toList.take 6}"

open Lean Meta Elab Tactic in
elab "show_inst " c:ident : tactic => do
  let tgt ← instantiateMVars (← getMainTarget)
  let nm := c.getId
  tgt.forEach fun s => do
    if s.getAppFn.constName? == some nm && s.getAppNumArgs ≥ 3 then
      let a := s.getAppArgs
      logInfo m!"n={s.getAppNumArgs} cat={a[0]!.getAppFn} inst={a[2]!.getAppFn} instargs={a[2]!.getAppNumArgs} :: {a[2]!}"

open Lean Meta Elab Tactic in
elab "diff_goal" : tactic => do
  let tgt ← instantiateMVars (← getMainTarget)
  let some (_, a, b) := tgt.eq? | throwError "not an eq"
  let acc ← IO.mkRef #[]
  diffExprs a b [] acc
  let ds ← acc.get
  logInfo m!"{ds.size} diffs"
  for (p, x, y) in ds.toList.take 6 do
    let p' := p.reverse.filter (fun s => !s.startsWith "?")
    logInfo m!"DIFF at {p'}:\n{x}\n=====\n{y}"

open Lean Meta Elab Tactic in
elab "diff_goal_dsimp " "[" ids:ident,* "]" : tactic => do
  let tgt ← instantiateMVars (← getMainTarget)
  let some (_, a, b) := tgt.eq? | throwError "not an eq"
  let mut thms : SimpTheorems := {}
  for id in ids.getElems do
    thms ← thms.addConst (← realizeGlobalConstNoOverloadWithInfo id)
  let ctx ← Simp.mkContext (simpTheorems := #[thms])
  let (b', _) ← Lean.Meta.dsimp b ctx
  let (a', _) ← Lean.Meta.dsimp a ctx
  let acc ← IO.mkRef #[]
  diffExprs a' b' [] acc
  let ds ← acc.get
  logInfo m!"{ds.size} diffs after dsimp"
  for (p, x, y) in ds.toList.take 20 do
    let p' := p.reverse.filter (fun s => !s.startsWith "?")
    logInfo m!"DIFF at {p'}:\n{x}\n=====\n{y}"

end

public meta section
open Lean Meta Elab Tactic in
elab "diff_hyp " h:ident : tactic => withMainContext do
  let tgt ← instantiateMVars (← getMainTarget)
  let d ← getLocalDeclFromUserName h.getId
  let ty ← instantiateMVars d.type
  let acc ← IO.mkRef #[]
  diffExprs ty tgt [] acc
  let ds ← acc.get
  logInfo m!"{ds.size} hyp diffs"
  for (p, x, y) in ds.toList.take 6 do
    let p' := p.reverse.filter (fun s => !s.startsWith "?")
    logInfo m!"DIFF at {p'}:\n{x}\n=====\n{y}"
end
