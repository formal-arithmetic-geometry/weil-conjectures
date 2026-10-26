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

/-- The equations `h : α = β` inside a pattern `cast h x` met by `foMatch` against a term which is
not a cast (assigned at the end of `foInstantiate`, by congruence). -/
initialize castEqs : IO.Ref (Array (MVarId × Expr × Expr)) ← IO.mkRef #[]

/-- The pairs of subterms identified by `isDefEq` during the last matchings (for diagnostics). -/
initialize foPairs : IO.Ref (Array (Expr × Expr)) ← IO.mkRef #[]

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
    trace[debug] "isDefEq fallback: {p} \n VERSUS \n {e}"
    let r ← isDefEq p e
    trace[debug] "  -> {r}"
    if r then foPairs.modify (·.push (← instantiateMVars p, e))
    return r
  -- a pattern `cast h x` against a term which is not a cast: match `x`, and take `h := rfl`
  if p.isAppOfArity ``cast 4 && !e.isAppOfArity ``cast 4 then
    let args := p.getAppArgs
    if ← foMatchAux cache args[3]! e bound then
      let h := (← instantiateMVars args[2]!).consumeMData
      if let .mvar hm := h then
        unless ← hm.isAssigned do
          castEqs.modify (·.push (hm, args[0]!, args[1]!))
      return true
    else return false
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

/-- Normalize the head of an object `F.obj X` for `F` a composite, an inclusion `P.ι` or `𝟭`, and
of a morphism `P.ι.map f` to `f.hom`. -/
partial def normObj (e : Expr) : MetaM Expr := do
  if e.isAppOfArity `CategoryTheory.Functor.obj 6 then
    let F := e.getArg! 4
    let x := e.getArg! 5
    if F.isAppOfArity `CategoryTheory.Functor.comp 8 then
      let .const _ ls := F.getAppFn | return e
      let [vC, vD, vE, uC, uD, uE] := ls | return e
      let cs := F.getAppArgs
      let inner := mkAppN (mkConst `CategoryTheory.Functor.obj [vC, vD, uC, uD])
        #[cs[0]!, cs[1]!, cs[2]!, cs[3]!, cs[6]!, x]
      return ← normObj (mkAppN (mkConst `CategoryTheory.Functor.obj [vD, vE, uD, uE])
        #[cs[2]!, cs[3]!, cs[4]!, cs[5]!, cs[7]!, inner])
    if F.isAppOfArity `CategoryTheory.ObjectProperty.ι 3 then
      return ← mkAppM `CategoryTheory.ObjectProperty.FullSubcategory.obj #[x]
    if F.isAppOfArity `CategoryTheory.Functor.id 2 then
      return x
  if e.isAppOfArity `CategoryTheory.Functor.map 8 then
    let F := e.getArg! 4
    if F.isAppOfArity `CategoryTheory.ObjectProperty.ι 3 then
      try return ← mkAppM `CategoryTheory.InducedCategory.Hom.hom #[e.getArg! 7]
      catch _ => return e
  return e

/-- A cheap test for two terms to be definitionally equal: equal up to proofs, to `normObj` and
to the unfolding of head constants. -/
partial def plausibleEq (a b : Expr) (fuel : Nat := 64) : MetaM Bool := do
  if a == b then return true
  if fuel == 0 then return false
  if (← isProof a) then return (← isProof b)
  let a ← normObj a
  let b ← normObj b
  if a == b then return true
  let fa := a.getAppFn
  let fb := b.getAppFn
  let as := a.getAppArgs
  let bs := b.getAppArgs
  if fa == fb && as.size == bs.size then
    for i in [:as.size] do
      unless ← plausibleEq as[i]! bs[i]! (fuel - 1) do return false
    return true
  let unf (x : Expr) : MetaM (Option Expr) := do
    let .const n _ := x.getAppFn | return none
    unless ← isReducible n do return none
    if (← getProjectionFnInfo? n).isSome then return none
    unfoldDefinition? x
  if let some a' ← unf a then return ← plausibleEq a' b (fuel - 1)
  if let some b' ← unf b then return ← plausibleEq a b' (fuel - 1)
  -- one delta step of a non-reducible head, if it produces the head of the other side
  let unf1 (x : Expr) (target : Expr) : MetaM (Option Expr) := do
    let .const n _ := x.getAppFn | return none
    if (← getProjectionFnInfo? n).isSome then return none
    let some x' ← unfoldDefinition? x | return none
    let x' := x'.headBeta
    if x'.getAppFn.constName? == target.getAppFn.constName? then return some x'
    return none
  if let some a' ← unf1 a b then return ← plausibleEq a' b (fuel - 1)
  if let some b' ← unf1 b a then return ← plausibleEq a b' (fuel - 1)
  return false

/-- A proof of `HEq a b` for two definitionally equal terms, by congruence along their common
structure; the leaves are closed by `HEq.refl` (definitional unfolding at the leaves only) or by
proof irrelevance. -/
partial def heqProofAux (cache : IO.Ref (Std.HashMap (Expr × Expr) Expr)) (a b : Expr) :
    MetaM Expr := do
  let a := a.consumeMData
  let b := b.consumeMData
  if a == b then return ← mkHEqRefl a
  if let some p := (← cache.get)[(a, b)]? then return p
  let a ← normObj a
  let b ← normObj b
  let r ← do
    if (← isProof a) && (← isProof b) then
      pure (mkApp4 (mkConst ``proof_irrel_heq) (← inferType a) (← inferType b) a b)
    else
      let fa := a.getAppFn
      let fb := b.getAppFn
      let as := a.getAppArgs
      let bs := b.getAppArgs
      let finfo ← getFunInfoNArgs fa as.size
      -- descend only if the explicit arguments are plausibly definitionally equal
      let argsOk : MetaM Bool := do
        for i in [:as.size] do
          let x := as[i]!
          let y := bs[i]!
          if x == y then continue
          if h : i < finfo.paramInfo.size then
            unless finfo.paramInfo[i].binderInfo.isExplicit do continue
          if (← isProof x) then continue
          let x' ← normObj x
          let y' ← normObj y
          let hd (e : Expr) : Option Name := match e.getAppFn with
            | .const n _ => some n
            | _ => none
          if (hd x').isSome && hd x' == hd y' && x'.getAppNumArgs == y'.getAppNumArgs then
            continue
          unless ← plausibleEq x y do
            return false
        return true
      let sameHead : MetaM Bool := do
        if fa == fb then return true
        match fa, fb with
        | .const n₁ l₁, .const n₂ l₂ =>
          if n₁ == n₂ && l₁.length == l₂.length then
            (l₁.zip l₂).allM fun (u, v) => isLevelDefEq u v
          else return false
        | _, _ => return false
      let ok ← if as.size == bs.size && as.size > 0 then
          (do if ← sameHead then argsOk else pure false) else pure false
      if ok then
        let lem ← match fa with
          | .const n ls => do
            match ← mkHCongrWithArityForConst? n ls as.size with
            | some l => pure l
            | none => mkHCongrWithArity fa as.size
          | _ => mkHCongrWithArity fa as.size
        let mut args : Array Expr := #[]
        for i in [:as.size] do
          let h ← heqProofAux cache as[i]! bs[i]!
          let h ← if lem.argKinds[i]? == some .eq then
              (if as[i]! == bs[i]! then mkEqRefl as[i]! else do
                let α ← inferType as[i]!
                let u ← getLevel α
                pure (mkApp4 (mkConst ``eq_of_heq [u]) α as[i]! bs[i]! h))
            else pure h
          args := args.push as[i]! |>.push bs[i]! |>.push h
        pure (mkAppN lem.proof args)
      else
        mkHEqRefl a
  cache.modify (·.insert (a, b) r)
  return r

/-- Transport a proof `a : A` to `B`, along `heqProofAux` (if `A` and `B` differ). -/
def transport (a A B : Expr) : MetaM Expr := do
  if A == B then return a
  let h ← heqProofAux (← IO.mkRef {}) A B
  return mkApp4 (mkConst ``Eq.mp [.zero]) A B
    (mkApp4 (mkConst ``eq_of_heq [1]) (mkSort 0) A B h) a

/-- A proof of `l = r` (or `HEq l r`) for definitionally equal `l` and `r`, by congruence along their
common structure (`heqProofAux`), so that the kernel only compares the small subterms which differ. -/
def congrProof (ty : Expr) : MetaM (Option Expr) := do
  let ty ← whnfR (← instantiateMVars ty)
  if let some (α, l, r) := ty.eq? then
    if l == r then return some (← mkEqRefl l)
    let h ← heqProofAux (← IO.mkRef {}) l r
    let u ← getLevel α
    return some (mkApp4 (mkConst ``eq_of_heq [u]) α l r h)
  if let some (_, l, _, r) := ty.heq? then
    return some (← heqProofAux (← IO.mkRef {}) l r)
  return none

/-- Instantiate the explicit hypotheses of `fe` by the terms `args` (in order: `_` leaves the
hypothesis open, `rfl` and `HEq.rfl` prove it by congruence), after matching the conclusion against
`target?` if given. The implicit arguments are found by first-order matching; the given proofs and
the conclusion are transported to the instantiated types along congruence proofs. Returns the
instantiated proof and the remaining hypotheses. -/
def foInstantiate (fe : Expr) (args : Array Term) (target? : Option Expr) :
    TacticM (Expr × Array MVarId) := do
  castEqs.set #[]
  let fty ← inferType fe
  let (mvs, bis, concl) ← forallMetaTelescopeReducing fty
  if let some target := target? then
    unless ← foMatch concl target do
      throwError "fo_apply: the conclusion{indentExpr concl}\ndoes not match the goal"
  -- the explicit binders, with the given terms
  let mut given : Array (Nat × Nat) := #[]
  let mut refls : Array Nat := #[]
  let mut newGoals : Array MVarId := #[]
  let mut k := 0
  for i in [:mvs.size] do
    if bis[i]! == .default then
      if h : k < args.size then
        if args[k].raw.isOfKind ``Lean.Parser.Term.hole then
          newGoals := newGoals.push mvs[i]!.mvarId!
        else if args[k].raw.isIdent &&
            (args[k].raw.getId == `rfl || args[k].raw.getId == `HEq.rfl) then
          refls := refls.push i
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
        if !isPf then mvs[i]!.mvarId!.assign a
  for i in [:mvs.size] do
    if bis[i]! == .instImplicit then
      unless ← mvs[i]!.mvarId!.isAssigned do
        mvs[i]!.mvarId!.assign (← synthInstance (← instantiateMVars (← inferType mvs[i]!)))
  -- the equations of the casts, and the remaining implicit equations, by congruence
  for (m, α, β) in ← castEqs.get do
    unless ← m.isAssigned do
      let some p ← congrProof (← mkEq (← instantiateMVars α) (← instantiateMVars β)) | pure ()
      m.assign p
  for i in [:mvs.size] do
    unless ← mvs[i]!.mvarId!.isAssigned do
      if bis[i]! != .default then
        if let some p ← congrProof (← inferType mvs[i]!) then mvs[i]!.mvarId!.assign p
  -- reflexivity arguments, by congruence
  for i in refls do
    let some p ← congrProof (← inferType mvs[i]!)
      | throwError "fo_apply: `rfl` for a hypothesis which is not an equation"
    mvs[i]!.mvarId!.assign p
  -- transport the given proofs to the instantiated hypotheses
  for (i, _, a, isPf) in elabd do
    if isPf then
      let B ← instantiateMVars (← inferType mvs[i]!)
      let A ← instantiateMVars (← inferType a)
      mvs[i]!.mvarId!.assign (← transport a A B)
  let goals ← newGoals.filterM fun g => return !(← g.isAssigned)
  let pf ← instantiateMVars (mkAppN fe mvs)
  match target? with
  | some target => return (← transport pf (← instantiateMVars (← inferType pf)) target, goals)
  | none => return (pf, goals)

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
    let ms ← getMVars pf
    for m in ms do
      unless newGoals.contains m do
        logInfo m!"fo_apply: unassigned {mkMVar m} : {← inferType (mkMVar m)}"
    g.assign pf
    replaceMainGoal newGoals.toList

end Mathlib.Tactic.FirstOrderApply

namespace Mathlib.Tactic.FirstOrderApply

/-- Diagnostic: send each pair recorded in `foPairs` to the kernel as an auxiliary theorem
`p = e := rfl`, logging to `/tmp/fo.log` before each. -/
elab "fo_kernel_check_pairs" : tactic => withMainContext do
  let pairs ← foPairs.get
  let mut i := 0
  for (p, e) in pairs do
    IO.FS.withFile "/tmp/fo.log" .append fun h => h.putStrLn s!"kernel pair {i} start"
    let t0 ← IO.monoMsNow
    let p ← instantiateMVars p
    let ty ← mkEq p e
    let _ ← mkAuxTheorem ty (← mkEqRefl p)
    let t1 ← IO.monoMsNow
    IO.FS.withFile "/tmp/fo.log" .append fun h => h.putStrLn s!"kernel pair {i} ok {t1 - t0} ms"
    i := i + 1

/-- Diagnostic: clear the recorded pairs. -/
elab "fo_clear_pairs" : tactic => foPairs.set #[]

end Mathlib.Tactic.FirstOrderApply

namespace Mathlib.Tactic.FirstOrderApply

/-- Diagnostic variant of `fo_apply` checking each `isDefEq`-identified pair in the kernel. -/
elab "fo_apply_check " f:term:max " using " args:term,* : tactic =>
  withMainContext do
    foPairs.set #[]
    let g ← getMainGoal
    let fe ← elabLemma f
    let (pf, newGoals) ← foInstantiate fe args.getElems (some (← instantiateMVars (← g.getType)))
    -- check each explicit argument and the conclusion in the kernel separately
    let args := pf.getAppArgs
    let fty ← instantiateMVars (← inferType fe)
    let (_, _, _) ← forallMetaTelescopeReducing fty
    let mut ty := fty
    for i in [:args.size] do
      let .forallE _ d b bi := ty | break
      let a := args[i]!
      if bi == .default && (← isProof a) then
        IO.FS.withFile "/tmp/fo.log" .append fun h => h.putStrLn s!"kernel arg {i} start"
        let t0 ← IO.monoMsNow
        let _ ← mkAuxTheorem (← instantiateMVars d) a
        let t1 ← IO.monoMsNow
        IO.FS.withFile "/tmp/fo.log" .append fun h => h.putStrLn s!"kernel arg {i} ok {t1 - t0} ms"
      ty := b.instantiate1 a
    IO.FS.withFile "/tmp/fo.log" .append fun h => h.putStrLn "kernel concl start"
    let _ ← mkAuxTheorem (← instantiateMVars (← g.getType)) pf
    IO.FS.withFile "/tmp/fo.log" .append fun h => h.putStrLn "kernel concl ok"
    g.assign pf
    replaceMainGoal newGoals.toList

end Mathlib.Tactic.FirstOrderApply

namespace Mathlib.Tactic.FirstOrderApply

/-- Diagnostic: the maximal differing subterm pairs of two expressions (structural walk). -/
partial def structDiff (a b : Expr) (acc : IO.Ref (Array (Expr × Expr)))
    (parent : Option (Expr × Expr) := none) (under : Bool := false) (path : String := "") :
    MetaM Unit := do
  let a := a.consumeMData
  let b := b.consumeMData
  if a == b then return
  if (← acc.get).size ≥ 40 then return
  let fa := a.getAppFn
  let fb := b.getAppFn
  let as := a.getAppArgs
  let bs := b.getAppArgs
  if fa == fb && as.size == bs.size && as.size > 0 then
    let under' := under || fa.isConstOf `CategoryTheory.CategoryStruct.comp || fa.isConstOf `Prefunctor.map
    for i in [:as.size] do
      structDiff as[i]! bs[i]! acc (some (a, b)) under' s!"{path}/{fa.constName?.getD `x}#{i}"
  else
    if true then
      let pr := (a, b)
      unless (← acc.get).contains pr do
        acc.modify (·.push pr)
        IO.FS.withFile "/tmp/fo.log" .append fun h => h.putStrLn s!"PATH {path}"

/-- Diagnostic variant of `fo_apply`: kernel-check each structural difference between the goal and
the instantiated conclusion separately (logging to `/tmp/fo.log`), then fail. -/
elab "fo_apply_diff " f:term:max " using " args:term,* : tactic =>
  withMainContext do
    let g ← getMainGoal
    let fe ← elabLemma f
    let (pf, _) ← foInstantiate fe args.getElems (some (← instantiateMVars (← g.getType)))
    let concl ← instantiateMVars (← inferType pf)
    let acc ← IO.mkRef #[]
    structDiff concl (← instantiateMVars (← g.getType)) acc
    let mut i := 0
    for (a, b) in ← acc.get do
      let sa ← ppExpr a
      let sb ← ppExpr b
      IO.FS.withFile "/tmp/fo.log" .append fun h =>
        h.putStrLn s!"diff {i}: {sa} ||| {sb}"
      let t0 ← IO.monoMsNow
      let _ ← mkAuxTheorem (← mkEq a b) (← mkEqRefl a)
      let t1 ← IO.monoMsNow
      IO.FS.withFile "/tmp/fo.log" .append fun h => h.putStrLn s!"diff {i} ok {t1 - t0} ms"
      i := i + 1
    throwError "fo_apply_diff: done"

end Mathlib.Tactic.FirstOrderApply

namespace Mathlib.Tactic.FirstOrderApply

/-- Diagnostic variant of `fo_apply`: log the structural differences between the type of each
explicit proof argument and the instantiated binder type, and between the conclusion and the goal
(to `/tmp/fo.log`), then fail. -/
elab "fo_apply_argdiff " f:term:max " using " args:term,* : tactic =>
  withMainContext do
    let g ← getMainGoal
    let fe ← elabLemma f
    let (pf, _) ← foInstantiate fe args.getElems (some (← instantiateMVars (← g.getType)))
    let pargs := pf.getAppArgs
    let mut ty ← instantiateMVars (← inferType fe)
    for i in [:pargs.size] do
      let .forallE _ d b bi := ty | break
      let a := pargs[i]!
      if bi == .default && (← isProof a) then
        let acc ← IO.mkRef #[]
        structDiff (← instantiateMVars d) (← instantiateMVars (← inferType a)) acc
        for (x, y) in ← acc.get do
          let sx ← withOptions (fun o => o.setBool `pp.explicit true |>.setBool `pp.proofs true) (ppExpr x)
          let sy ← withOptions (fun o => o.setBool `pp.explicit true |>.setBool `pp.proofs true) (ppExpr y)
          IO.FS.withFile "/tmp/fo.log" .append fun h =>
            h.putStrLn s!"arg {i}:\n  {sx}\n  |||\n  {sy}"
      ty := b.instantiate1 a
    let acc ← IO.mkRef #[]
    structDiff (← instantiateMVars (← inferType pf)) (← instantiateMVars (← g.getType)) acc
    for (x, y) in ← acc.get do
      let sx ← ppExpr x
      let sy ← ppExpr y
      IO.FS.withFile "/tmp/fo.log" .append fun h => h.putStrLn s!"concl:\n  {sx}\n  |||\n  {sy}"
    throwError "fo_apply_argdiff: done"

end Mathlib.Tactic.FirstOrderApply

namespace Mathlib.Tactic.FirstOrderApply

/-- Diagnostic variant of `fo_apply`: kernel-check each `isDefEq`-identified pair separately. -/
elab "fo_apply_pairs " f:term:max " using " args:term,* : tactic =>
  withMainContext do
    foPairs.set #[]
    let g ← getMainGoal
    let fe ← elabLemma f
    let _ ← foInstantiate fe args.getElems (some (← instantiateMVars (← g.getType)))
    let mut i := 0
    for (p, e) in ← foPairs.get do
      let p ← instantiateMVars p
      let sp ← ppExpr p
      let se ← ppExpr e
      IO.FS.withFile "/tmp/fo.log" .append fun h => h.putStrLn s!"pair {i}: {sp} ||| {se}"
      let t0 ← IO.monoMsNow
      let _ ← mkAuxTheorem (← mkEq p e) (← mkEqRefl p)
      let t1 ← IO.monoMsNow
      IO.FS.withFile "/tmp/fo.log" .append fun h => h.putStrLn s!"pair {i} ok {t1 - t0} ms"
      i := i + 1
    throwError "fo_apply_pairs: done"

end Mathlib.Tactic.FirstOrderApply

namespace Mathlib.Tactic.FirstOrderApply


/-- `unify_proofs h₁ … hₙ`: in the goal and the hypotheses `hᵢ`, replace all proofs of the same
proposition (up to definitional equality of the propositions) by a single one. Afterwards, terms
which differed only by their proofs are syntactically equal, so that the kernel does not need to
unfold definitions to compare them.

The old and the new statement are related through an auxiliary definition
`aux := fun h₁ … hₘ ↦ T[h₁, …, hₘ]` abstracting all the proofs: the kernel compares
`aux p₁ … pₘ` with `aux q₁ … qₘ` argument by argument (by proof irrelevance), and does not need
to compare the two statements themselves. -/
elab "unify_proofs" hs:(ppSpace colGt ident)* : tactic => do
  let g ← getMainGoal
  let fvs ← g.withContext <| hs.mapM fun h => return (← getLocalDeclFromUserName h.getId).fvarId
  let (reverted, g) ← g.revert fvs
  let auxName ← Term.mkAuxName `unifyProofsAux
  let g ← g.withContext do
    let target ← instantiateMVars (← g.getType)
    let proofs ← IO.mkRef (#[] : Array (Expr × Expr))
    let visited ← IO.mkRef (Std.HashSet.emptyWithCapacity : Std.HashSet Expr)
    let rec visit (e : Expr) : MetaM Unit := do
      if (← visited.get).contains e then return
      visited.modify (·.insert e)
      if !e.hasLooseBVars && !e.isMVar then
        if ← isProof e then
          let ty ← instantiateMVars (← inferType e)
          unless ty.hasLooseBVars || ty.hasFVar && false do proofs.modify (·.push (ty, e))
          return
      match e with
      | .app f a => visit f; visit a
      | .lam _ t b _ | .forallE _ t b _ => visit t; visit b
      | .letE _ t v b _ => visit t; visit v; visit b
      | .mdata _ b => visit b
      | .proj _ _ b => visit b
      | _ => pure ()
    visit target
    -- the canonical proof of each proposition, the propositions being normalized by replacing
    -- their inner proofs by canonical ones
    let canonFor ← IO.mkRef (Std.HashMap.emptyWithCapacity : Std.HashMap Expr Expr)
    let normCache ← IO.mkRef (Std.HashMap.emptyWithCapacity : Std.HashMap Expr Expr)
    let rec canonOf (fuel : Nat) (p : Expr) : MetaM Expr := do
      let ty ← instantiateMVars (← inferType p)
      let ty ← normType fuel ty
      match (← canonFor.get)[ty]? with
      | some q => return q
      | none =>
        -- small propositions are also compared up to definitional equality
        if ty.approxDepth < 40 then
          for (ty₀, q) in (← canonFor.get).toList do
            if ty₀.getAppFn == ty.getAppFn && ty₀.approxDepth < 40 then
              if ← withNewMCtxDepth (withTransparency .instances (isDefEq ty₀ ty)) then
                canonFor.modify (·.insert ty q)
                return q
        canonFor.modify (·.insert ty p); return p
    , normType (fuel : Nat) (e : Expr) : MetaM Expr := do
      match fuel with
      | 0 => return e
      | fuel + 1 =>
      if let some r := (← normCache.get)[e]? then return r
      let r ← do
        if !e.hasLooseBVars && !e.isMVar && (← isProof e) then canonOf fuel e
        else match e with
        | .app f a => return e.updateApp! (← normType (fuel + 1) f) (← normType (fuel + 1) a)
        | .mdata _ b => return e.updateMData! (← normType (fuel + 1) b)
        | _ => return e
      normCache.modify (·.insert e r)
      return r
    let mut repl : Array (Expr × Expr × Expr) := #[]  -- (proof, its type, canonical proof)
    for (ty, p) in ← proofs.get do
      if repl.any (·.1 == p) then continue
      let q ← canonOf 8 p
      if q != p then repl := repl.push (p, ty, q)
    for (ty, q) in (← canonFor.get).toList do
      if ty.isAppOf `CategoryTheory.Precoherent then trace[debug] "canon {ty} := {q}"
    for (p, ty, q) in repl do
      if ty.isAppOf `CategoryTheory.Precoherent then trace[debug] "repl {p} ↦ {q}"
    if repl.isEmpty then return g
    -- the auxiliary definition abstracting the replaced proofs
    let auxBody ← withLocalDeclsDND (repl.mapIdx fun i (_, ty, _) => (Name.mkSimple s!"h{i}", ty))
      fun hs => do
        let body := target.replace fun e =>
          match repl.findIdx? (·.1 == e) with
          | some i => some hs[i]!
          | none => none
        mkLambdaFVars hs body
    let auxTy ← inferType auxBody
    let aux ← mkAuxDefinition auxName auxTy auxBody (compile := false)
    let oldT := mkAppN aux (repl.map (·.1))
    let newT := mkAppN aux (repl.map (·.2.2))
    let newTarget := (auxBody.beta (repl.map (·.2.2))).headBeta
    let next ← mkFreshExprSyntheticOpaqueMVar newTarget
    -- `next : newTarget ≡ aux q…`, `aux q… ≡ aux p…` (proof irrelevance), `aux p… ≡ target`
    g.assign (← mkExpectedTypeHint (← mkExpectedTypeHint (← mkExpectedTypeHint next newT) oldT)
      target)
    trace[debug] "unify_proofs: {repl.size} proofs replaced"
    pure next.mvarId!
  let (_, g) ← g.introNP reverted.size
  replaceMainGoal [g]

end Mathlib.Tactic.FirstOrderApply

namespace Mathlib.Tactic.FirstOrderApply

/-- Diagnostic: kernel-check `a = b` under a heartbeat limit; on failure, recurse into the
differing arguments, logging the minimal failing pairs to `/tmp/fo.log`. -/
partial def kernelBisect (a b : Expr) (depth : Nat) : MetaM Unit := do
  if a == b then return
  if ← isProof a then return
  let ok ← try
      withCurrHeartbeats <| withOptions (fun o => o.insert `maxHeartbeats (.ofNat 100000)) <|
        withTheReader Core.Context (fun c => { c with maxHeartbeats := 100000 * 1000 }) do
        let _ ← mkAuxTheorem (← mkEq a b) (← mkEqRefl a)
      pure true
    catch _ => pure false
  if ok then return
  let fa := a.getAppFn
  let fb := b.getAppFn
  let as := a.getAppArgs
  let bs := b.getAppArgs
  let mut recursed := false
  if fa == fb && as.size == bs.size && depth < 40 then
    for i in [:as.size] do
      if as[i]! != bs[i]! then
        if (← isDefEq (← inferType as[i]!) (← inferType bs[i]!)) then
          recursed := true
          kernelBisect as[i]! bs[i]! (depth + 1)
  unless recursed do
    let sa ← ppExpr a
    let sb ← ppExpr b
    IO.FS.withFile "/tmp/fo.log" .append fun h =>
      h.putStrLn s!"BISECT leaf (depth {depth}) {fa.constName?} / {fb.constName?}:\n  {sa}\n  |||\n  {sb}"

/-- Diagnostic variant of `fo_apply`: bisect the kernel check of each explicit proof argument. -/
elab "fo_apply_bisect " f:term:max " using " args:term,* : tactic =>
  withMainContext do
    let g ← getMainGoal
    let fe ← elabLemma f
    let (pf, _) ← foInstantiate fe args.getElems (some (← instantiateMVars (← g.getType)))
    let pargs := pf.getAppArgs
    let mut ty ← instantiateMVars (← inferType fe)
    for i in [:pargs.size] do
      let .forallE _ d b bi := ty | break
      let a := pargs[i]!
      if bi == .default && (← isProof a) then
        IO.FS.withFile "/tmp/fo.log" .append fun h => h.putStrLn s!"bisect arg {i}"
        kernelBisect (← instantiateMVars d) (← instantiateMVars (← inferType a)) 0
      ty := b.instantiate1 a
    throwError "fo_apply_bisect: done"

end Mathlib.Tactic.FirstOrderApply
