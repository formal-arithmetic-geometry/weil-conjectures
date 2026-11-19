
open Lean Lean.Meta

set_option pp.explicit true
set_option pp.universes true
set_option pp.maxSteps 100000

private def auditShape : Expr → String
  | .app .. => "app"
  | .const n _ => s!"const {n}"
  | .proj n i _ => s!"proj {n}.{i}"
  | .lam .. => "lambda"
  | .forallE .. => "forall"
  | .letE .. => "let"
  | .fvar .. => "fvar"
  | .bvar .. => "bvar"
  | .mdata .. => "metadata"
  | .sort .. => "sort"
  | .lit .. => "literal"
  | .mvar .. => "mvar"

private def auditHint : ReducibilityHints → String
  | .abbrev => "abbrev"
  | .opaque => "opaque"
  | .regular h => s!"regular height {h}"

private def auditDescribe (label : String) (e : Expr) : MetaM Unit := do
  let args := e.getAppArgs
  let head := e.getAppFn
  logInfo m!"{label}: outer={auditShape e}; head={auditShape head}; args={args.size}"
  match head with
  | .const n ls =>
    logInfo m!"{label}: universes {ls}"
    match (← getConstInfo n) with
    | .defnInfo d =>
      logInfo m!"{label}: definition, Kernel hint {auditHint d.hints}, body outer={auditShape d.value}, body head={auditShape d.value.getAppFn}"
    | .thmInfo _ => logInfo m!"{label}: theorem"
    | .axiomInfo _ => logInfo m!"{label}: axiom"
    | _ => logInfo m!"{label}: other declaration kind"
  | .proj n i major =>
    logInfo m!"{label}: projection {n}.{i}, major outer={auditShape major}, major head={auditShape major.getAppFn}"
  | _ => pure ()
  for i in [:min args.size 32] do
    let a := args[i]!
    logInfo m!"{label}: arg {i} outer={auditShape a}, head={auditShape a.getAppFn}"

private partial def auditFirstDiff (a b : Expr) (path : String := "root") :
    Option (String × Expr × Expr) :=
  if a == b then none else
    match a, b with
    | .app f x, .app g y =>
      (auditFirstDiff f g (path ++ ".fn")).orElse fun _ =>
        auditFirstDiff x y (path ++ ".arg")
    | .forallE _ da ba _, .forallE _ db bb _ =>
      (auditFirstDiff da db (path ++ ".domain")).orElse fun _ =>
        auditFirstDiff ba bb (path ++ ".body")
    | .lam _ da ba _, .lam _ db bb _ =>
      (auditFirstDiff da db (path ++ ".domain")).orElse fun _ =>
        auditFirstDiff ba bb (path ++ ".body")
    | .letE _ ta va ba _, .letE _ tb vb bb _ =>
      (auditFirstDiff ta tb (path ++ ".type")).orElse fun _ =>
        (auditFirstDiff va vb (path ++ ".value")).orElse fun _ =>
          auditFirstDiff ba bb (path ++ ".body")
    | .proj na ia ea, .proj nb ib eb =>
      if na == nb && ia == ib then auditFirstDiff ea eb (path ++ ".proj")
      else some (path, a, b)
    | .mdata _ ea, .mdata _ eb => auditFirstDiff ea eb (path ++ ".mdata")
    | _, _ => some (path, a, b)

private partial def auditStripLambdas (e : Expr) (n : Nat := 0) : Nat × Expr :=
  match e with
  | .lam _ _ body _ => auditStripLambdas body (n + 1)
  | _ => (n, e)

private partial def auditStripForalls (e : Expr) (n : Nat := 0) : Nat × Expr :=
  match e with
  | .forallE _ _ body _ => auditStripForalls body (n + 1)
  | _ => (n, e)

run_meta do
  let env ← getEnv
  let name := `AUDIT_TARGET
  let info ← getConstInfo name
  let value := info.value! (allowOpaque := true)
  logInfo m!"AUDIT declaration {name}; original value and declared type read from the current environment"
  let start ← IO.monoMsNow
  let result := Kernel.check env {} value
  let stop ← IO.monoMsNow
  logInfo m!"Kernel.check(value) {stop - start} ms"
  match result with
  | .error _ => logInfo m!"value replay failed"
  | .ok inferred =>
    auditDescribe "actual inferred type" inferred
    auditDescribe "expected declared type" info.type
    let (actualBinders, actualResult) := auditStripForalls inferred
    let (expectedBinders, expectedResult) := auditStripForalls info.type
    logInfo m!"result binders actual={actualBinders}, expected={expectedBinders}"
    auditDescribe "actual result" actualResult
    auditDescribe "expected result" expectedResult
    let startEq ← IO.monoMsNow
    let equal := Kernel.isDefEq env {} inferred info.type
    let stopEq ← IO.monoMsNow
    logInfo m!"final conversion={stopEq - startEq} ms, result={match equal with | .ok true => "equal" | .ok false => "unequal" | .error _ => "error"}"
    match auditFirstDiff inferred info.type with
    | none => logInfo m!"final type pair structurally identical"
    | some (path, a, b) =>
      logInfo m!"first structural divergence {path}"
      auditDescribe "divergence actual" a
      auditDescribe "divergence expected" b
  let (binders, body) := auditStripLambdas value
  logInfo m!"value binders {binders}"
  auditDescribe "value body" body
