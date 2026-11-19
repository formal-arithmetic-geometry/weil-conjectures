
open Lean Lean.Meta

set_option maxHeartbeats 10000000

private def eqHead (e : Expr) : String :=
  match e.getAppFn with
  | .const n _ => s!"const {n}"
  | .proj n i _ => s!"proj {n}.{i}"
  | .fvar .. => "fvar"
  | .bvar i => s!"bvar {i}"
  | .lam .. => "lambda"
  | .forallE .. => "forall"
  | .letE .. => "let"
  | .mdata .. => "metadata"
  | _ => "other"

private partial def peelEqLambdas (e : Expr) : Expr :=
  match e with
  | .lam _ _ b _ => peelEqLambdas b
  | _ => e

run_meta do
  let env ← getEnv
  match (← getConstInfo `Eq.mpr) with
  | .defnInfo d =>
    logInfo m!"Eq.mpr hint={match d.hints with | .regular h => s!"regular {h}" | .abbrev => "abbrev" | .opaque => "opaque"}; immediate post-lambda head={eqHead (peelEqLambdas d.value)}"
  | _ => logInfo m!"Eq.mpr is not a definition"
  let info ← getConstInfo `AlgebraicGeometry.Etale.rawModuleScalar_pullback_module_formula
  let value := info.value! (allowOpaque := true)
  lambdaTelescope value fun _ body => do
    let lctx ← getLCtx
    let args := body.getAppArgs
    let arg := args[3]!
    let appSoFar := mkAppN body.getAppFn (args.extract 0 3)
    let .ok actual := Kernel.check env lctx arg
      | throwError "Eq.refl did not Kernel-check"
    let .ok fnType := Kernel.check env lctx appSoFar
      | throwError "Eq.mpr prefix did not Kernel-check"
    let .ok (.forallE _ expected _ _) := Kernel.whnf env lctx fnType
      | throwError "Eq.mpr final binder missing"
    logInfo m!"Eq.mpr final domain: actual={eqHead actual}, expected={eqHead expected}; args={actual.getAppArgs.size}/{expected.getAppArgs.size}"
    let la := actual.getAppArgs
    let ra := expected.getAppArgs
    for i in [:min la.size ra.size] do
      let a := la[i]!
      let b := ra[i]!
      let start ← IO.monoMsNow
      let result := Kernel.isDefEq env lctx a b
      let stop ← IO.monoMsNow
      logInfo m!"Eq domain arg {i}: {eqHead a}/{eqHead b}, structural={a == b}, defeq={stop - start} ms, result={match result with | .ok true => "equal" | .ok false => "unequal" | .error _ => "error"}"
