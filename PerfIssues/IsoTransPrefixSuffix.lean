
open Lean Lean.Meta

set_option maxHeartbeats 10000000

private partial def instantiateRecordedLets (e : Expr) : Expr :=
  match e with
  | .letE _ _ value body _ => instantiateRecordedLets (body.instantiate1 value)
  | _ => e

private def isoHead (e : Expr) : String :=
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

run_meta do
  let env ← getEnv
  let info ← getConstInfo `AlgebraicGeometry.ProEtale.homologyIntegersTowerIso
  let value := info.value! (allowOpaque := true)
  lambdaTelescope value fun xs rawBody => do
    let lctx ← getLCtx
    let body := instantiateRecordedLets rawBody
    let args := body.getAppArgs
    logInfo m!"PR1624: opened {xs.size} binders; post-let head={isoHead body}; args={args.size}"
    let mut appSoFar := body.getAppFn
    for i in [:args.size] do
      let arg := args[i]!
      if i >= 5 then
        let startArg ← IO.monoMsNow
        let argResult := Kernel.check env lctx arg
        let stopArg ← IO.monoMsNow
        let startFn ← IO.monoMsNow
        let fnResult := Kernel.check env lctx appSoFar
        let stopFn ← IO.monoMsNow
        match argResult, fnResult with
        | .ok actual, .ok fnType =>
          match Kernel.whnf env lctx fnType with
          | .ok (.forallE _ expected _ _) =>
            let startEq ← IO.monoMsNow
            let result := Kernel.isDefEq env lctx actual expected
            let stopEq ← IO.monoMsNow
            logInfo m!"arg {i}: term={isoHead arg}, actual={isoHead actual}, expected={isoHead expected}; own={stopArg - startArg} ms, prefix={stopFn - startFn} ms, domain={stopEq - startEq} ms, result={match result with | .ok true => "equal" | .ok false => "unequal" | .error _ => "error"}"
          | _ => logInfo m!"arg {i}: expected type not Pi"
        | _, _ => logInfo m!"arg {i}: argument or prefix failed"
      appSoFar := mkApp appSoFar arg
