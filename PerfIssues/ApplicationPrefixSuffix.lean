
open Lean Lean.Meta

set_option pp.explicit true
set_option pp.universes true
set_option maxHeartbeats 10000000

private def appHead (e : Expr) : String :=
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
  let name := `AUDIT_TARGET
  let startIndex : Nat := AUDIT_START
  let info ← getConstInfo name
  let value := info.value! (allowOpaque := true)
  lambdaTelescope value fun xs body => do
    let lctx ← getLCtx
    let args := body.getAppArgs
    logInfo m!"{name}: binders={xs.size}, body head={appHead body}, args={args.size}"
    let mut appSoFar := body.getAppFn
    for i in [:args.size] do
      let arg := args[i]!
      if i >= startIndex then
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
            logInfo m!"arg {i}: term={appHead arg}, actual type={appHead actual}, expected domain={appHead expected}, structurally equal={actual == expected}"
            let startEq ← IO.monoMsNow
            let result := Kernel.isDefEq env lctx actual expected
            let stopEq ← IO.monoMsNow
            logInfo m!"arg {i}: own check={stopArg - startArg} ms, prefix check={stopFn - startFn} ms, domain conversion={stopEq - startEq} ms, result={match result with | .ok true => "equal" | .ok false => "unequal" | .error _ => "error"}"
          | _ => logInfo m!"arg {i}: function type not Pi"
        | _, _ => logInfo m!"arg {i}: argument or prefix failed Kernel.check"
      appSoFar := mkApp appSoFar arg
