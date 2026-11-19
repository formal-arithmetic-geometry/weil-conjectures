
open Lean Lean.Meta

set_option maxHeartbeats 10000000

private partial def instantiateIsoLets (e : Expr) : Expr :=
  match e with
  | .letE _ _ value body _ => instantiateIsoLets (body.instantiate1 value)
  | _ => e

private def isoArgHead (e : Expr) : String :=
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
  lambdaTelescope value fun _ rawBody => do
    let lctx ← getLCtx
    let body := instantiateIsoLets rawBody
    let args := body.getAppArgs
    let finalArg := args[6]!
    let appSoFar := mkAppN body.getAppFn (args.extract 0 6)
    let .ok actual := Kernel.check env lctx finalArg
      | throwError "final iso argument did not Kernel-check"
    let .ok fnType := Kernel.check env lctx appSoFar
      | throwError "Iso.trans prefix did not Kernel-check"
    let .ok (.forallE _ expected _ _) := Kernel.whnf env lctx fnType
      | throwError "Iso.trans final binder missing"
    let la := actual.getAppArgs
    let ra := expected.getAppArgs
    logInfo m!"final Iso domain: {isoArgHead actual}/{isoArgHead expected}; args={la.size}/{ra.size}"
    for i in [:min la.size ra.size] do
      let a := la[i]!
      let b := ra[i]!
      let start ← IO.monoMsNow
      let result := Kernel.isDefEq env lctx a b
      let stop ← IO.monoMsNow
      logInfo m!"Iso domain arg {i}: {isoArgHead a}/{isoArgHead b}, structural={a == b}, defeq={stop - start} ms, result={match result with | .ok true => "equal" | .ok false => "unequal" | .error _ => "error"}"
