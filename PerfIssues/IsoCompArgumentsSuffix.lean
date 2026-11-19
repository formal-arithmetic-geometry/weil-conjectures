
open Lean Lean.Meta

set_option maxHeartbeats 10000000

private partial def isoLets (e : Expr) : Expr :=
  match e with
  | .letE _ _ value body _ => isoLets (body.instantiate1 value)
  | _ => e

private def compHead (e : Expr) : String :=
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
  match (← getConstInfo `CategoryTheory.Functor.comp) with
  | .defnInfo d =>
    logInfo m!"Functor.comp hint={match d.hints with | .regular h => s!"regular {h}" | .abbrev => "abbrev" | .opaque => "opaque"}"
  | _ => pure ()
  let info ← getConstInfo `AlgebraicGeometry.ProEtale.homologyIntegersTowerIso
  lambdaTelescope (info.value! (allowOpaque := true)) fun _ rawBody => do
    let lctx ← getLCtx
    let body := isoLets rawBody
    let args := body.getAppArgs
    let finalArg := args[6]!
    let appSoFar := mkAppN body.getAppFn (args.extract 0 6)
    let .ok actual := Kernel.check env lctx finalArg
      | throwError "final iso argument did not Kernel-check"
    let .ok fnType := Kernel.check env lctx appSoFar
      | throwError "Iso.trans prefix did not Kernel-check"
    let .ok (.forallE _ expected _ _) := Kernel.whnf env lctx fnType
      | throwError "Iso.trans final binder missing"
    for endpoint in [2, 3] do
      let left := actual.getAppArgs[endpoint]!
      let right := expected.getAppArgs[endpoint]!
      let la := left.getAppArgs
      let ra := right.getAppArgs
      logInfo m!"endpoint {endpoint}: {compHead left}/{compHead right}; args={la.size}/{ra.size}; same head={left.getAppFn == right.getAppFn}"
      for i in [:min la.size ra.size] do
        let a := la[i]!
        let b := ra[i]!
        let start ← IO.monoMsNow
        let result := Kernel.isDefEq env lctx a b
        let stop ← IO.monoMsNow
        logInfo m!"endpoint {endpoint} arg {i}: {compHead a}/{compHead b}, structural={a == b}, defeq={stop - start} ms, result={match result with | .ok true => "equal" | .ok false => "unequal" | .error _ => "error"}"
