module

import all WeilConjectures.WeilSheaf.Native.NativePullTensor

open Lean Lean.Meta

set_option maxHeartbeats 10000000

private def endpointHead (e : Expr) : String :=
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

private partial def peelLambdas (e : Expr) : Expr :=
  match e with
  | .lam _ _ body _ => peelLambdas body
  | _ => e

run_meta do
  let env ← getEnv
  let info ← getConstInfo `AlgebraicGeometry.ProEtaleWeilSheaf.nativePullTotalTensor
  let value := info.value! (allowOpaque := true)
  lambdaTelescope value fun xs body => do
    let lctx ← getLCtx
    let .ok actual := Kernel.check env lctx body
      | throwError "body did not Kernel-check"
    let mut expected := info.type
    for x in xs do
      match expected with
      | .forallE _ _ rest _ => expected := rest.instantiate1 x
      | _ => throwError "declared type has too few binders"
    let leftArgs := actual.getAppArgs
    let rightArgs := expected.getAppArgs
    for endpoint in [2, 3] do
      let left := leftArgs[endpoint]!
      let right := rightArgs[endpoint]!
      logInfo m!"endpoint {endpoint}: actual={endpointHead left}, expected={endpointHead right}, app args={left.getAppArgs.size}/{right.getAppArgs.size}"
      if endpoint == 2 then
        match (← getConstInfo `CategoryTheory.Functor.comp) with
        | .defnInfo d =>
          logInfo m!"Functor.comp hint={match d.hints with | .regular h => s!"regular {h}" | .abbrev => "abbrev" | .opaque => "opaque"}; immediate body outer={endpointHead d.value}, after lambda binders={endpointHead (peelLambdas d.value)}"
        | _ => logInfo m!"Functor.comp is not a definition"
      let la := left.getAppArgs
      let ra := right.getAppArgs
      for i in [:min la.size ra.size] do
        let a := la[i]!
        let b := ra[i]!
        let start ← IO.monoMsNow
        let result := Kernel.isDefEq env lctx a b
        let stop ← IO.monoMsNow
        logInfo m!"endpoint {endpoint} arg {i}: {endpointHead a} / {endpointHead b}, structural={a == b}, defeq={stop - start} ms, result={match result with | .ok true => "equal" | .ok false => "unequal" | .error _ => "error"}"
