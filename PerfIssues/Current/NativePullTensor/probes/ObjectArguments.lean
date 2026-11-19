module

import all WeilConjectures.WeilSheaf.Native.NativePullTensor

open Lean Lean.Meta

set_option maxHeartbeats 10000000

private def objectHead (e : Expr) : String :=
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
    let actualEndpoints := actual.getAppArgs
    let expectedEndpoints := expected.getAppArgs
    for (endpoint, argIndex) in [(2, 6), (3, 7)] do
      let leftEndpoint := actualEndpoints[endpoint]!
      let rightEndpoint := expectedEndpoints[endpoint]!
      let leftArgs := leftEndpoint.getAppArgs
      let rightArgs := rightEndpoint.getAppArgs
      let left := leftArgs[argIndex]!
      let right := rightArgs[argIndex]!
      logInfo m!"endpoint {endpoint} Functor.obj: head={objectHead left}/{objectHead right}; args={left.getAppArgs.size}/{right.getAppArgs.size}"
      let la := left.getAppArgs
      let ra := right.getAppArgs
      for i in [:min la.size ra.size] do
        let a := la[i]!
        let b := ra[i]!
        let start ← IO.monoMsNow
        let result := Kernel.isDefEq env lctx a b
        let stop ← IO.monoMsNow
        logInfo m!"endpoint {endpoint} obj arg {i}: {objectHead a}/{objectHead b}, structural={a == b}, defeq={stop - start} ms, result={match result with | .ok true => "equal" | .ok false => "unequal" | .error _ => "error"}"
