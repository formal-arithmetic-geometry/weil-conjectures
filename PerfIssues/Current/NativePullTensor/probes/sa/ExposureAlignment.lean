module

import all WeilConjectures.WeilSheaf.Native.NativePullTensor

open Lean Lean.Meta

set_option maxHeartbeats 10000000

run_meta do
  let env ← getEnv
  match (← getConstInfo `CategoryTheory.Functor.obj) with
  | .defnInfo d =>
    logInfo m!"Functor.obj: definition hint={match d.hints with | .regular h => s!"regular {h}" | .abbrev => "abbrev" | .opaque => "opaque"}"
  | .ctorInfo _ => logInfo m!"Functor.obj: constructor"
  | .recInfo _ => logInfo m!"Functor.obj: recursor"
  | _ => logInfo m!"Functor.obj: other declaration kind"
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
      let leftEndpointArgs := leftEndpoint.getAppArgs
      let rightEndpointArgs := rightEndpoint.getAppArgs
      let leftObj := leftEndpointArgs[argIndex]!
      let rightObj := rightEndpointArgs[argIndex]!
      let leftArgs := leftObj.getAppArgs
      let rightArgs := rightObj.getAppArgs
      let aligned := mkAppN rightObj.getAppFn (rightArgs.set! 4 leftArgs[4]!)
      let .ok alignedType := Kernel.check env lctx aligned
        | throwError "aligned object did not Kernel-check"
      let .ok rightType := Kernel.check env lctx rightObj
        | throwError "original right object did not Kernel-check"
      logInfo m!"endpoint {endpoint}: replacement only at Functor.obj argument 4; aligned object type structurally equal={alignedType == rightType}"
      for (label, a, b) in [("original", leftObj, rightObj),
          ("aligned", leftObj, aligned), ("control right/aligned", rightObj, aligned)] do
        let start ← IO.monoMsNow
        let result := Kernel.isDefEq env lctx a b
        let stop ← IO.monoMsNow
        logInfo m!"endpoint {endpoint} {label}: {stop - start} ms, result={match result with | .ok true => "equal" | .ok false => "unequal" | .error _ => "error"}"
