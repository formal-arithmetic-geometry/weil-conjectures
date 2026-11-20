module

import all WeilConjectures.WeilSheaf.Native.NativePullTensor

open Lean Lean.Meta

set_option maxHeartbeats 10000000
set_option diagnostics true
set_option diagnostics.threshold 1000

run_meta do
  setEnv (Kernel.enableDiag (← getEnv) true)
  let info ← getConstInfo `AlgebraicGeometry.ProEtaleWeilSheaf.nativePullTotalTensor
  let .defnInfo d := info | throwError "expected a definition"
  lambdaTelescope d.value fun xs body => do
    let mut expected := d.type
    for x in xs do
      match expected with
      | .forallE _ _ rest _ => expected := rest.instantiate1 x
      | _ => throwError "declared type has too few binders"
    let .ok actual := Kernel.check (← getEnv) (← getLCtx) body
      | throwError "original value body did not Kernel-check"
    let actualEndpoints := actual.getAppArgs
    let expectedEndpoints := expected.getAppArgs
    let mut alignedExpected := expected
    for (endpoint, argIndex) in [(2, 6), (3, 7)] do
      let leftObj := actualEndpoints[endpoint]!.getAppArgs[argIndex]!
      let rightObj := expectedEndpoints[endpoint]!.getAppArgs[argIndex]!
      let la := leftObj.getAppArgs
      let ra := rightObj.getAppArgs
      let aligned := mkAppN rightObj.getAppFn (ra.set! 4 la[4]!)
      let .ok alignedType := Kernel.check (← getEnv) (← getLCtx) aligned
        | throwError "aligned endpoint did not Kernel-check"
      let .ok rightType := Kernel.check (← getEnv) (← getLCtx) rightObj
        | throwError "original endpoint did not Kernel-check"
      unless alignedType == rightType do
        throwError "aligned endpoint changed its checked type"
      alignedExpected := alignedExpected.replace fun e =>
        if e == rightObj then some aligned else none
      logInfo m!"endpoint {endpoint}: changed={alignedExpected != expected}; trigger aligned"
    let alignedType ← mkForallFVars xs alignedExpected
    logInfo "preparation diagnostics"
    setEnv (Kernel.resetDiag (← getEnv))
    for (label, name, type) in
        [("E0 original", `auditNativeE0, d.type),
         ("aligned", `auditNativeAligned, alignedType),
         ("E3 restored", `auditNativeE3, d.type)] do
      logInfo m!"checking {label}"
      let start ← IO.monoMsNow
      let .ok checked := (← getEnv).addDeclCore 0 0
          (.defnDecl { d with name := name, type := type }) (cancelTk? := none)
        | throwError "synchronous declaration check failed"
      let diag := Kernel.getDiagnostics checked
      logInfo m!"{label}: kernel counters enabled={Kernel.isDiagnosticsEnabled checked}"
      for name in [`CategoryTheory.Functor.obj, `CategoryTheory.Functor.map,
          `CategoryTheory.NatTrans.app, `CategoryTheory.CategoryStruct.comp, `Eq.ndrec] do
        logInfo m!"{label}: unfold {name} = {(diag.unfoldCounter.find? name).getD 0}"
      setEnv (Kernel.resetDiag checked)
      let stop ← IO.monoMsNow
      logInfo m!"{label}: {stop - start} ms"
