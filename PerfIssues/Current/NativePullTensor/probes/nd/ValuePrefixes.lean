module

import all WeilConjectures.WeilSheaf.Native.NativePullTensor

open Lean Lean.Meta

set_option pp.explicit true
set_option pp.universes true

run_meta do
  let env ← getEnv
  let info ← getConstInfo `AlgebraicGeometry.ProEtaleWeilSheaf.nativePullTotalTensor
  let value := info.value! (allowOpaque := true)
  lambdaTelescope value fun xs body => do
    let lctx ← getLCtx
    logInfo m!"binders: {xs.size}; application arguments: {body.getAppArgs.size}"
    let head ← ppExpr body.getAppFn
    logInfo m!"head: {(toString head).take 500}"
    let mut appPrefix := body.getAppFn
    for i in [:body.getAppArgs.size] do
      let arg := body.getAppArgs[i]!
      let startArg ← IO.monoMsNow
      let argResult := Kernel.check env lctx arg
      let endArg ← IO.monoMsNow
      let startFn ← IO.monoMsNow
      let fnResult := Kernel.check env lctx appPrefix
      let endFn ← IO.monoMsNow
      match argResult, fnResult with
      | .ok actual, .ok fnType =>
        match Kernel.whnf env lctx fnType with
        | .ok (.forallE _ expected _ _) =>
          let startEq ← IO.monoMsNow
          let conv := Kernel.isDefEq env lctx actual expected
          let endEq ← IO.monoMsNow
          let status := match conv with
            | .ok true => "equal"
            | .ok false => "unequal"
            | .error _ => "error"
          logInfo m!"arg {i}: own check {endArg - startArg} ms; prefix check {endFn - startFn} ms; domain conversion {endEq - startEq} ms ({status})"
          let left ← ppExpr actual
          let right ← ppExpr expected
          logInfo m!"actual type {i}: {(toString left).take 500}"
          logInfo m!"expected domain {i}: {(toString right).take 500}"
        | _ => logInfo m!"arg {i}: function type is not a pi type"
      | _, _ => logInfo m!"arg {i}: argument or prefix failed Kernel.check"
      appPrefix := mkApp appPrefix arg
      let startFull ← IO.monoMsNow
      let result := Kernel.check env lctx appPrefix
      let endFull ← IO.monoMsNow
      let status := match result with
        | .ok _ => "ok"
        | .error _ => "error"
      logInfo m!"application prefix through arg {i}: {endFull - startFull} ms ({status})"
