module

import all WeilConjectures.WeilSheaf.Native.NativePullTensor

open Lean Lean.Meta

set_option pp.explicit true
set_option pp.universes true
set_option maxHeartbeats 10000000

private def shortHead (e : Expr) : String :=
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
  let name := `AlgebraicGeometry.ProEtaleWeilSheaf.nativePullTotalTensor
  let info ← getConstInfo name
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
    logInfo m!"NPT-result: {xs.size} original binders, actual={shortHead actual}, expected={shortHead expected}"
    let actualArgs := actual.getAppArgs
    let expectedArgs := expected.getAppArgs
    logInfo m!"head identical={actual.getAppFn == expected.getAppFn}; actual args={actualArgs.size}; expected args={expectedArgs.size}"
    for i in [:min actualArgs.size expectedArgs.size] do
      let left := actualArgs[i]!
      let right := expectedArgs[i]!
      logInfo m!"arg {i}: actual head={shortHead left}; expected head={shortHead right}; structurally equal={left == right}"
      let start ← IO.monoMsNow
      let result := Kernel.isDefEq env lctx left right
      let stop ← IO.monoMsNow
      logInfo m!"arg {i}: defeq {stop - start} ms, result={match result with | .ok true => "equal" | .ok false => "unequal" | .error _ => "error"}"
