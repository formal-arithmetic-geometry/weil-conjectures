module

import all WeilConjectures.WeilSheaf.Native.NativePullTensor

open Lean Lean.Meta

set_option maxRecDepth 100000
set_option pp.explicit true

run_meta do
  let env ← getEnv
  let names := #[
    `AlgebraicGeometry.ProEtaleWeilSheaf.exists_nativePullTotalTensor,
    `AlgebraicGeometry.ProEtaleWeilSheaf.nativePullTotalTensor,
    `AlgebraicGeometry.ProEtaleWeilSheaf.nativePullTotalTensor_summands,
    `AlgebraicGeometry.ProEtaleWeilSheaf.nativeRestrictionDerivedTensor]
  for name in names do
    let info ← getConstInfo name
    let some value := info.value? (allowOpaque := true) | throwError "No value for {name}"
    let startType ← IO.monoMsNow
    let typeResult := Kernel.check env {} info.type
    let endType ← IO.monoMsNow
    let startValue ← IO.monoMsNow
    let valueResult := Kernel.check env {} value
    let endValue ← IO.monoMsNow
    logInfo m!"{name}: type check {endType - startType} ms; value check {endValue - startValue} ms"
    match typeResult, valueResult with
    | .ok _, .ok inferred =>
      let startEq ← IO.monoMsNow
      let equal := Kernel.isDefEq env {} inferred info.type
      let endEq ← IO.monoMsNow
      let status := match equal with
        | .ok true => "equal"
        | .ok false => "unequal"
        | .error _ => "error"
      logInfo m!"{name}: final conversion {endEq - startEq} ms; structurally equal {inferred == info.type}; result {status}"
      let actual ← ppExpr inferred
      let expected ← ppExpr info.type
      logInfo m!"{name}: inferred prefix {(toString actual).take 1000}"
      logInfo m!"{name}: declared prefix {(toString expected).take 1000}"
    | .error _, _ => logInfo m!"{name}: declared type check failed"
    | _, .error _ => logInfo m!"{name}: value check failed"
