module

import all WeilConjectures.WeilSheaf.Native.NativePullTensor

open Lean

run_meta do
  let env ← getEnv
  let info ← getConstInfo `AlgebraicGeometry.ProEtaleWeilSheaf.nativePullTotalTensor
  let value := info.value! (allowOpaque := true)
  let typeObjects ← info.type.numObjs
  let valueObjects ← value.numObjs
  logInfo m!"expression objects: declared type {typeObjects}, stored value {valueObjects}"
  let .ok inferred := Kernel.check env {} value |
    throwError "Value replay failed"
  let probes := #[("inferred / inferred", inferred, inferred),
    ("declared / declared", info.type, info.type),
    ("inferred / declared", inferred, info.type)]
  for (label, left, right) in probes do
    let start ← IO.monoMsNow
    let result := Kernel.isDefEq env {} left right
    let stop ← IO.monoMsNow
    let status := match result with
      | .ok true => "equal"
      | .ok false => "unequal"
      | .error _ => "error"
    logInfo m!"{label}: {stop - start} ms ({status})"
