import WeilConjectures.SixFunctors.Etale.Derived.Tensor
import Lean

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let name := `AlgebraicGeometry.Etale.isLeftDerivedFunctor₂_derivedTensor
  let some info := env.find? name
    | throwError "declaration not found: {name}"
  let some value := info.value? (allowOpaque := true)
    | throwError "value not found: {name}"
  let type := info.type
  let t0 ← IO.monoMsNow
  let checkedType := Kernel.check env {} type
  let t1 ← IO.monoMsNow
  let checkedValue := Kernel.check env {} value
  let t2 ← IO.monoMsNow
  let .ok inferredType := checkedValue
    | throwError "value check failed"
  let converted := Kernel.isDefEq env {} inferredType type
  let t3 ← IO.monoMsNow
  logInfo m!"{name}: type={t1-t0}ms value={t2-t1}ms final={t3-t2}ms"
  let convertedOk : Bool := converted.toOption == some true
  logInfo m!"type result={checkedType.isOk}, conversion result={convertedOk}"
  logInfo m!"declared head={type.getAppFn}, inferred head={inferredType.getAppFn}"
