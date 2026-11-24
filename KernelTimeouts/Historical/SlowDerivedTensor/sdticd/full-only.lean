import WeilConjectures.SixFunctors.Etale.Derived.Tensor

open Lean Elab Command Meta

set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let some info := env.find? ``AlgebraicGeometry.Etale.isLeftDerivedFunctor₂_derivedTensor
    | throwError "missing consumer"
  let inferred ← match Kernel.check env default (info.value! true) with
    | .ok ty => pure ty
    | .error _ => throwError "Kernel.check failed"
  logInfo m!"[FULL] inferred_hash={inferred.hash} declared_hash={info.type.hash} inferred_size={inferred.sizeWithoutSharing} declared_size={info.type.sizeWithoutSharing}"
  let start ← IO.monoMsNow
  let result := Kernel.isDefEq env default inferred info.type
  let finish ← IO.monoMsNow
  let resultText := match result with
    | .ok b => s!"{b}"
    | .error _ => "error"
  logInfo m!"[FULL] result={resultText} ms={finish - start}"
