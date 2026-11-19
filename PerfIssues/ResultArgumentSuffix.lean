
open Lean Lean.Meta

set_option maxHeartbeats 10000000

private def resultHead (e : Expr) : String :=
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
  let name := `AlgebraicGeometry.ProEtale.leftDerivedUpperStarTensorComparison_app_app_fac
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
    logInfo m!"PR1625-result: binders={xs.size}; actual={resultHead actual}; expected={resultHead expected}"
    let la := actual.getAppArgs
    let ra := expected.getAppArgs
    logInfo m!"result head identical={actual.getAppFn == expected.getAppFn}; args={la.size}/{ra.size}"
    for i in [:min la.size ra.size] do
      let a := la[i]!
      let b := ra[i]!
      let start ← IO.monoMsNow
      let result := Kernel.isDefEq env lctx a b
      let stop ← IO.monoMsNow
      logInfo m!"result arg {i}: actual={resultHead a}, expected={resultHead b}, structural={a == b}, defeq={stop - start} ms, result={match result with | .ok true => "equal" | .ok false => "unequal" | .error _ => "error"}"
