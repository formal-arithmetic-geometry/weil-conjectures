
open Lean Lean.Meta

set_option maxHeartbeats 10000000

private def lhsHead (e : Expr) : String :=
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
    let actualArgs := actual.getAppArgs
    let expectedArgs := expected.getAppArgs
    let left := actualArgs[1]!
    let right := expectedArgs[1]!
    logInfo m!"PR1625 lhs: {lhsHead left}/{lhsHead right}; args={left.getAppArgs.size}/{right.getAppArgs.size}"
    match (← getConstInfo `CategoryTheory.CategoryStruct.comp) with
    | .defnInfo d =>
      logInfo m!"CategoryStruct.comp hint={match d.hints with | .regular h => s!"regular {h}" | .abbrev => "abbrev" | .opaque => "opaque"}"
    | _ => logInfo m!"CategoryStruct.comp is not a definition"
    let la := left.getAppArgs
    let ra := right.getAppArgs
    for i in [:min la.size ra.size] do
      let a := la[i]!
      let b := ra[i]!
      let start ← IO.monoMsNow
      let result := Kernel.isDefEq env lctx a b
      let stop ← IO.monoMsNow
      logInfo m!"lhs arg {i}: {lhsHead a}/{lhsHead b}, structural={a == b}, defeq={stop - start} ms, result={match result with | .ok true => "equal" | .ok false => "unequal" | .error _ => "error"}"
