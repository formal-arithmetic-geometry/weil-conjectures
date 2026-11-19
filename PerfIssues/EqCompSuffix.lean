
open Lean Lean.Meta

set_option maxHeartbeats 10000000

private def compHead (e : Expr) : String :=
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

private partial def peelCompLambdas (e : Expr) : Expr :=
  match e with
  | .lam _ _ b _ => peelCompLambdas b
  | _ => e

run_meta do
  let env ← getEnv
  match (← getConstInfo `CategoryTheory.CategoryStruct.comp) with
  | .defnInfo d =>
    logInfo m!"CategoryStruct.comp hint={match d.hints with | .regular h => s!"regular {h}" | .abbrev => "abbrev" | .opaque => "opaque"}, one-step post-lambda body={compHead (peelCompLambdas d.value)}"
  | _ => logInfo m!"CategoryStruct.comp is not a definition"
  let info ← getConstInfo `AlgebraicGeometry.Etale.rawModuleScalar_pullback_module_formula
  let value := info.value! (allowOpaque := true)
  lambdaTelescope value fun _ body => do
    let lctx ← getLCtx
    let args := body.getAppArgs
    let arg := args[3]!
    let appSoFar := mkAppN body.getAppFn (args.extract 0 3)
    let .ok actualEq := Kernel.check env lctx arg
      | throwError "Eq.refl did not Kernel-check"
    let .ok fnType := Kernel.check env lctx appSoFar
      | throwError "Eq.mpr prefix did not Kernel-check"
    let .ok (.forallE _ expectedEq _ _) := Kernel.whnf env lctx fnType
      | throwError "Eq.mpr final binder missing"
    let actualEqArgs := actualEq.getAppArgs
    let expectedEqArgs := expectedEq.getAppArgs
    let left := actualEqArgs[2]!
    let right := expectedEqArgs[2]!
    let la := left.getAppArgs
    let ra := right.getAppArgs
    logInfo m!"Eq right side: {compHead left}/{compHead right}; args={la.size}/{ra.size}"
    for i in [:min la.size ra.size] do
      let a := la[i]!
      let b := ra[i]!
      let start ← IO.monoMsNow
      let result := Kernel.isDefEq env lctx a b
      let stop ← IO.monoMsNow
      logInfo m!"comp arg {i}: {compHead a}/{compHead b}, structural={a == b}, defeq={stop - start} ms, result={match result with | .ok true => "equal" | .ok false => "unequal" | .error _ => "error"}"
