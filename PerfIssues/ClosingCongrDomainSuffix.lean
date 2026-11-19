
open Lean Lean.Meta

set_option maxHeartbeats 10000000

private partial def closingLets (e : Expr) : Expr :=
  match e with
  | .letE _ _ value body _ => closingLets (body.instantiate1 value)
  | _ => e

private def headName (e : Expr) : String :=
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
  let info ← getConstInfo
    `AlgebraicGeometry.ProEtale.not_preservesColimitsOfShape_rightDerivedLowerStar_of_isAbelianVariety
  lambdaTelescope (info.value! (allowOpaque := true)) fun _ raw => do
    let body := closingLets raw
    lambdaTelescope body.getAppArgs[4]! fun _ branch => do
      lambdaTelescope branch.getAppArgs[17]! fun _ inner => do
        lambdaTelescope inner.getAppArgs[4]! fun _ intro => do
          lambdaTelescope intro.getAppArgs[3]! fun _ proofBody => do
            let lctx ← getLCtx
            let congrTerm := proofBody.getAppArgs[0]!.getAppArgs[1]!.getAppArgs[2]!
            let args := congrTerm.getAppArgs
            let proof := args[7]!
            let appPrefix := mkAppN congrTerm.getAppFn (args.extract 0 7)
            let .ok actual := Kernel.check env lctx proof
              | throwError "zero_comp proof did not Kernel-check"
            let .ok fnType := Kernel.check env lctx appPrefix
              | throwError "congr prefix did not Kernel-check"
            let .ok (.forallE _ expected _ _) := Kernel.whnf env lctx fnType
              | throwError "congr final binder missing"
            let la := actual.getAppArgs
            let ra := expected.getAppArgs
            logInfo m!"congr final domain: {headName actual}/{headName expected}; args={la.size}/{ra.size}; same head={actual.getAppFn == expected.getAppFn}"
            for i in [:min la.size ra.size] do
              let a := la[i]!
              let b := ra[i]!
              let start ← IO.monoMsNow
              let result := Kernel.isDefEq env lctx a b
              let stop ← IO.monoMsNow
              logInfo m!"Eq arg {i}: {headName a}/{headName b}, structural={a == b}, defeq={stop - start} ms, result={match result with | .ok true => "equal" | .ok false => "unequal" | .error _ => "error"}"
