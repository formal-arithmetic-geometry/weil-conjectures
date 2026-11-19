
open Lean Lean.Meta

set_option maxHeartbeats 10000000

private partial def instantiateClosingLets (e : Expr) : Expr :=
  match e with
  | .letE _ _ value body _ => instantiateClosingLets (body.instantiate1 value)
  | _ => e

private def closingHead (e : Expr) : String :=
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
  lambdaTelescope (info.value! (allowOpaque := true)) fun _ rawBody => do
    let body := instantiateClosingLets rawBody
    lambdaTelescope body.getAppArgs[4]! fun _ branchBody => do
      let inner := branchBody.getAppArgs[17]!
      lambdaTelescope inner fun _ innerBody => do
        lambdaTelescope innerBody.getAppArgs[4]! fun _ intro => do
          let lctx ← getLCtx
          let args := intro.getAppArgs
          logInfo m!"closing intro head={closingHead intro}, args={args.size}"
          for i in [:args.size] do
            let arg := args[i]!
            let appPrefix := mkAppN intro.getAppFn (args.extract 0 i)
            let startCheck ← IO.monoMsNow
            let checked := Kernel.check env lctx arg
            let stopCheck ← IO.monoMsNow
            let .ok actual := checked
              | throwError "closing argument {i} did not Kernel-check"
            let .ok fnType := Kernel.check env lctx appPrefix
              | throwError "closing prefix {i} did not Kernel-check"
            let .ok (.forallE _ expected _ _) := Kernel.whnf env lctx fnType
              | throwError "closing prefix {i} has no binder"
            let startEq ← IO.monoMsNow
            let result := Kernel.isDefEq env lctx actual expected
            let stopEq ← IO.monoMsNow
            logInfo m!"intro arg {i}: value={closingHead arg}, actual={closingHead actual}, expected={closingHead expected}, check={stopCheck - startCheck} ms, domain={stopEq - startEq} ms, result={match result with | .ok true => "equal" | .ok false => "unequal" | .error _ => "error"}"
