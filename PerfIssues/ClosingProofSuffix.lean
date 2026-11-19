
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
          let proof := intro.getAppArgs[3]!
          lambdaTelescope proof fun xs rawProofBody => do
            let lctx ← getLCtx
            let proofBody := closingLets rawProofBody
            let args := proofBody.getAppArgs
            logInfo m!"closing proof binders={xs.size}, body={headName proofBody}, args={args.size}"
            for i in [:args.size] do
              let arg := args[i]!
              let appPrefix := mkAppN proofBody.getAppFn (args.extract 0 i)
              let startCheck ← IO.monoMsNow
              let checked := Kernel.check env lctx arg
              let stopCheck ← IO.monoMsNow
              let .ok actual := checked
                | throwError "closing proof argument {i} did not Kernel-check"
              let .ok fnType := Kernel.check env lctx appPrefix
                | throwError "closing proof prefix {i} did not Kernel-check"
              let .ok (.forallE _ expected _ _) := Kernel.whnf env lctx fnType
                | throwError "closing proof prefix {i} has no binder"
              let startEq ← IO.monoMsNow
              let result := Kernel.isDefEq env lctx actual expected
              let stopEq ← IO.monoMsNow
              logInfo m!"proof arg {i}: value={headName arg}, actual={headName actual}, expected={headName expected}, check={stopCheck - startCheck} ms, domain={stopEq - startEq} ms, result={match result with | .ok true => "equal" | .ok false => "unequal" | .error _ => "error"}"
