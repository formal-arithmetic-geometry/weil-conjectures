
open Lean Lean.Meta

set_option maxHeartbeats 10000000

private def proofHead (e : Expr) : String :=
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

private def auditProofPrefix (env : Environment) (name : Name) : MetaM Unit := do
  let info ← getConstInfo name
  let value := info.value! (allowOpaque := true)
  lambdaTelescope value fun xs body => do
    let lctx ← getLCtx
    let args := body.getAppArgs
    logInfo m!"{name}: binders={xs.size}, body head={proofHead body}, args={args.size}"
    let mut appSoFar := body.getAppFn
    for i in [:args.size] do
      let arg := args[i]!
      let startArg ← IO.monoMsNow
      let argResult := Kernel.check env lctx arg
      let stopArg ← IO.monoMsNow
      let startFn ← IO.monoMsNow
      let fnResult := Kernel.check env lctx appSoFar
      let stopFn ← IO.monoMsNow
      match argResult, fnResult with
      | .ok actual, .ok fnType =>
        match Kernel.whnf env lctx fnType with
        | .ok (.forallE _ expected _ _) =>
          let startEq ← IO.monoMsNow
          let result := Kernel.isDefEq env lctx actual expected
          let stopEq ← IO.monoMsNow
          logInfo m!"{name} arg {i}: term={proofHead arg}, actual type={proofHead actual}, expected={proofHead expected}, structural={actual == expected}; own={stopArg - startArg} ms, prefix={stopFn - startFn} ms, domain={stopEq - startEq} ms, result={match result with | .ok true => "equal" | .ok false => "unequal" | .error _ => "error"}"
        | _ => logInfo m!"{name} arg {i}: function type not Pi"
      | _, _ => logInfo m!"{name} arg {i}: argument or prefix failed"
      appSoFar := mkApp appSoFar arg

run_meta do
  let env ← getEnv
  for n in [1, 2] do
    auditProofPrefix env (Name.str `AlgebraicGeometry.ProEtaleWeilSheaf.powFunctor s!"_proof_{n}")
