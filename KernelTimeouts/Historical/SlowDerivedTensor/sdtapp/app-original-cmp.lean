import WeilConjectures.SixFunctors.Etale.Derived.Tensor

open Lean Elab Command Meta

private def head (e : Expr) : String :=
  match e.getAppFn with
  | .const n ls => s!"{n}/{e.getAppNumArgs}/{ls}"
  | x => s!"{x.ctorName}/{e.getAppNumArgs}"

set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let some info := env.find? `AlgebraicGeometry.Etale.isLeftDerivedFunctor₂_derivedTensor
    | throwError "missing original instance"
  let value := info.value! true
  let inferred ← match Kernel.check env default value with
    | .ok ty => pure ty
    | .error _ => throwError "Kernel.check failed"
  liftTermElabM do
    logInfo m!"[ORIG] value={head value} inferred={head inferred} stored={head info.type} structural={inferred == info.type}"
    let t0 ← IO.monoMsNow
    let result := Kernel.isDefEq env (← getLCtx) inferred info.type
    let t1 ← IO.monoMsNow
    let answer := match result with | .ok x => s!"{x}" | .error _ => "error"
    logInfo m!"[ORIG-CMP] result={answer} ms={t1-t0}"
