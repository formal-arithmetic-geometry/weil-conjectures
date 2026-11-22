module

import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.Trace.DiagonalTraceFiniteEtaleIntegralKummer

open Lean Lean.Meta

private def recursorEndpoint (p : Exists (fun n : Nat => n = n)) : True :=
  Exists.casesOn p (fun _ _ => True.intro)

private def head (e : Expr) : String :=
  match e.getAppFn with
  | .const n _ => s!"{n}"
  | .proj n i _ => s!"{n}.{i}"
  | _ => "other"

run_meta do
  let env ← getEnv
  let a ← getConstInfo ``recursorEndpoint
  lambdaTelescope a.value! fun _ lhs => do
    let lctx ← getLCtx
    let rhs ← mkAppM ``id #[lhs]
    logInfo m!"diagnostic M PR2122: heads={head lhs}/{head rhs}; structural={lhs == rhs}"
    let .ok _ := Kernel.check env lctx lhs
      | throwError "recursor lhs did not Kernel-check"
    let .ok _ := Kernel.check env lctx rhs
      | throwError "recursor rhs did not Kernel-check"
    let start ← IO.monoMsNow
    let result := Kernel.isDefEq env lctx lhs rhs
    let stop ← IO.monoMsNow
    logInfo m!"diagnostic M PR2122: {stop - start} ms, result={match result with | .ok true => "equal" | .ok false => "unequal" | .error _ => "error"}"
