module

import WeilConjectures.SixFunctors.ProEtale.Adic.IntegersSheafHomologyTower

open CategoryTheory Lean Lean.Meta

universe u v w

variable {C : Type u} {D : Type v} {E : Type w}
  [Category C] [Category D] [Category E]

private def endpoint (F : C ⥤ D) (G : D ⥤ E) (H : E ⥤ C) : C ⥤ C :=
  (F ⋙ G) ⋙ H

private def head (e : Expr) : String :=
  match e.getAppFn with
  | .const n _ => s!"{n}"
  | .proj n i _ => s!"{n}.{i}"
  | _ => "other"

run_meta do
  let env ← getEnv
  let a ← getConstInfo ``endpoint
  lambdaTelescope a.value! fun _ lhs => do
    let lctx ← getLCtx
    let rhs ← mkAppM ``id #[lhs]
    logInfo m!"diagnostic M PR1624: heads={head lhs}/{head rhs}; structural={lhs == rhs}"
    let .ok _ := Kernel.check env lctx lhs
      | throwError "endpoint lhs did not Kernel-check"
    let .ok _ := Kernel.check env lctx rhs
      | throwError "endpoint rhs did not Kernel-check"
    let start ← IO.monoMsNow
    let result := Kernel.isDefEq env lctx lhs rhs
    let stop ← IO.monoMsNow
    logInfo m!"diagnostic M PR1624: {stop - start} ms, result={match result with | .ok true => "equal" | .ok false => "unequal" | .error _ => "error"}"
