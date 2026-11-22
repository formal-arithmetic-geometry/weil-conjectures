module

import WeilConjectures.WeilSheaf.BaseChangeField.Transport

open Lean Lean.Meta

structure GeneratedField (α : Type) where
  value : α
  witness : value = value

private def generatedField (x : Nat) : GeneratedField Nat :=
  { value := x, witness := rfl }

private def head (e : Expr) : String :=
  match e.getAppFn with
  | .const n _ => s!"{n}"
  | .proj n i _ => s!"{n}.{i}"
  | _ => "other"

run_meta do
  let env ← getEnv
  let info ← getConstInfo ``generatedField
  lambdaTelescope info.value! fun _ lhs => do
    let lctx ← getLCtx
    let rhs ← mkAppM ``id #[lhs]
    logInfo m!"diagnostic M PR1627: heads={head lhs}/{head rhs}; structural={lhs == rhs}"
    let .ok _ := Kernel.check env lctx lhs
      | throwError "generated field lhs did not Kernel-check"
    let .ok _ := Kernel.check env lctx rhs
      | throwError "generated field rhs did not Kernel-check"
    let start ← IO.monoMsNow
    let result := Kernel.isDefEq env lctx lhs rhs
    let stop ← IO.monoMsNow
    logInfo m!"diagnostic M PR1627: {stop - start} ms, result={match result with | .ok true => "equal" | .ok false => "unequal" | .error _ => "error"}"
