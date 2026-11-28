import WeilConjectures.SixFunctors.Etale.Derived.Tensor

open Lean Elab Command Meta

private def head (e : Expr) : String :=
  match e.getAppFn with
  | .const n ls => s!"{n}/{e.getAppNumArgs}/{ls}"
  | x => s!"{x.ctorName}/{e.getAppNumArgs}"

set_option maxHeartbeats 0 in
set_option trace.Meta.isDefEq.delta true in
run_cmd do
  let env ← getEnv
  let some info := env.find? `AlgebraicGeometry.Etale.isLeftDerivedFunctor₂_derivedTensor
    | throwError "missing original instance"
  let inferred ← match Kernel.check env default (info.value! true) with
    | .ok ty => pure ty
    | .error _ => throwError "Kernel.check failed"
  let rec inspect (checked stored : Expr) (n : Nat) : MetaM Unit := do
    if n == 0 then
      logInfo m!"[E1] checked={head checked} stored={head stored} structural={checked == stored}"
      for (label, e) in #[("checked", checked), ("stored", stored)] do
        for i in [0:e.getAppNumArgs] do
          let a := e.getAppArgs[i]!
          logInfo m!"[E1-ARG] {label}.{i} {head a} size={a.sizeWithoutSharing}"
          if i == 10 || i == 14 then
            IO.FS.writeFile s!"../results/e1-{label}-arg{i}.raw" (repr a).pretty
      let result ← isDefEq checked stored
      logInfo m!"[E1-META] defeq={result}"
      let kernel := Kernel.isDefEq env (← getLCtx) checked stored
      let answer := match kernel with | .ok x => s!"{x}" | .error _ => "error"
      logInfo m!"[E1-KERNEL] defeq={answer}"
    else
      match checked, stored with
      | .forallE name dom a _, .forallE _ dom' b _ =>
        let same := dom == dom'
        logInfo m!"[E1-BINDER] {10-n} {name} structural={same}"
        withLocalDeclD name dom fun x => inspect (a.instantiate1 x) (b.instantiate1 x) (n-1)
      | _, _ => throwError "mismatched binder shape"
  liftTermElabM <| inspect inferred info.type 10
