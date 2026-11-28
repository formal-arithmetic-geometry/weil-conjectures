import WeilConjectures.SixFunctors.Etale.Derived.Tensor

open Lean Elab Command Meta
open CategoryTheory Limits MonoidalCategory
set_option linter.style.emptyLine false
set_option linter.style.longLine false

namespace AlgebraicGeometry
open Scheme
universe u' u

set_option debug.skipKernelTC true in
lemma icd_tensorObj_probe_app
    (A : Type u') [Category.{u + 1, u'} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1, u + 1, u'} A] [MonoidalCategory A]
    [MonoidalPreadditive A] [SymmetricCategory A] (X : Scheme.{u})
    [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    (K L : DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    @tensorObj (DerivedCategory (Sheaf X.smallEtaleTopology A)) _ inferInstance K L =
    @tensorObj (DerivedMonoidal DerivedCategory.Qh
      (HomotopyCategory.quasiIso (Sheaf X.smallEtaleTopology A) (ComplexShape.up ℤ)))
      _ inferInstance K L := by
  rfl

private def head (e : Expr) : String :=
  match e.getAppFn with
  | .const n ls => s!"{n}/{e.getAppNumArgs}/{ls}"
  | .proj n i _ => s!"proj:{n}.{i}/{e.getAppNumArgs}"
  | x => s!"{x.ctorName}/{e.getAppNumArgs}"

private def spine (side part : String) (e : Expr) : MetaM Unit := do
  logInfo m!"[NODE] {side}.{part} {head e} size={e.sizeWithoutSharing}"
  for i in [0:e.getAppNumArgs] do
    let a := e.getAppArgs[i]!
    let index : Nat := if part == "carrier" then 0 else if part == "lhs" then 1 else 2
    logInfo m!"[ARG] {side}.{part}.{i} {head a} size={a.sizeWithoutSharing} rawPath=root/body^12/arg{index}/fn^{e.getAppNumArgs - 1 - i}/arg"
    if part != "carrier" then
      IO.FS.writeFile s!"../results/probe-{side}-{part}-arg{i}.raw" (repr a).pretty
    if part != "carrier" && i == 2 then
      for j in [0:a.getAppNumArgs] do
        let x := a.getAppArgs[j]!
        logInfo m!"[PROVIDER-ARG] {side}.{part}.{j} {head x} size={x.sizeWithoutSharing}"

private def inspect (side : String) (e : Expr) : MetaM Unit := do
  let mut body := e
  for _ in [0:12] do
    match body with
    | .forallE _ _ b _ => body := b
    | _ => throwError "expected twelve binders"
  logInfo m!"[BODY] {side} {head body} size={body.sizeWithoutSharing}"
  IO.FS.writeFile s!"../results/probe-{side}-body.raw" (repr body).pretty
  if body.getAppFn.isConstOf ``Eq && body.getAppNumArgs == 3 then
    spine side "carrier" body.getAppArgs[0]!
    spine side "lhs" body.getAppArgs[1]!
    spine side "rhs" body.getAppArgs[2]!

set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let some info := env.find? ``icd_tensorObj_probe_app | throwError "missing"
  let value := info.value! true
  liftTermElabM do
    inspect "stored" info.type
    inspect "meta" (← inferType value)
    match Kernel.check env default value with
    | .ok ty => inspect "kernel" ty
    | .error _ => logInfo m!"[KERNEL] check failed"
    let checked ← match Kernel.check env default value with
      | .ok ty => pure ty
      | .error _ => throwError "Kernel.check failed"
    let rec openBoth (a b : Expr) (n : Nat) : MetaM Unit := do
      if n == 0 then
        logInfo m!"[CTX] checked={head a} stored={head b} checkedArgs={a.getAppNumArgs} storedArgs={b.getAppNumArgs}"
        for (side, e) in #[("checked", a), ("stored", b)] do
          for i in [0:e.getAppNumArgs] do
            let x := e.getAppArgs[i]!
            logInfo m!"[CTX-ARG] {side}.{i} {head x}"
      else
        match a, b with
        | .forallE name dom body _, .forallE _ dom' body' _ =>
          let same := dom == dom'
          let eq := Kernel.isDefEq env (← getLCtx) dom dom'
          let answer := match eq with | .ok v => s!"{v}" | .error _ => "error"
          logInfo m!"[CTX-BINDER] {12-n} {name} structural={same} defeq={answer}"
          withLocalDeclD name dom fun x => openBoth (body.instantiate1 x) (body'.instantiate1 x) (n-1)
        | _, _ => throwError "mismatched binder shape"
    openBoth checked info.type 12

end AlgebraicGeometry
