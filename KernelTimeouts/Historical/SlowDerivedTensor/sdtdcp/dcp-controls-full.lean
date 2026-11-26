import WeilConjectures.SixFunctors.Etale.Derived.Tensor

open Lean Elab Command Meta
open CategoryTheory Limits MonoidalCategory

namespace AlgebraicGeometry
open Scheme
universe u' u

set_option debug.skipKernelTC true in
lemma dcp_control_probe
    (A : Type u') [Category.{u + 1, u'} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1, u + 1, u'} A] [MonoidalCategory A]
    [MonoidalPreadditive A] [SymmetricCategory A] (X : Scheme.{u})
    [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    (K L : DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    @tensorObj (DerivedCategory (Sheaf X.smallEtaleTopology A)) _ inferInstance K L =
    @tensorObj (DerivedMonoidal DerivedCategory.Qh
      (HomotopyCategory.quasiIso (Sheaf X.smallEtaleTopology A) (ComplexShape.up ℤ)))
      _ inferInstance K L := by rfl

private def head (e : Expr) : String :=
  match e.getAppFn with
  | .const n _ => s!"{n}/{e.getAppNumArgs}"
  | .proj n i _ => s!"proj {n}.{i}/{e.getAppNumArgs}"
  | x => s!"{x.ctorName}/{e.getAppNumArgs}"

private partial def findApp? (e : Expr) (n : Name) (arity : Nat) : Option Expr :=
  if e.getAppFn.isConstOf n && e.getAppNumArgs == arity then some e else
  match e with
  | .app f x => (findApp? f n arity).orElse fun _ => findApp? x n arity
  | .lam _ d b _ | .forallE _ d b _ =>
    (findApp? d n arity).orElse fun _ => findApp? b n arity
  | .letE _ t v b _ =>
    (findApp? t n arity).orElse fun _ => (findApp? v n arity).orElse fun _ => findApp? b n arity
  | .proj _ _ x | .mdata _ x => findApp? x n arity
  | _ => none

private def check (label : String) (e : Expr) : MetaM Unit := do
  try
    checkWithKernel e
    logInfo m!"[DCP-CHECK] {label} valid=true type={head (← inferType e)} hash={e.hash} size={e.sizeWithoutSharing}"
  catch ex =>
    logInfo m!"[DCP-CHECK] {label} valid=false reason={ex.toMessageData}"

private def compare (env : Environment) (label : String) (a b : Expr) : MetaM Unit := do
  let t0 ← IO.monoMsNow
  let r := Kernel.isDefEq env (← getLCtx) a b
  let t1 ← IO.monoMsNow
  let result := match r with | .ok x => s!"{x}" | .error _ => "error"
  logInfo m!"[DCP-CMP] {label} result={result} ms={t1-t0} equal={a == b} hash={a.hash}/{b.hash} size={a.sizeWithoutSharing}/{b.sizeWithoutSharing}"

set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let some info := env.find? ``dcp_control_probe | throwError "missing probe"
  let inferred ← match Kernel.check env default (info.value! true) with
    | .ok ty => pure ty
    | .error _ => throwError "check failed"
  let rec descend (a b : Expr) (n : Nat) (xs : Array Expr) : MetaM Unit := do
    match n with
    | 0 =>
      let lp := (a.getAppArgs[2]!).getAppArgs[2]!
      let rp := (b.getAppArgs[2]!).getAppArgs[2]!
      logInfo m!"[DCP-PROVIDER] checked={head lp} stored={head rp} typeChecked={head (← inferType lp)} typeStored={head (← inferType rp)}"
      check "P-D" lp
      check "P-D-prime" rp
      compare env "P-D/P-D-prime" lp rp
      let lwh ← whnf lp
      let rwh ← whnf rp
      logInfo m!"[DCP-WHNF] checked={head lwh} stored={head rwh} hash={lwh.hash}/{rwh.hash} size={lwh.sizeWithoutSharing}/{rwh.sizeWithoutSharing}"
      compare env "provider-WHNF" lwh rwh
      for i in [2, 3, 4] do
        compare env s!"field-{i}" (lwh.getAppArgs[i]!) (rwh.getAppArgs[i]!)
      let storedToD := b.replace fun e => if e == rp then some lp else none
      let checkedToDPrime := a.replace fun e => if e == lp then some rp else none
      check "stored-route-to-P-D" storedToD
      check "checked-route-to-P-D-prime" checkedToDPrime
      compare env "original-root-body" a b
      compare env "D-aligned-forward-body" a storedToD
      compare env "D-aligned-reverse-body" checkedToDPrime b
      let some shortcut := findApp? rp `instMonoidalCategoryHomotopyCategoryIntUp_weilConjectures 8
        | throwError "shortcut missing"
      let some canonical := findApp? lwh `HomotopyCategory.MonoidalCategory.instMonoidalCategory 19
        | throwError "canonical missing"
      logInfo m!"[DCP-K] shortcut={head shortcut} canonical={head canonical} typeHash={(← inferType shortcut).hash}/{(← inferType canonical).hash}"
      let kAligned := b.replace fun e => if e == shortcut then some canonical else none
      check "K-aligned-original-routes" kAligned
      compare env "K-aligned-body" a kAligned
      let both := storedToD.replace fun e => if e == shortcut then some canonical else none
      check "D-and-K-aligned" both
      compare env "D-and-K-aligned-body" a both
      let forwardClosed ← mkForallFVars xs storedToD
      let reverseClosed ← mkForallFVars xs checkedToDPrime
      let kClosed ← mkForallFVars xs kAligned
      let bothClosed ← mkForallFVars xs both
      check "D-aligned-forward-closed" forwardClosed
      check "D-aligned-reverse-closed" reverseClosed
      check "K-aligned-closed" kClosed
      check "D-and-K-aligned-closed" bothClosed
      compare env "C10-D-aligned-forward-full-root" inferred forwardClosed
      compare env "C10-D-aligned-reverse-full-root" reverseClosed info.type
      compare env "C01-K-aligned-full-root" inferred kClosed
      compare env "C11-both-aligned-full-root" inferred bothClosed
    | n+1 =>
      match a, b with
      | .forallE name ty body _, .forallE _ _ body' _ =>
        withLocalDeclD name ty fun x => descend (body.instantiate1 x) (body'.instantiate1 x) n (xs.push x)
      | _, _ => throwError "binder mismatch"
  liftTermElabM <| descend inferred info.type 12 #[]

end AlgebraicGeometry
