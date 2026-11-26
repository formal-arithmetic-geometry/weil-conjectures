import WeilConjectures.SixFunctors.Etale.Derived.Tensor

open Lean Elab Command Meta
open CategoryTheory Limits MonoidalCategory

namespace AlgebraicGeometry
open Scheme
universe u' u

set_option debug.skipKernelTC true in
lemma dcp_closed_probe
    (A : Type u') [Category.{u + 1, u'} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1, u + 1, u'} A] [MonoidalCategory A]
    [MonoidalPreadditive A] [SymmetricCategory A] (X : Scheme.{u})
    [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    (K L : DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    @tensorObj (DerivedCategory (Sheaf X.smallEtaleTopology A)) _ inferInstance K L =
    @tensorObj (DerivedMonoidal DerivedCategory.Qh
      (HomotopyCategory.quasiIso (Sheaf X.smallEtaleTopology A) (ComplexShape.up ℤ)))
      _ inferInstance K L := by rfl

private partial def body (e : Expr) (fuel : Nat) : Expr :=
  match fuel, e with
  | 0, _ => e
  | n+1, .forallE _ _ b _ => body b n
  | _, _ => e

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

private def cmp (env : Environment) (label : String) (a b : Expr) : MetaM Unit := do
  let t0 ← IO.monoMsNow
  let r := Kernel.isDefEq env (← getLCtx) a b
  let t1 ← IO.monoMsNow
  let result := match r with | .ok x => s!"{x}" | .error _ => "error"
  logInfo m!"[DCP-CLOSED] {label} result={result} ms={t1-t0} equal={a == b} size={a.sizeWithoutSharing}/{b.sizeWithoutSharing}"

set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let some info := env.find? ``dcp_closed_probe | throwError "missing probe"
  let inferred ← match Kernel.check env default (info.value! true) with
    | .ok ty => pure ty
    | .error _ => throwError "proof check failed"
  let a := body inferred 12
  let b := body info.type 12
  let lp := (a.getAppArgs[2]!).getAppArgs[2]!
  let rp := (b.getAppArgs[2]!).getAppArgs[2]!
  let storedToD := info.type.replace fun e => if e == rp then some lp else none
  let checkedToDPrime := inferred.replace fun e => if e == lp then some rp else none
  let some shortcut := findApp? info.type `instMonoidalCategoryHomotopyCategoryIntUp_weilConjectures 8
    | throwError "shortcut not found"
  let lwh ← liftTermElabM <| whnf lp
  let some canonical := findApp? lwh `HomotopyCategory.MonoidalCategory.instMonoidalCategory 19
    | throwError "canonical not found"
  let kAligned := info.type.replace fun e => if e == shortcut then some canonical else none
  let both := storedToD.replace fun e => if e == shortcut then some canonical else none
  logInfo m!"[DCP-CLOSED] changed D={storedToD != info.type} reverse={checkedToDPrime != inferred} K={kAligned != info.type} both={both != info.type}"
  for (label, e) in [("C10-forward", storedToD), ("C10-reverse", checkedToDPrime),
      ("C01", kAligned), ("C11", both)] do
    match Kernel.check env default e with
    | .ok _ => logInfo m!"[DCP-CLOSED] {label} kernelCheck=true"
    | .error _ => logInfo m!"[DCP-CLOSED] {label} kernelCheck=false"
  liftTermElabM do
    cmp env "C00" inferred info.type
    cmp env "C10-forward" inferred storedToD
    cmp env "C10-reverse" checkedToDPrime info.type
    cmp env "C01" inferred kAligned
    cmp env "C11" inferred both

end AlgebraicGeometry
