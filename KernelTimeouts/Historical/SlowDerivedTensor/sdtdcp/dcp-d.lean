import WeilConjectures.SixFunctors.Etale.Derived.Tensor

open Lean Elab Command Meta
open CategoryTheory Limits MonoidalCategory

namespace AlgebraicGeometry
open Scheme
universe u' u

set_option debug.skipKernelTC true in
lemma dcp_k_provider_probe
    (A : Type u') [Category.{u + 1, u'} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1, u + 1, u'} A] [MonoidalCategory A]
    [MonoidalPreadditive A] [SymmetricCategory A] (X : Scheme.{u})
    [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    (K L : DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    @tensorObj (DerivedCategory (Sheaf X.smallEtaleTopology A)) _ inferInstance K L =
    @tensorObj (DerivedMonoidal DerivedCategory.Qh
      (HomotopyCategory.quasiIso (Sheaf X.smallEtaleTopology A) (ComplexShape.up ℤ)))
      _ inferInstance K L := by rfl

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

private def compare (env : Environment) (label : String) (a b : Expr) : MetaM Unit := do
  let t0 ← IO.monoMsNow
  let r := Kernel.isDefEq env (← getLCtx) a b
  let t1 ← IO.monoMsNow
  let result := match r with | .ok x => s!"{x}" | .error _ => "error"
  logInfo m!"[DCP-D] {label} result={result} ms={t1-t0} equal={a == b} hash={a.hash}/{b.hash} size={a.sizeWithoutSharing}/{b.sizeWithoutSharing}"

set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let some info := env.find? ``dcp_k_provider_probe | throwError "missing probe"
  let inferred ← match Kernel.check env default (info.value! true) with
    | .ok ty => pure ty
    | .error _ => throwError "check failed"
  let rec descend (a b : Expr) (n : Nat) (xs : Array Expr) : MetaM Unit := do
    match n with
    | 0 =>
      let lp := (a.getAppArgs[2]!).getAppArgs[2]!
      let rp := (b.getAppArgs[2]!).getAppArgs[2]!
      let lwh ← whnf lp
      let rwh ← whnf rp
      let some direct := findApp? lwh `instIsRightCancelAddOfAddRightReflectLE 4
        | throwError "direct proof missing"
      let some shortcut := findApp? rwh `instMonoidalCategoryHomotopyCategoryIntUp_weilConjectures 8
        | throwError "shortcut missing"
      let expanded ← unfoldDefinition shortcut
      let expandedChanged := expanded.replace fun e =>
        if e.isConstOf `instMonoidalCategoryHomotopyCategoryIntUp_weilConjectures._proof_2 then
          some direct
        else none
      let fixedLeft := a.replace fun e => if e == lp then some rp else none
      let d1 := b.replace fun e => if e == shortcut then some expanded else none
      let d2 := b.replace fun e => if e == shortcut then some expandedChanged else none
      logInfo m!"[DCP-D] shortcutHash={shortcut.hash} expandedHash={expanded.hash} proofChanged={expandedChanged != expanded}"
      for (label, e) in [("fixed-left", fixedLeft), ("D1-expanded", d1), ("D2-proof", d2)] do
        checkWithKernel e
        logInfo m!"[DCP-D] {label} localKernelCheck=true hash={e.hash} size={e.sizeWithoutSharing}"
      let fixedClosed ← mkForallFVars xs fixedLeft
      let d1Closed ← mkForallFVars xs d1
      let d2Closed ← mkForallFVars xs d2
      compare env "D0-fixed-D-original-full-root" fixedClosed info.type
      compare env "D1-fixed-D-expanded-full-root" fixedClosed d1Closed
      compare env "D2-fixed-D-proof-full-root" fixedClosed d2Closed
      compare env "D1-versus-D2-full-root" d1Closed d2Closed
    | n+1 =>
      match a, b with
      | .forallE name ty body _, .forallE _ _ body' _ =>
        withLocalDeclD name ty fun x => descend (body.instantiate1 x) (body'.instantiate1 x) n (xs.push x)
      | _, _ => throwError "binder mismatch"
  liftTermElabM <| descend inferred info.type 12 #[]

end AlgebraicGeometry
