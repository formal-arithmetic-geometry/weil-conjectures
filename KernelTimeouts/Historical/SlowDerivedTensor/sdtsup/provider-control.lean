import WeilConjectures.SixFunctors.Etale.Derived.Tensor

open Lean Elab Command Meta
open CategoryTheory Limits MonoidalCategory

namespace AlgebraicGeometry
open Scheme
universe u' u

set_option debug.skipKernelTC true in
lemma sup_provider_probe
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
  | .lam .. => "lam"
  | _ => s!"{e.getAppFn.ctorName}/{e.getAppNumArgs}"

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

private def timed (env : Environment) (label : String) (a b : Expr) : MetaM Unit := do
  let t0 ← IO.monoMsNow
  let r := Kernel.isDefEq env (← getLCtx) a b
  let t1 ← IO.monoMsNow
  let result := match r with | .ok x => s!"{x}" | .error _ => "error"
  logInfo m!"[SUP] {label} result={result} ms={t1-t0} equal={a == b} hash={a.hash}/{b.hash} size={a.sizeWithoutSharing}/{b.sizeWithoutSharing}"

set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let some info := env.find? ``sup_provider_probe | throwError "missing probe"
  let inferred ← match Kernel.check env default (info.value! true) with
    | .ok ty => pure ty
    | .error _ => throwError "check failed"
  let rec descend (a b : Expr) (n : Nat) : MetaM Unit := do
    match n with
    | 0 =>
      let lp := (a.getAppArgs[2]!).getAppArgs[2]!
      let rp := (b.getAppArgs[2]!).getAppArgs[2]!
      let la ← whnf lp
      let rb ← whnf rp
      let lf := la.getAppArgs[4]!
      let rf := rb.getAppArgs[4]!
      logInfo m!"[SUP] original-whiskerRight {head lf} {head rf}"
      let some direct := findApp? la `instIsRightCancelAddOfAddRightReflectLE 4
        | throwError "direct provider absent"
      logInfo m!"[SUP] direct-provider {head direct} hash={direct.hash} type={← inferType direct}"
      let some shortcut := findApp? rb `instMonoidalCategoryHomotopyCategoryIntUp_weilConjectures 8
        | throwError "shortcut application absent"
      let expanded ← unfoldDefinition shortcut
      let expandedChanged := expanded.replace fun e =>
        if e.isConstOf `instMonoidalCategoryHomotopyCategoryIntUp_weilConjectures._proof_2 then
          some direct
        else none
      logInfo m!"[SUP] shortcut={head shortcut} expanded-change={expandedChanged != expanded}"
      let changed := rb.replace fun e => if e == shortcut then some expandedChanged else none
      let expandedOnly := rb.replace fun e => if e == shortcut then some expanded else none
      logInfo m!"[SUP] provider-change={changed != rb}"
      checkWithKernel changed
      checkWithKernel expandedOnly
      logInfo m!"[SUP] rebuilt-structure-kernel-check=true type={← inferType changed}"
      let cf := changed.getAppArgs[4]!
      let ef := expandedOnly.getAppArgs[4]!
      timed env "P0-P1.whiskerRight" lf rf
      timed env "P0-expanded.whiskerRight" lf ef
      timed env "P0-P2.whiskerRight" lf cf
      timed env "P1-P2.whiskerRight" rf cf
      for i in [2, 3] do
        timed env s!"P0-P1.field{i}" (la.getAppArgs[i]!) (rb.getAppArgs[i]!)
        timed env s!"P0-P2.field{i}" (la.getAppArgs[i]!) (changed.getAppArgs[i]!)
      let expandedRoot := b.replace fun e => if e == shortcut then some expanded else none
      let changedRoot := b.replace fun e => if e == shortcut then some expandedChanged else none
      logInfo m!"[SUP] root-change={changedRoot != b}"
      checkWithKernel expandedRoot
      checkWithKernel changedRoot
      logInfo m!"[SUP] rebuilt-root-kernel-check=true"
      timed env "P0-P1.root" a b
      timed env "P0-expanded.root" a expandedRoot
      timed env "P0-P2.root" a changedRoot
    | n+1 =>
      match a, b with
      | .forallE name ty body _, .forallE _ _ body' _ =>
        withLocalDeclD name ty fun x => descend (body.instantiate1 x) (body'.instantiate1 x) n
      | _, _ => throwError "binder mismatch"
  liftTermElabM <| descend inferred info.type 12

end AlgebraicGeometry
