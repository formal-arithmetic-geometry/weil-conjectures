import WeilConjectures.SixFunctors.Etale.Derived.Tensor

open Lean Elab Command Meta
open CategoryTheory Limits MonoidalCategory
set_option linter.style.emptyLine false
set_option linter.style.longLine false

namespace AlgebraicGeometry
open Scheme
universe u' u

set_option debug.skipKernelTC true in
lemma ide2_hint_probe
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
    (findApp? t n arity).orElse fun _ =>
      (findApp? v n arity).orElse fun _ => findApp? b n arity
  | .proj _ _ x | .mdata _ x => findApp? x n arity
  | _ => none

private def clone (sourceName targetName : Name) (height : Nat) : CommandElabM Unit := do
  let some (.defnInfo d) := (← getEnv).find? sourceName
    | throwError m!"not definition {sourceName}"
  liftCoreM <| addDecl (.defnDecl { d with name := targetName, hints := .regular height.toUInt32 })
  let some (.defnInfo c) := (← getEnv).find? targetName
    | throwError m!"clone absent {targetName}"
  logInfo m!"[B-CLONE] {targetName} source={sourceName} height={height} bodyEqual={c.value == d.value} typeEqual={c.type == d.type}"

private def renameHead (e : Expr) (n : Name) : Expr :=
  match e.getAppFn with
  | .const _ ls => mkAppN (mkConst n ls) e.getAppArgs
  | _ => e

private def inspect (env : Environment) (a b : Expr) : MetaM Unit := do
  let pa := (a.getAppArgs[2]!).getAppArgs[2]!
  let pb := (b.getAppArgs[2]!).getAppArgs[2]!
  let some direct := findApp? (← whnf pa) `HomotopyCategory.MonoidalCategory.instMonoidalCategory 19
    | throwError "canonical missing"
  let some shortcut := findApp? (← whnf pb) `instMonoidalCategoryHomotopyCategoryIntUp_weilConjectures 8
    | throwError "shortcut missing"
  for (label, cn, sn) in #[("original", `HomotopyCategory.MonoidalCategory.instMonoidalCategory,
      `instMonoidalCategoryHomotopyCategoryIntUp_weilConjectures),
      ("equal24", `ide2Canonical24, `ide2Shortcut24),
      ("equal25", `ide2Canonical25, `ide2Shortcut25),
      ("swapped", `ide2Canonical25, `ide2Shortcut24)] do
    let x := renameHead direct cn
    let y := renameHead shortcut sn
    checkWithKernel x
    checkWithKernel y
    let cx := Kernel.check env (← getLCtx) x
    let cy := Kernel.check env (← getLCtx) y
    logInfo m!"[B-CHECK] {label} checked={cx.isOk} stored={cy.isOk} structural={x == y}"
    if !cx.isOk || !cy.isOk then throwError m!"invalid provider {label}"
    let result := Kernel.isDefEq env (← getLCtx) x y
    let answer := match result with | .ok value => s!"{value}" | .error _ => "error"
    logInfo m!"[B-CMP] {label} result={answer} leftHead={cn} rightHead={sn}"
    let wx ← whnf x
    let wy ← whnf y
    logInfo m!"[B-WHNF] {label} checkedHead={wx.getAppFn} storedHead={wy.getAppFn} structural={wx == wy}"

set_option maxHeartbeats 0 in
run_cmd do
  let canonical := `HomotopyCategory.MonoidalCategory.instMonoidalCategory
  let shortcut := `instMonoidalCategoryHomotopyCategoryIntUp_weilConjectures
  clone canonical `ide2Canonical24 24
  clone canonical `ide2Canonical25 25
  clone shortcut `ide2Shortcut24 24
  clone shortcut `ide2Shortcut25 25
  let env ← getEnv
  let some info := env.find? ``ide2_hint_probe | throwError "missing probe"
  let checked ← match Kernel.check env default (info.value! true) with
    | .ok ty => pure ty
    | .error _ => throwError "kernel check failed"
  let rec descend (a b : Expr) (n : Nat) : MetaM Unit := do
    match n with
    | 0 => inspect env a b
    | n+1 =>
      match a, b with
      | .forallE name ty body _, .forallE _ _ body' _ =>
        withLocalDeclD name ty fun x => descend (body.instantiate1 x) (body'.instantiate1 x) n
      | _, _ => throwError "bad binder path"
  liftTermElabM <| descend checked info.type 12

end AlgebraicGeometry
