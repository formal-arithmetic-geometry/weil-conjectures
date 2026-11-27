import WeilConjectures.SixFunctors.Etale.Derived.Tensor

open Lean Elab Command Meta
open CategoryTheory Limits MonoidalCategory
set_option linter.style.emptyLine false
set_option linter.style.longLine false

namespace AlgebraicGeometry
open Scheme
universe u' u

set_option debug.skipKernelTC true in
lemma ide_r1b_probe
    (A : Type u') [Category.{u + 1, u'} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1, u + 1, u'} A] [MonoidalCategory A]
    [MonoidalPreadditive A] [SymmetricCategory A] (X : Scheme.{u})
    [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    (K L : DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    @tensorObj (DerivedCategory (Sheaf X.smallEtaleTopology A)) _ inferInstance K L =
    @tensorObj (DerivedMonoidal DerivedCategory.Qh
      (HomotopyCategory.quasiIso (Sheaf X.smallEtaleTopology A) (ComplexShape.up ℤ)))
      _ inferInstance K L := by rfl

private def h (e : Expr) : String :=
  match e.getAppFn with
  | .const n ls => s!"{n}/{e.getAppNumArgs}/{ls}"
  | .proj n i _ => s!"proj:{n}.{i}"
  | e => s!"{e.ctorName}/{e.getAppNumArgs}"

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
  let saved ← saveState
  try
    let r ← isDefEq a b
    logInfo m!"[IDE-R1-CMP] {label} structural={a == b} metaDefEq={r}"
  catch ex => logInfo m!"[IDE-R1-CMP] {label} failed={ex.toMessageData}"
  restoreState saved
  let kr := Kernel.isDefEq env (← getLCtx) a b
  let answer := match kr with | .ok v => s!"{v}" | .error _ => "error"
  logInfo m!"[IDE-R1-KERNEL] {label} defeq={answer}"

private def report (env : Environment) (a b : Expr) : MetaM Unit := do
  logInfo m!"[IDE-R1-APP] checked={h a} stored={h b} structural={a == b}"
  logInfo m!"[IDE-R1-DUMP] checked {repr a}"
  logInfo m!"[IDE-R1-DUMP] stored {repr b}"
  cmp env "application" a b
  let ta ← inferType a
  let tb ← inferType b
  logInfo m!"[IDE-R1-TYPE] checked={repr ta} stored={repr tb}"
  cmp env "result-type" ta tb
  for i in [0:8] do
    let aa := a.getAppArgs[i]!
    let bb := b.getAppArgs[i]!
    let ata ← inferType aa
    let bta ← inferType bb
    logInfo m!"[IDE-R1-ARG] i={i} checked={h aa} stored={h bb} checkedType={h ata} storedType={h bta} structural={aa == bb} checkedHash={aa.hash} storedHash={bb.hash}"
    logInfo m!"[IDE-R1-ARGDUMP] i={i} checked={repr aa} stored={repr bb} checkedType={repr ata} storedType={repr bta}"
    cmp env s!"arg{i}" aa bb
    cmp env s!"arg{i}-type" ata bta

private def inspect (env : Environment) (a b : Expr) : MetaM Unit := do
  let pa := (a.getAppArgs[2]!).getAppArgs[2]!
  let pb := (b.getAppArgs[2]!).getAppArgs[2]!
  let stored := findApp? pb `instMonoidalCategoryHomotopyCategoryIntUp_weilConjectures 8
  let some sb := stored | throwError "stored shortcut missing"
  let mut x := pa
  for step in [0:12] do
    let found := findApp? x `instMonoidalCategoryHomotopyCategoryIntUp_weilConjectures 8
    logInfo m!"[IDE-R1-SEARCH] step={step} head={h x} size={x.sizeWithoutSharing} found={found.isSome}"
    if let some ca := found then
      report env ca sb
      return
    if x.getAppFn.isConstOf `inferInstance then
      x := x.getAppArgs[1]!
    else if x.getAppFn.isConstOf `CategoryTheory.MonoidalCategory.toMonoidalCategoryStruct then
      x := x.getAppArgs[2]!
    else if x.getAppFn.isConstOf `CategoryTheory.MonoidalCategory.mk then
      x := x.getAppArgs[2]!
    else if x.getAppFn.isConstOf `CategoryTheory.MonoidalCategoryStruct.mk then
      logInfo m!"[IDE-R1-SEARCH] end at constructor; no checked shortcut application"
      return
    else
      try
        let y ← unfoldDefinition x
        if y == x then
          logInfo m!"[IDE-R1-SEARCH] blocked at {h x}"
          return
        x := y
      catch ex =>
        logInfo m!"[IDE-R1-SEARCH] unfold failed at {h x}: {ex.toMessageData}"
        return

set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let some info := env.find? ``ide_r1b_probe | throwError "missing probe"
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
