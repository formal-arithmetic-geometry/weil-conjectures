import WeilConjectures.SixFunctors.Etale.Derived.Tensor

open Lean Elab Command Meta
open CategoryTheory Limits MonoidalCategory
set_option linter.style.emptyLine false
set_option linter.style.longLine false

namespace AlgebraicGeometry
open Scheme
universe u' u

set_option debug.skipKernelTC true in
lemma ide_tensorObj_probe
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
  | .const n ls => s!"{n}/{e.getAppNumArgs}/{ls}"
  | .proj n i _ => s!"proj:{n}.{i}/{e.getAppNumArgs}"
  | .lam .. => "lam"
  | .forallE .. => "forall"
  | f => s!"{f.ctorName}/{e.getAppNumArgs}"

private partial def hits (e : Expr) (needle : Name) (arity : Nat)
    (path : String := "root") : Array String := Id.run do
  let here := if e.getAppFn.isConstOf needle && e.getAppNumArgs == arity then #[path] else #[]
  match e with
  | .app f x => return here ++ hits f needle arity (path ++ "/fn") ++ hits x needle arity (path ++ "/arg")
  | .lam _ d b _ | .forallE _ d b _ =>
    return here ++ hits d needle arity (path ++ "/domain") ++ hits b needle arity (path ++ "/body")
  | .letE _ t v b _ =>
    return here ++ hits t needle arity (path ++ "/type") ++ hits v needle arity (path ++ "/value") ++ hits b needle arity (path ++ "/body")
  | .proj _ _ x | .mdata _ x => return here ++ hits x needle arity (path ++ "/proj")
  | _ => return here

private def snap (stage side operation : String) (e : Expr) : MetaM Unit := do
  let ty ← inferType e
  let sh := hits e `instMonoidalCategoryHomotopyCategoryIntUp_weilConjectures 8
  let ca := hits e `HomotopyCategory.MonoidalCategory.instMonoidalCategory 19
  logInfo m!"[IDE-SNAP] stage={stage} side={side} op={operation} hash={e.hash} size={e.sizeWithoutSharing} head={head e} type={head ty} shortcut={sh.size} canonical={ca.size} shortcutPaths={sh} canonicalPaths={ca}"

private def kernelCmp (env : Environment) (label : String) (a b : Expr) : MetaM Unit := do
  let t0 ← IO.monoMsNow
  let result := Kernel.isDefEq env (← getLCtx) a b
  let t1 ← IO.monoMsNow
  let answer := match result with | .ok v => s!"{v}" | .error _ => "error"
  logInfo m!"[IDE-CMP] {label} structural={a == b} defeq={answer} ms={t1-t0}"

private def kernelCheck (env : Environment) (label : String) (e : Expr) : MetaM Unit := do
  let result := Kernel.check env (← getLCtx) e
  let answer := match result with | .ok t => s!"ok:{head t}" | .error _ => "error"
  logInfo m!"[IDE-CHECK] {label} {answer}"

private def field (env : Environment) (side name : String) (i : Nat)
    (provider reduced : Expr) : MetaM Expr := do
  let projection := Expr.proj `CategoryTheory.MonoidalCategoryStruct i provider
  let extracted := reduced.getAppArgs[i]!
  let projected ← whnf projection
  let fieldWhnf ← whnf extracted
  snap ("S3." ++ name ++ ".projection") side "unreduced-projection" projection
  snap ("S3." ++ name ++ ".extracted") side "constructor-field" extracted
  snap ("S3." ++ name ++ ".whnf") side "projection-whnf" projected
  snap ("S3." ++ name ++ ".field-whnf") side "field-whnf" fieldWhnf
  kernelCheck env (side ++ "." ++ name ++ ".projection") projection
  return extracted

private def staged (env : Environment) (a b : Expr) : MetaM Unit := do
  let pa := (a.getAppArgs[2]!).getAppArgs[2]!
  let pb := (b.getAppArgs[2]!).getAppArgs[2]!
  snap "S0" "checked" "none" pa
  snap "S0" "stored" "none" pb
  logInfo m!"[IDE-DUMP] S0.checked {repr pa}"
  logInfo m!"[IDE-DUMP] S0.stored {repr pb}"
  let ta ← inferType pa
  let tb ← inferType pb
  let twa ← whnf ta
  let twb ← whnf tb
  snap "S1" "checked" "type-whnf" twa
  snap "S1" "stored" "type-whnf" twb
  kernelCmp env "S1.type" twa twb
  let wa ← whnf pa
  let wb ← whnf pb
  snap "S2" "checked" "value-whnf" wa
  snap "S2" "stored" "value-whnf" wb
  kernelCmp env "S2.value" wa wb
  for (name, i) in #[ ("tensorObj", 2), ("whiskerLeft", 3), ("whiskerRight", 4) ] do
    let fa ← field env "checked" name i pa wa
    let fb ← field env "stored" name i pb wb
    kernelCmp env ("S3." ++ name) fa fb
  for (label, x, y) in #[("A", pa, pa), ("B", pb, pb), ("C", pa, pb), ("D", pb, pa)] do
    kernelCheck env ("R3." ++ label ++ ".checked") x
    kernelCheck env ("R3." ++ label ++ ".stored") y
    let wx ← whnf x
    let wy ← whnf y
    snap ("R3." ++ label) "checked" "value-whnf" wx
    snap ("R3." ++ label) "stored" "value-whnf" wy
    kernelCmp env ("R3." ++ label) x y
  for mode in [TransparencyMode.reducible, .instances, .default, .all] do
    let xa ← withTransparency mode <| whnf pa
    let xb ← withTransparency mode <| whnf pb
    snap (s!"R5.{mode}") "checked" "provider-whnf" xa
    snap (s!"R5.{mode}") "stored" "provider-whnf" xb
    let saved ← saveState
    let defeq ← withTransparency mode <| isDefEq pa pb
    restoreState saved
    logInfo m!"[IDE-R5] mode={mode} metaDefEq={defeq} structural={xa == xb}"

set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let some info := env.find? ``ide_tensorObj_probe | throwError "missing probe"
  let checked ← match Kernel.check env default (info.value! true) with
    | .ok ty => pure ty
    | .error _ => throwError "kernel check failed"
  let rec descend (a b : Expr) (n : Nat) : MetaM Unit := do
    match n with
    | 0 => staged env a b
    | n+1 =>
      match a, b with
      | .forallE name ty body _, .forallE _ _ body' _ =>
        withLocalDeclD name ty fun x => descend (body.instantiate1 x) (body'.instantiate1 x) n
      | _, _ => throwError "bad binder path"
  liftTermElabM <| descend checked info.type 12

end AlgebraicGeometry
