import WeilConjectures.SixFunctors.Etale.Derived.Tensor

open Lean Elab Command Meta
open CategoryTheory Limits MonoidalCategory
set_option linter.style.emptyLine false
set_option linter.style.longLine false

namespace AlgebraicGeometry
open Scheme
universe u' u

set_option debug.skipKernelTC true in
lemma icd_tensorObj_probe
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
  | .proj n i _ => s!"proj {n}.{i}/{e.getAppNumArgs}"
  | .fvar _ => s!"fvar/{e.getAppNumArgs}"
  | .lam .. => "lam"
  | .forallE .. => "forall"
  | f => s!"{f.ctorName}/{e.getAppNumArgs}"

private def levels (e : Expr) : String :=
  match e.getAppFn with
  | .const _ ls => toString ls
  | _ => "none"

private partial def findApps (e : Expr) (needle : Name) (arity : Nat)
    (path : String := "root") : Array (String × Expr) :=
  let here := if e.getAppFn.isConstOf needle && e.getAppNumArgs == arity then #[(path, e)] else #[]
  match e with
  | .app f x => here ++ findApps f needle arity (path ++ "/fn") ++ findApps x needle arity (path ++ "/arg")
  | .lam _ d b _ | .forallE _ d b _ => here ++ findApps d needle arity (path ++ "/domain") ++ findApps b needle arity (path ++ "/body")
  | .letE _ t v b _ => here ++ findApps t needle arity (path ++ "/type") ++ findApps v needle arity (path ++ "/value") ++ findApps b needle arity (path ++ "/body")
  | .proj _ _ x | .mdata _ x => here ++ findApps x needle arity (path ++ "/proj")
  | _ => here

private def resultText (r : Except Kernel.Exception Bool) : String :=
  match r with
  | .ok b => s!"ok:{b}"
  | .error _ => "error"

private def cmp (env : Environment) (label : String) (a b : Expr) : MetaM Unit := do
  let t0 ← IO.monoMsNow
  let r := Kernel.isDefEq env (← getLCtx) a b
  let t1 ← IO.monoMsNow
  logInfo m!"[P2-CMP] {label} result={resultText r} wall_ms={t1-t0} lhs={a.hash} rhs={b.hash}"

private def appInfo (label : String) (e : Expr) : MetaM Unit := do
  let ty ← inferType e
  logInfo m!"[P2-APP] {label} pathless hash={e.hash} size={e.sizeWithoutSharing} head={head e} levels={levels e} typeHash={ty.hash} typeSize={ty.sizeWithoutSharing}"
  logInfo m!"[P2-DUMP] {label} {repr e}"
  let args := e.getAppArgs
  for i in [0:args.size] do
    let a := args[i]!
    let aty ← inferType a
    logInfo m!"[P2-ARG] {label} i={i} hash={a.hash} size={a.sizeWithoutSharing} head={head a} typeHash={aty.hash} typeHead={head aty} equalSelf={a.equal a}"
    logInfo m!"[P2-ARGDUMP] {label} i={i} {repr a}"

private def hybrid (label : String) (base other : Expr) (index : Nat) : MetaM Unit := do
  let bs := base.getAppArgs
  let os := other.getAppArgs
  if index >= bs.size || index >= os.size then
    logInfo m!"[P2-HYBRID] {label} index={index} valid=false reason=missing"
  else
    let hs := bs.set! index os[index]!
    let h := mkAppN base.getAppFn hs
    try
      checkWithKernel h
      logInfo m!"[P2-HYBRID] {label} index={index} valid=true hash={h.hash} size={h.sizeWithoutSharing}"
      cmp (← getEnv) (label ++ "-vs-base") h base
    catch ex =>
      logInfo m!"[P2-HYBRID] {label} index={index} valid=false reason={ex.toMessageData}"

run_cmd do
  let env ← getEnv
  let some info := env.find? ``icd_tensorObj_probe | throwError "missing probe"
  let value := info.value! true
  let checked ← match Kernel.check env default value with
    | .ok ty => pure ty
    | .error _ => throwError "check failed"
  let rec descend (a b : Expr) (n : Nat) : MetaM Unit := do
    match n with
    | 0 =>
      let la := findApps a `instMonoidalCategoryHomotopyCategoryIntUp_weilConjectures 8
      let rb := findApps b `instMonoidalCategoryHomotopyCategoryIntUp_weilConjectures 8
      logInfo m!"[P2-ROOT] checkedHash={a.hash} checkedSize={a.sizeWithoutSharing} storedHash={b.hash} storedSize={b.sizeWithoutSharing} checkedApps={la.size} storedApps={rb.size}"
      for i in [0:la.size] do
        let (p,e) := la[i]!
        appInfo s!"checked.{i}.path={p}" e
      for i in [0:rb.size] do
        let (p,e) := rb[i]!
        appInfo s!"stored.{i}.path={p}" e
      if la.size > 0 && rb.size > 0 then
        let l := la[0]!.2
        let r := rb[0]!.2
        cmp env "direct-l-r" l r
        cmp env "direct-r-l" r l
        let lty ← inferType l
        let rty ← inferType r
        cmp env "result-type-l-r" lty rty
        logInfo m!"[P2-TYPES] lhsType={repr lty} rhsType={repr rty} typeEqual={lty == rty}"
        for i in [0:l.getAppNumArgs] do
          let x := l.getAppArgs[i]!
          let y := r.getAppArgs[i]!
          logInfo m!"[P2-ARGCMP] i={i} equal={x == y} lhsHash={x.hash} rhsHash={y.hash}"
          cmp env s!"arg-{i}" x y
        for i in [0:l.getAppNumArgs] do
          hybrid s!"checked-base-stored-arg{i}" l r i
          hybrid s!"stored-base-checked-arg{i}" r l i
        let lnorm := l
        let rnorm := r
        cmp env "normalized-level-placeholder" lnorm rnorm
      let pl := if la.size > 0 then la[0]!.2 else a
      let pr := if rb.size > 0 then rb[0]!.2 else b
      cmp env "surrounding-body" a b
      logInfo m!"[P2-PARENT] checkedParent={head a} storedParent={head b} checkedShortcut={pl.hash} storedShortcut={pr.hash}"
    | n+1 =>
      match a, b with
      | .forallE name ty body _, .forallE _ _ body' _ =>
        withLocalDeclD name ty fun x => descend (body.instantiate1 x) (body'.instantiate1 x) n
      | _, _ => throwError m!"not forall depth {n}"
  liftTermElabM <| descend checked info.type 12

end AlgebraicGeometry
