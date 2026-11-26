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
  | .const n ls => s!"const={n} args={ls} argc={e.getAppNumArgs}"
  | .proj n i _ => s!"proj={n}.{i} argc={e.getAppNumArgs}"
  | .fvar _ => s!"fvar argc={e.getAppNumArgs}"
  | .lam .. => "lam"
  | .forallE .. => "forall"
  | f => s!"ctor={f.ctorName} argc={e.getAppNumArgs}"

private partial def walk (needle : Name) (e : Expr) (path : String := "root") : MetaM Unit := do
  match e with
  | .const n _ =>
    if n == needle then
      let ty ← inferType e
      logInfo m!"[LCP-HIT] name={needle} path={path} head={head e} hash={e.hash} typeHash={ty.hash}"
  | .app f x =>
    if f.getAppFn.isConstOf needle && e.getAppNumArgs == 19 then
      logInfo m!"[LCP-PARENT] name={needle} path={path} parentHead={head e} parentHash={e.hash}"
    walk needle f (path ++ "/fn")
    walk needle x (path ++ "/arg")
  | .lam _ d b _ =>
    walk needle d (path ++ "/domain")
    walk needle b (path ++ "/body")
  | .forallE _ d b _ =>
    walk needle d (path ++ "/domain")
    walk needle b (path ++ "/body")
  | .letE _ t v b _ =>
    walk needle t (path ++ "/letType")
    walk needle v (path ++ "/letValue")
    walk needle b (path ++ "/letBody")
  | .proj n i x => walk needle x (path ++ s!"/proj({n},{i})")
  | .mdata _ x => walk needle x (path ++ "/mdata")
  | _ => pure ()

private def summarize (label : String) (e : Expr) : MetaM Unit := do
  let ty ← inferType e
  logInfo m!"[LCP-ROOT] label={label} hash={e.hash} size={e.sizeWithoutSharing} head={head e} typeHash={ty.hash} typeHead={head ty}"
  walk `HomotopyCategory.MonoidalCategory.instMonoidalCategory e
  walk `instMonoidalCategoryHomotopyCategoryIntUp_weilConjectures e
  walk `CategoryTheory.Functor.HasDerivedMonoidalCategory.curriedTensor_hasLeftDerivedFunctor₂ e

private def args (label : String) (e : Expr) : MetaM Unit := do
  logInfo m!"[LCP-SPINE] label={label} head={head e} hash={e.hash} argc={e.getAppNumArgs}"
  for i in [0:e.getAppNumArgs] do
    let x := e.getAppArgs[i]!
    logInfo m!"[LCP-SPINE] label={label} arg={i} head={head x} hash={x.hash} size={x.sizeWithoutSharing}"

private partial def findField (e : Expr) (path : String := "root") : MetaM Unit := do
  match e with
  | .app f x =>
    if e.getAppFn.isConstOf `CategoryTheory.Functor.HasDerivedMonoidalCategory.curriedTensor_hasLeftDerivedFunctor₂ && e.getAppNumArgs == 10 then
      logInfo m!"[LCP-FIELD] path={path} hash={e.hash} size={e.sizeWithoutSharing}"
      for i in [0:10] do
        let a := e.getAppArgs[i]!
        logInfo m!"[LCP-FIELDARG] path={path} i={i} head={head a} hash={a.hash} size={a.sizeWithoutSharing}"
    findField f (path ++ "/fn")
    findField x (path ++ "/arg")
  | .lam _ d b _ | .forallE _ d b _ =>
    findField d (path ++ "/domain")
    findField b (path ++ "/body")
  | .letE _ t v b _ =>
    findField t (path ++ "/type")
    findField v (path ++ "/value")
    findField b (path ++ "/body")
  | .proj _ _ x | .mdata _ x => findField x (path ++ "/proj")
  | _ => pure ()

run_cmd do
  let env ← getEnv
  let some info := env.find? ``icd_tensorObj_probe | throwError "missing probe"
  let value := info.value! true
  let checked ← match Kernel.check env default value with
    | .ok ty => pure ty
    | .error _ => throwError "check failed"
  logInfo m!"[LCP-VALUE] valueHash={value.hash} valueSize={value.sizeWithoutSharing} checkedHash={checked.hash} checkedSize={checked.sizeWithoutSharing}"
  let rec descend (a b : Expr) (n : Nat) : MetaM Unit := do
    match n with
    | 0 =>
      summarize "checked-final-body" a
      summarize "stored-final-body" b
      logInfo m!"[LCP-DUMP-CHECKED] {repr a}"
      logInfo m!"[LCP-DUMP-STORED] {repr b}"
      let aa := a.getAppArgs
      let bb := b.getAppArgs
      logInfo m!"[LCP-BODY] leftArgs={aa.size} rightArgs={bb.size}"
      for i in [0:min aa.size bb.size] do
        logInfo m!"[LCP-ARG] i={i} leftHead={head aa[i]!} rightHead={head bb[i]!} leftHash={aa[i]!.hash} rightHash={bb[i]!.hash}"
      summarize "checked-rhs" aa[2]!
      summarize "stored-rhs" bb[2]!
      let leftProvider := (aa[2]!.getAppArgs)[2]!
      let rightProvider := (bb[2]!.getAppArgs)[2]!
      args "checked-provider-original" leftProvider
      args "stored-provider-original" rightProvider
      summarize "checked-provider-original" leftProvider
      summarize "stored-provider-original" rightProvider
      let leftInstance := leftProvider.getAppArgs[1]!
      let rightInstance := rightProvider.getAppArgs[1]!
      args "checked-provider-instance" leftInstance
      args "stored-provider-instance" rightInstance
      summarize "checked-provider-instance" leftInstance
      summarize "stored-provider-instance" rightInstance
      let leftInstanceWhnf ← whnf leftInstance
      let rightInstanceWhnf ← whnf rightInstance
      args "checked-provider-instance-whnf" leftInstanceWhnf
      args "stored-provider-instance-whnf" rightInstanceWhnf
      summarize "checked-provider-instance-whnf" leftInstanceWhnf
      summarize "stored-provider-instance-whnf" rightInstanceWhnf
      findField leftInstanceWhnf
      findField rightInstanceWhnf
      let leftReduced ← whnf leftProvider
      let rightReduced ← whnf rightProvider
      summarize "checked-provider-whnf" leftReduced
      summarize "stored-provider-whnf" rightReduced
      logInfo m!"[LCP-PROVIDER] checkedOriginal={leftProvider} storedOriginal={rightProvider} checkedReduced={head leftReduced} storedReduced={head rightReduced}"
    | n+1 =>
      match a, b with
      | .forallE name ty body _, .forallE _ _ body' _ =>
        withLocalDeclD name ty fun x => descend (body.instantiate1 x) (body'.instantiate1 x) n
      | _, _ => throwError m!"not forall at depth {n} left={a} right={b}"
  liftTermElabM <| descend checked info.type 12

end AlgebraicGeometry
