import WeilConjectures.SixFunctors.Etale.Derived.Tensor

open Lean Elab Command Meta

private def head (e : Expr) : String :=
  match e.getAppFn with
  | .const n ls => s!"{n}/{e.getAppNumArgs}/{ls}"
  | .proj n i _ => s!"proj:{n}.{i}/{e.getAppNumArgs}"
  | x => s!"{x.ctorName}/{e.getAppNumArgs}"

private partial def walk (e : Expr) (path : String := "root") (parent : Option Name := none) : Array (String × Expr) :=
  let here := match e.getAppFn with
    | .const n _ =>
      if parent != some n && (n == `CategoryTheory.DerivedMonoidal || n == `CategoryTheory.MonoidalCategory.curriedTensor ||
          n == `DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory ||
          n == `CategoryTheory.DerivedMonoidal.instMonoidalCategory ||
          n == `AlgebraicGeometry.Etale.derivedTensor ||
          n == `DerivedCategory.isLeftDerivedFunctor₂CurriedTensor) then
        #[(path, e)] else #[]
    | _ => #[]
  match e with
  | .app f x =>
      let fnName := match e.getAppFn with | .const n _ => some n | _ => none
      here ++ walk f (path ++ "/fn") fnName ++ walk x (path ++ "/arg")
  | .lam _ d b _ | .forallE _ d b _ =>
      here ++ walk d (path ++ "/domain") ++ walk b (path ++ "/body")
  | .letE _ t v b _ =>
      here ++ walk t (path ++ "/type") ++ walk v (path ++ "/value") ++
        walk b (path ++ "/body")
  | .proj _ _ x | .mdata _ x => here ++ walk x (path ++ "/sub")
  | _ => here

private def inspect (label : String) (e : Expr) : MetaM Unit := do
  logInfo m!"[ROOT] {label} head={head e} size={e.sizeWithoutSharing}"
  let mut body := e
  for i in [0:10] do
    match body with
    | .forallE n d b _ =>
      logInfo m!"[BINDER] {label} {i} {n}: {head d}"
      body := b
    | _ => logInfo m!"[BINDER] {label} {i} STOP {head body}"
  logInfo m!"[BODY] {label} head={head body} args={body.getAppNumArgs}"
  for i in [0:body.getAppNumArgs] do
    let a := body.getAppArgs[i]!
    logInfo m!"[BODY-ARG] {label} {i} head={head a} size={a.sizeWithoutSharing}"
  for (path, a) in walk body do
    logInfo m!"[HIT] {label} {path} head={head a} size={a.sizeWithoutSharing}"
    if a.getAppNumArgs < 20 then
      for i in [0:a.getAppNumArgs] do
        let x := a.getAppArgs[i]!
        logInfo m!"[SPINE] {label} {path} arg{i} {head x} size={x.sizeWithoutSharing}"

set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  for (label, n) in #[("original", `AlgebraicGeometry.Etale.isLeftDerivedFunctor₂_derivedTensor),
      ("derivedTensor", `AlgebraicGeometry.Etale.derivedTensor),
      ("adapter", `DerivedCategory.isLeftDerivedFunctor₂CurriedTensor)] do
    let some info := env.find? n | throwError "missing"
    let value := info.value! true
    liftTermElabM do
      inspect (label ++ ".stored") info.type
      inspect (label ++ ".meta-inferred") (← inferType value)
      let checked := Kernel.check env default value
      match checked with
      | .ok ty => inspect (label ++ ".kernel-inferred") ty
      | .error _ => logInfo m!"[KERNEL] {label} failed"
