import WeilConjectures.SixFunctors.Etale.Derived.Tensor

open Lean Elab Command

private def head (e : Expr) : String :=
  match e.getAppFn with
  | .const n ls => s!"{n}/{e.getAppNumArgs}/{ls}"
  | .proj n i _ => s!"proj {n}.{i}/{e.getAppNumArgs}"
  | x => s!"{x.ctorName}/{e.getAppNumArgs}"

private partial def peel (e : Expr) (i : Nat := 0) : CommandElabM Expr := do
  match e with
  | .lam n d b bi =>
    let binder := match bi with
      | .default => "explicit"
      | .implicit => "implicit"
      | .strictImplicit => "strictImplicit"
      | .instImplicit => "instance"
    logInfo m!"[DCP-BINDER] i={i} name={n} info={binder} domainHead={head d} domainHash={d.hash}"
    peel b (i+1)
  | .letE n t v b _ =>
    logInfo m!"[DCP-LET] i={i} name={n} typeHead={head t} valueHead={head v}"
    peel b i
  | _ => pure e

run_cmd do
  let env ← getEnv
  for n in [
      `DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory,
      `DerivedCategory.instMonoidalCategory_weilConjectures,
      `DerivedCategory.instMonoidalCategory_weilConjectures._aux_1,
      `CategoryTheory.DerivedMonoidal.instMonoidalCategory,
      `CategoryTheory.DerivedMonoidal,
      `instMonoidalCategoryHomotopyCategoryIntUp_weilConjectures] do
    match env.find? n with
    | some (.defnInfo v) =>
      logInfo m!"[DCP-SPINE] name={n} levels={v.levelParams}"
      let e ← peel v.value
      logInfo m!"[DCP-BODY] name={n} head={head e} hash={e.hash} size={e.sizeWithoutSharing}"
      for i in [0:e.getAppNumArgs] do
        let a := e.getAppArgs[i]!
        logInfo m!"[DCP-BODYARG] name={n} i={i} head={head a} hash={a.hash} size={a.sizeWithoutSharing}"
    | _ => logInfo m!"[DCP-SPINE] name={n} missing"
