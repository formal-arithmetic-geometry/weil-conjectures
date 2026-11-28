import WeilConjectures.SixFunctors.Etale.Derived.Tensor

open Lean Elab Command Meta

private def head (e : Expr) : String :=
  match e.getAppFn with
  | .const n ls => s!"{n}/{e.getAppNumArgs}/{ls}"
  | .proj n i _ => s!"proj:{n}.{i}/{e.getAppNumArgs}"
  | x => s!"{x.ctorName}/{e.getAppNumArgs}"

private partial def peel (e : Expr) : Nat × Expr :=
  match e with
  | .lam _ _ b _ | .forallE _ _ b _ =>
      let (n, x) := peel b
      (n + 1, x)
  | _ => (0, e)

private def audit (env : Environment) (label : String) (name : Name) : CommandElabM Unit := do
  let some info := env.find? name | throwError m!"missing {name}"
  let val := info.value! true
  let (tn, t) := peel info.type
  let (vn, v) := peel val
  logInfo m!"[DECL] {label} {name} typeBinders={tn} type={head t} valueBinders={vn} value={head v} valueSize={val.sizeWithoutSharing}"
  IO.FS.writeFile s!"../results/decl-{label}-type.raw" (repr info.type).pretty
  IO.FS.writeFile s!"../results/decl-{label}-value.raw" (repr val).pretty
  for (side, e) in #[("type", t), ("value", v)] do
    for i in [0:e.getAppNumArgs] do
      let a := e.getAppArgs[i]!
      logInfo m!"[DECL-ARG] {label}.{side}.{i} {head a} size={a.sizeWithoutSharing}"

set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  for (label, name) in #[("original", `AlgebraicGeometry.Etale.isLeftDerivedFunctor₂_derivedTensor),
      ("derivedTensor", `AlgebraicGeometry.Etale.derivedTensor),
      ("specialized", `DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory),
      ("bridge", `DerivedCategory.instMonoidalCategory_weilConjectures),
      ("bridge-aux", `DerivedCategory.instMonoidalCategory_weilConjectures._aux_1),
      ("generic", `CategoryTheory.DerivedMonoidal.instMonoidalCategory),
      ("left-derivability-adapter", `DerivedCategory.isLeftDerivedFunctor₂CurriedTensor),
      ("left-derivability-bridge", `DerivedCategory.instIsLeftDerivedFunctor₂HomotopyCategoryIntUpCurriedTensorμNatTransQhQuasiIso)] do
    audit env label name
