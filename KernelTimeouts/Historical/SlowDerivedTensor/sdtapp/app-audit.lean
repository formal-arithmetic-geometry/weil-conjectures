import WeilConjectures.SixFunctors.Etale.Derived.Tensor

open Lean Elab Command Meta

private def head (e : Expr) : String :=
  match e.getAppFn with
  | .const n ls => s!"{n}/{e.getAppNumArgs}/{ls}"
  | .proj n i _ => s!"proj:{n}.{i}/{e.getAppNumArgs}"
  | x => s!"{x.ctorName}/{e.getAppNumArgs}"

private partial def hits (e : Expr) (needle : Name) (path : String := "root") : Array String :=
  let here := if e.getAppFn.isConstOf needle then #[path] else #[]
  match e with
  | .app f x => here ++ hits f needle (path ++ "/fn") ++ hits x needle (path ++ "/arg")
  | .lam _ d b _ | .forallE _ d b _ =>
      here ++ hits d needle (path ++ "/domain") ++ hits b needle (path ++ "/body")
  | .letE _ t v b _ =>
      here ++ hits t needle (path ++ "/type") ++ hits v needle (path ++ "/value") ++
        hits b needle (path ++ "/body")
  | .proj _ _ x | .mdata _ x => here ++ hits x needle (path ++ "/sub")
  | _ => here

private def audit (env : Environment) (name : Name) (label : String) : CommandElabM Unit := do
  let some info := env.find? name | throwError m!"missing {name}"
  let value := info.value! true
  IO.FS.writeFile s!"../results/{label}-type.raw" (repr info.type).pretty
  IO.FS.writeFile s!"../results/{label}-value.raw" (repr value).pretty
  logInfo m!"[AUDIT] {label} name={name} type={head info.type} typeSize={info.type.sizeWithoutSharing} value={head value} valueSize={value.sizeWithoutSharing}"
  liftTermElabM do
    let inferred ← inferType value
    IO.FS.writeFile s!"../results/{label}-meta-inferred.raw" (repr inferred).pretty
    logInfo m!"[INFER-META] {label} inferred={head inferred} size={inferred.sizeWithoutSharing} structural={inferred == info.type}"
    for (side, e) in #[("stored", info.type), ("meta-inferred", inferred)] do
      for n in [`CategoryTheory.tensorObj, `CategoryTheory.MonoidalCategoryStruct.tensorObj,
          `CategoryTheory.MonoidalCategory.curriedTensor,
          `CategoryTheory.MonoidalCategory.tensorObj,
          `CategoryTheory.DerivedMonoidal,
          `CategoryTheory.DerivedMonoidal.instMonoidalCategory,
          `DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory] do
        let found := hits e n
        if !found.isEmpty then logInfo m!"[HITS] {label} {side} {n}: {found}"

set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  audit env `AlgebraicGeometry.Etale.isLeftDerivedFunctor₂_derivedTensor "original"
  audit env `AlgebraicGeometry.Etale.derivedTensor "derivedTensor"
  audit env `DerivedCategory.isLeftDerivedFunctor₂CurriedTensor "adapter"
  audit env `DerivedCategory.instIsLeftDerivedFunctor₂CurriedTensor "generic-specialized"
