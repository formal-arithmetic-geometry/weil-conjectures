import WeilConjectures.SixFunctors.Etale.Derived.Tensor

open Lean Elab Command

private partial def containsConst (e : Expr) (n : Name) : Bool :=
  match e with
  | .const m _ => m == n
  | .app f x => containsConst f n || containsConst x n
  | .lam _ d b _ | .forallE _ d b _ => containsConst d n || containsConst b n
  | .letE _ t v b _ => containsConst t n || containsConst v n || containsConst b n
  | .proj _ _ x | .mdata _ x => containsConst x n
  | _ => false

run_cmd do
  let env ← getEnv
  logInfo m!"[PROV-DECL] monoidal fields={getStructureFields env `CategoryTheory.MonoidalCategory}"
  logInfo m!"[PROV-DECL] struct fields={getStructureFields env `CategoryTheory.MonoidalCategoryStruct}"
  for n in [`HomotopyCategory.MonoidalCategory.instMonoidalCategory,
      `instMonoidalCategoryHomotopyCategoryIntUp_weilConjectures,
      `instMonoidalCategoryHomotopyCategoryIntUp_weilConjectures._proof_2,
      `CategoryTheory.MonoidalCategory.ofBifunctor,
      `HomotopyCategory.MonoidalCategory.bifunctor] do
    let priority := ((← liftCoreM <| Lean.Meta.getInstancePriority? n).map toString).getD "none"
    let scope := ((← liftCoreM <| Lean.Meta.getInstanceAttrKind? n).map toString).getD "none"
    logInfo m!"[PROV-REGISTRY] {n} priority={priority} scope={scope}"
    match env.find? n with
    | some (.defnInfo v) =>
      let hint := match v.hints with
        | .opaque => "opaque"
        | .abbrev => "abbrev"
        | .regular h => s!"regular({h})"
      logInfo m!"[PROV-DECL] {n} levels={v.levelParams} hints={hint} type={v.type}"
      logInfo m!"[PROV-VALUE] {n} head={v.value.getAppFn} argc={v.value.getAppNumArgs} value={v.value}"
      if n == `instMonoidalCategoryHomotopyCategoryIntUp_weilConjectures then
        logInfo m!"[PROV-ANCESTRY] shortcut_contains_canonical={containsConst v.value `HomotopyCategory.MonoidalCategory.instMonoidalCategory}"
    | some (.thmInfo v) => logInfo m!"[PROV-DECL] {n} theorem levels={v.levelParams} type={v.type}"
    | some _ => logInfo m!"[PROV-DECL] {n} nondef"
    | none => logInfo m!"[PROV-DECL] {n} missing"
