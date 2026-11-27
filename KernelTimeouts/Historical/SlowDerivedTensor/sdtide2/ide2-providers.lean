import WeilConjectures.SixFunctors.Etale.Derived.Tensor

open Lean Elab Command Meta
set_option linter.style.emptyLine false
set_option linter.style.longLine false

private partial def constPaths (e : Expr) (needle : Name) (path : String := "root") : Array String :=
  let here := match e with
    | .const n _ => if n == needle then #[path] else #[]
    | _ => #[]
  match e with
  | .app f x => here ++ constPaths f needle (path ++ "/fn") ++
      constPaths x needle (path ++ "/arg")
  | .lam _ d b _ | .forallE _ d b _ => here ++ constPaths d needle (path ++ "/domain") ++
      constPaths b needle (path ++ "/body")
  | .letE _ t v b _ => here ++ constPaths t needle (path ++ "/type") ++
      constPaths v needle (path ++ "/value") ++ constPaths b needle (path ++ "/body")
  | .proj _ _ x | .mdata _ x => here ++ constPaths x needle (path ++ "/proj")
  | _ => here

set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let stem := `instMonoidalCategoryHomotopyCategoryIntUp_weilConjectures
  let some (.defnInfo shortcut) := env.find? stem | throwError "shortcut missing"
  liftTermElabM do
    for i in [1:13] do
      let n := stem ++ Name.str .anonymous s!"_proof_{i}"
      let paths := constPaths shortcut.value n
      match env.find? n with
      | none => logInfo m!"[P-DECL] {n} absent paths={paths}"
      | some info =>
        let kind := match info with
          | .thmInfo _ => "theorem"
          | .defnInfo _ => "definition"
          | .opaqueInfo _ => "opaque"
          | _ => "other"
        let typ ← ppExpr info.type
        logInfo m!"[P-DECL] {n} kind={kind} paths={paths} type={typ}"
    let n := `HomotopyCategory.MonoidalCategory.instMonoidalCategory
    let paths := constPaths shortcut.value n
    logInfo m!"[P-CANONICAL] paths={paths}"
    for i in [1:13] do
      let owner := stem ++ Name.str .anonymous s!"_proof_{i}"
      let some info := env.find? owner | throwError m!"missing {owner}"
      let body := info.value! true
      for j in [1:13] do
        let callee := stem ++ Name.str .anonymous s!"_proof_{j}"
        let uses := constPaths body callee
        if !uses.isEmpty then
          logInfo m!"[P-DEP] proof_{i} -> proof_{j} count={uses.size} paths={uses}"
