import WeilConjectures.SixFunctors.Etale.Derived.Tensor

open Lean Elab Command Meta

private partial def contains (e : Expr) (n : Name) : Bool :=
  match e with
  | .const m _ => m == n
  | .app f x => contains f n || contains x n
  | .lam _ d b _ | .forallE _ d b _ => contains d n || contains b n
  | .letE _ t v b _ => contains t n || contains v n || contains b n
  | .proj _ _ x | .mdata _ x => contains x n
  | _ => false

private partial def findApp? (e : Expr) (n : Name) (arity : Nat) : Option Expr :=
  if e.getAppFn.isConstOf n && e.getAppNumArgs == arity then some e else
  match e with
  | .app f x => (findApp? f n arity).orElse fun _ => findApp? x n arity
  | .lam _ d b _ | .forallE _ d b _ =>
    (findApp? d n arity).orElse fun _ => findApp? b n arity
  | .letE _ t v b _ =>
    (findApp? t n arity).orElse fun _ =>
      (findApp? v n arity).orElse fun _ => findApp? b n arity
  | .proj _ _ x | .mdata _ x => findApp? x n arity
  | _ => none

run_cmd do
  let env ← getEnv
  let some (.defnInfo wrapper) := env.find? `DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory
    | throwError "missing wrapper"
  let some app := findApp? wrapper.value `instMonoidalCategoryHomotopyCategoryIntUp_weilConjectures 8
    | throwError "missing shortcut application"
  logInfo m!"[LCP-REDUCE] stage=shortcut-app preHash={app.hash} preSize={app.sizeWithoutSharing} preCanonical={contains app `HomotopyCategory.MonoidalCategory.instMonoidalCategory} preShortcut={contains app `instMonoidalCategoryHomotopyCategoryIntUp_weilConjectures}"
  logInfo m!"[LCP-DUMP-SHORTCUT] {repr app}"
  let post ← liftTermElabM <| unfoldDefinition app
  logInfo m!"[LCP-REDUCE] stage=delta-shortcut postHash={post.hash} postSize={post.sizeWithoutSharing} postCanonical={contains post `HomotopyCategory.MonoidalCategory.instMonoidalCategory} postShortcut={contains post `instMonoidalCategoryHomotopyCategoryIntUp_weilConjectures} postHead={post.getAppFn}"
  let some canon := findApp? post `HomotopyCategory.MonoidalCategory.instMonoidalCategory 19
    | throwError "missing canonical after delta"
  let levels := match canon.getAppFn with
    | .const _ ls => toString ls
    | _ => "none"
  logInfo m!"[LCP-REDUCE] stage=canonical-app hash={canon.hash} size={canon.sizeWithoutSharing} argc={canon.getAppNumArgs} levels={levels}"
  logInfo m!"[LCP-DUMP-CANONICAL] {repr canon}"
