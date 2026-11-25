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
  let canonical := `HomotopyCategory.MonoidalCategory.instMonoidalCategory
  let shortcut := `instMonoidalCategoryHomotopyCategoryIntUp_weilConjectures
  for n in [`CategoryTheory.Functor.HasDerivedMonoidalCategory.curriedTensor_hasLeftDerivedFunctor₂,
      `DerivedCategory.hasDerivedMonoidalCategory,
      `DerivedCategory.isLeftDerivedFunctor₂CurriedTensor,
      `AlgebraicGeometry.Etale.isLeftDerivedFunctor₂_derivedTensor,
      `AlgebraicGeometry.Etale.derivedTensor] do
    match env.find? n with
    | some (.defnInfo v) =>
      logInfo m!"[ISF-ORIGIN] {n} def type canonical={containsConst v.type canonical} shortcut={containsConst v.type shortcut} value canonical={containsConst v.value canonical} shortcut={containsConst v.value shortcut}"
    | some (.thmInfo v) =>
      logInfo m!"[ISF-ORIGIN] {n} thm type canonical={containsConst v.type canonical} shortcut={containsConst v.type shortcut} value canonical={containsConst v.value canonical} shortcut={containsConst v.value shortcut}"
    | some (.opaqueInfo v) =>
      logInfo m!"[ISF-ORIGIN] {n} opaque type canonical={containsConst v.type canonical} shortcut={containsConst v.type shortcut}"
    | some _ => logInfo m!"[ISF-ORIGIN] {n} other"
    | none => logInfo m!"[ISF-ORIGIN] {n} missing"
