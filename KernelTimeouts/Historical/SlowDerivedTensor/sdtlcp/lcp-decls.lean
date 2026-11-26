import WeilConjectures.SixFunctors.Etale.Derived.Tensor

open Lean Elab Command

private partial def contains (e : Expr) (n : Name) : Bool :=
  match e with
  | .const m _ => m == n
  | .app f x => contains f n || contains x n
  | .lam _ d b _ | .forallE _ d b _ => contains d n || contains b n
  | .letE _ t v b _ => contains t n || contains v n || contains b n
  | .proj _ _ x | .mdata _ x => contains x n
  | _ => false

private def h (e : Expr) : String :=
  match e.getAppFn with
  | .const n ls => s!"{n} levels={ls} argc={e.getAppNumArgs}"
  | .proj n i _ => s!"proj {n}.{i} argc={e.getAppNumArgs}"
  | x => s!"{x.ctorName} argc={e.getAppNumArgs}"

private partial def findApps (e : Expr) (n : Name) (arity : Nat) (path : String := "root") : CommandElabM Unit := do
  match e with
  | .app f x =>
    if e.getAppFn.isConstOf n && e.getAppNumArgs == arity then
      logInfo m!"[LCP-APP] name={n} path={path} hash={e.hash} argc={arity}"
      for i in [0:arity] do
        let a := e.getAppArgs[i]!
        logInfo m!"[LCP-APPARG] name={n} path={path} i={i} head={h a} hash={a.hash} size={a.sizeWithoutSharing}"
    findApps f n arity (path ++ "/fn")
    findApps x n arity (path ++ "/arg")
  | .lam _ d b _ | .forallE _ d b _ =>
    findApps d n arity (path ++ "/domain")
    findApps b n arity (path ++ "/body")
  | .letE _ t v b _ =>
    findApps t n arity (path ++ "/type")
    findApps v n arity (path ++ "/value")
    findApps b n arity (path ++ "/body")
  | .proj _ _ x | .mdata _ x => findApps x n arity (path ++ "/proj")
  | _ => pure ()

run_cmd do
  let env ← getEnv
  for n in [
    `DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory,
    `CategoryTheory.DerivedMonoidal.instMonoidalCategory,
    `CategoryTheory.Functor.HasDerivedMonoidalCategory.curriedTensor_hasLeftDerivedFunctor₂,
    `DerivedCategory.hasDerivedMonoidalCategory,
    `CategoryTheory.Functor.HasDerivedMonoidalCategory,
    `CategoryTheory.Functor.HasLeftDerivedFunctor₂,
    `CategoryTheory.MorphismProperty.instHasDerivedMonoidalCategory,
    `CategoryTheory.MorphismProperty.KFlat.instHasDerivedMonoidalCategory,
    `CategoryTheory.DerivedMonoidal.bifunctor,
    `CategoryTheory.Functor.totalLeftDerived,
    `CategoryTheory.Functor.leftDerived₂,
    `DerivedCategory.isLeftDerivedFunctor₂CurriedTensor,
    `AlgebraicGeometry.Etale.isLeftDerivedFunctor₂_derivedTensor,
    `AlgebraicGeometry.Etale.derivedTensor,
    `instMonoidalCategoryHomotopyCategoryIntUp_weilConjectures] do
    match env.find? n with
    | none => logInfo m!"[LCP-DECL] name={n} missing"
    | some ci =>
      let typ := ci.type
      logInfo m!"[LCP-DECL] name={n} typeHash={typ.hash} typeSize={typ.sizeWithoutSharing} typeHead={h typ} typeCanonical={contains typ `HomotopyCategory.MonoidalCategory.instMonoidalCategory} typeShortcut={contains typ `instMonoidalCategoryHomotopyCategoryIntUp_weilConjectures} typeField={contains typ `CategoryTheory.Functor.HasDerivedMonoidalCategory.curriedTensor_hasLeftDerivedFunctor₂}"
      match ci.value? with
      | none => logInfo m!"[LCP-DECL] name={n} noValue"
      | some v =>
        logInfo m!"[LCP-DECL] name={n} valueHash={v.hash} valueSize={v.sizeWithoutSharing} valueHead={h v} valueCanonical={contains v `HomotopyCategory.MonoidalCategory.instMonoidalCategory} valueShortcut={contains v `instMonoidalCategoryHomotopyCategoryIntUp_weilConjectures} valueField={contains v `CategoryTheory.Functor.HasDerivedMonoidalCategory.curriedTensor_hasLeftDerivedFunctor₂}"
        for i in [0:v.getAppNumArgs] do
          let x := v.getAppArgs[i]!
          logInfo m!"[LCP-DECLARG] name={n} i={i} head={h x} hash={x.hash} canonical={contains x `HomotopyCategory.MonoidalCategory.instMonoidalCategory} shortcut={contains x `instMonoidalCategoryHomotopyCategoryIntUp_weilConjectures} field={contains x `CategoryTheory.Functor.HasDerivedMonoidalCategory.curriedTensor_hasLeftDerivedFunctor₂}"
        if n == `DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory then
          findApps v `instMonoidalCategoryHomotopyCategoryIntUp_weilConjectures 8
        if n == `instMonoidalCategoryHomotopyCategoryIntUp_weilConjectures then
          findApps v `HomotopyCategory.MonoidalCategory.instMonoidalCategory 19
        if n == `CategoryTheory.DerivedMonoidal.instMonoidalCategory then
          findApps v `CategoryTheory.Functor.HasDerivedMonoidalCategory.curriedTensor_hasLeftDerivedFunctor₂ 10
