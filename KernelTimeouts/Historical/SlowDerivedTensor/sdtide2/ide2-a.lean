import WeilConjectures.SixFunctors.Etale.Derived.Tensor

open Lean Elab Command Meta
open CategoryTheory Limits MonoidalCategory
set_option linter.style.emptyLine false
set_option linter.style.longLine false

namespace AlgebraicGeometry
open Scheme
universe u' u

set_option debug.skipKernelTC true in
lemma ide2_probe
    (A : Type u') [Category.{u + 1, u'} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1, u + 1, u'} A] [MonoidalCategory A]
    [MonoidalPreadditive A] [SymmetricCategory A] (X : Scheme.{u})
    [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    (K L : DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    @tensorObj (DerivedCategory (Sheaf X.smallEtaleTopology A)) _ inferInstance K L =
    @tensorObj (DerivedMonoidal DerivedCategory.Qh
      (HomotopyCategory.quasiIso (Sheaf X.smallEtaleTopology A) (ComplexShape.up ℤ)))
      _ inferInstance K L := by rfl

private def h (e : Expr) : String :=
  match e.getAppFn with
  | .const n ls => s!"{n}/{e.getAppNumArgs}/{ls}"
  | .proj n i _ => s!"proj:{n}.{i}"
  | .fvar _ => "fvar"
  | .lam .. => "lam"
  | .forallE .. => "forall"
  | x => s!"{x.ctorName}"

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

private partial def firstDiff (a b : Expr) (path : String := "root") : String :=
  if a == b then s!"{path}:equal" else
  match a, b with
  | .app f x, .app g y =>
    if f == g then firstDiff x y (path ++ "/arg") else firstDiff f g (path ++ "/fn")
  | .lam _ d x _, .lam _ e y _ | .forallE _ d x _, .forallE _ e y _ =>
    if d == e then firstDiff x y (path ++ "/body") else firstDiff d e (path ++ "/domain")
  | .letE _ t v x _, .letE _ u w y _ =>
    if t != u then firstDiff t u (path ++ "/type")
    else if v != w then firstDiff v w (path ++ "/value")
    else firstDiff x y (path ++ "/body")
  | .proj _ _ x, .proj _ _ y => firstDiff x y (path ++ "/proj")
  | .mdata _ x, .mdata _ y => firstDiff x y (path ++ "/mdata")
  | _, _ => s!"{path}: {h a} | {h b}"

private partial def zetaSpine (e : Expr) : Expr :=
  match e with
  | .letE _ _ value body _ => zetaSpine (body.instantiate1 value)
  | _ => e

private def cmp (env : Environment) (label : String) (a b : Expr) : MetaM Unit := do
  let r := Kernel.isDefEq env (← getLCtx) a b
  let ans := match r with | .ok v => s!"{v}" | .error _ => "error"
  logInfo m!"[A-CMP] {label} structural={a == b} defeq={ans} diff={firstDiff a b}"

private def auditDecl (env : Environment) (n : Name) : CommandElabM Unit := do
  match env.find? n with
  | none => logInfo m!"[A-DECL] {n} absent"
  | some info =>
    let kind := match info with
      | .thmInfo _ => "theorem"
      | .defnInfo _ => "definition"
      | .opaqueInfo _ => "opaque"
      | _ => "other"
    logInfo m!"[A-DECL] {n} kind={kind} type={repr info.type} valueHead={h (info.value! true)}"

private def inspect (env : Environment) (a b : Expr) : MetaM Unit := do
  let pa := (a.getAppArgs[2]!).getAppArgs[2]!
  let pb := (b.getAppArgs[2]!).getAppArgs[2]!
  let wa ← whnf pa
  let wb ← whnf pb
  let some direct := findApp? wa `HomotopyCategory.MonoidalCategory.instMonoidalCategory 19
    | throwError "direct canonical missing"
  let some shortcut := findApp? wb `instMonoidalCategoryHomotopyCategoryIntUp_weilConjectures 8
    | throwError "shortcut missing"
  let expanded := zetaSpine (← unfoldDefinition shortcut)
  let some nested := findApp? expanded `HomotopyCategory.MonoidalCategory.instMonoidalCategory 19
    | throwError "nested canonical missing"
  logInfo m!"[A-APPS] direct={h direct} shortcut={h shortcut} nested={h nested} expandedHead={h expanded}"
  logInfo m!"[A-CHECK] direct={(Kernel.check env (← getLCtx) direct).isOk} shortcut={(Kernel.check env (← getLCtx) shortcut).isOk} nested={(Kernel.check env (← getLCtx) nested).isOk}"
  cmp env "canonical" direct nested
  for i in [0:19] do
    let x := direct.getAppArgs[i]!
    let y := nested.getAppArgs[i]!
    let tx ← inferType x
    let ty ← inferType y
    logInfo m!"[A-ARG] i={i} direct={h x} nested={h y} typeDirect={h tx} typeNested={h ty} directHash={x.hash} nestedHash={y.hash}"
    cmp env s!"arg{i}" x y
    cmp env s!"arg{i}.type" tx ty
  let parentA := Expr.proj `CategoryTheory.MonoidalCategory 0 direct
  let parentB := Expr.proj `CategoryTheory.MonoidalCategory 0 shortcut
  let fields := #["tensorObj", "whiskerLeft", "whiskerRight", "tensorHom",
    "tensorUnit", "associator", "leftUnitor", "rightUnitor"]
  for i in [0:8] do
    let x ← whnf (Expr.proj `CategoryTheory.MonoidalCategoryStruct i parentA)
    let y ← whnf (Expr.proj `CategoryTheory.MonoidalCategoryStruct i parentB)
    logInfo m!"[A-FIELD] {fields[i]!} typeDiff={firstDiff (← inferType x) (← inferType y)}"
    cmp env s!"field.{fields[i]!}" x y
  let laws := #["tensorHom_def", "id_tensorHom_id", "tensorHom_comp_tensorHom",
    "whiskerLeft_id", "id_whiskerRight", "associator_naturality",
    "leftUnitor_naturality", "rightUnitor_naturality", "pentagon", "triangle"]
  for i in [1:11] do
    let x ← whnf (Expr.proj `CategoryTheory.MonoidalCategory i direct)
    let y ← whnf (Expr.proj `CategoryTheory.MonoidalCategory i shortcut)
    logInfo m!"[A-LAW] {laws[i-1]!} typeDiff={firstDiff (← inferType x) (← inferType y)}"
    cmp env s!"law.{laws[i-1]!}" x y

set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let stem := `instMonoidalCategoryHomotopyCategoryIntUp_weilConjectures
  auditDecl env stem
  for i in [2:13] do
    auditDecl env (stem ++ Name.str .anonymous s!"_proof_{i}")
  let some info := env.find? ``ide2_probe | throwError "missing probe"
  let checked ← match Kernel.check env default (info.value! true) with
    | .ok ty => pure ty
    | .error _ => throwError "kernel check failed"
  let rec descend (a b : Expr) (n : Nat) : MetaM Unit := do
    match n with
    | 0 => inspect env a b
    | n+1 =>
      match a, b with
      | .forallE name ty body _, .forallE _ _ body' _ =>
        withLocalDeclD name ty fun x => descend (body.instantiate1 x) (body'.instantiate1 x) n
      | _, _ => throwError "bad binder path"
  liftTermElabM <| descend checked info.type 12

end AlgebraicGeometry
