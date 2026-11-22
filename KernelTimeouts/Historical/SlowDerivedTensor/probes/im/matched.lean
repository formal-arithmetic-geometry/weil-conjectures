import WeilConjectures.SixFunctors.Etale.Derived.Tensor

open Lean Elab Command Meta
open CategoryTheory Limits MonoidalCategory
set_option linter.style.emptyLine false
set_option linter.style.longLine false

namespace AlgebraicGeometry

open Scheme

universe u' u

set_option debug.skipKernelTC true in
lemma imTensorMatched
    (A : Type u')
    [Category.{u + 1, u'} A]
    [Abelian A]
    [IsGrothendieckAbelian.{u + 1, u + 1, u'} A]
    [MonoidalCategory A]
    [MonoidalPreadditive A]
    [SymmetricCategory A]
    (X : Scheme.{u})
    [MonoidalClosed A]
    [Abelian.HasFunctorialFlatResolution A]
    (K L : DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    (let p : MonoidalCategoryStruct (DerivedCategory (Sheaf X.smallEtaleTopology A)) := inferInstance
     @tensorObj (DerivedCategory (Sheaf X.smallEtaleTopology A)) _ p K L) =
    (let q : MonoidalCategoryStruct (DerivedCategory (Sheaf X.smallEtaleTopology A)) := inferInstance
     @tensorObj (DerivedCategory (Sheaf X.smallEtaleTopology A)) _ q K L) := by
  sorry

set_option debug.skipKernelTC true in
lemma imTensorAligned
    (A : Type u')
    [Category.{u + 1, u'} A]
    [Abelian A]
    [IsGrothendieckAbelian.{u + 1, u + 1, u'} A]
    [MonoidalCategory A]
    [MonoidalPreadditive A]
    [SymmetricCategory A]
    (X : Scheme.{u})
    [MonoidalClosed A]
    [Abelian.HasFunctorialFlatResolution A]
    (K L : DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    (let p : MonoidalCategoryStruct (DerivedCategory (Sheaf X.smallEtaleTopology A)) := inferInstance
     @tensorObj (DerivedCategory (Sheaf X.smallEtaleTopology A)) _ p K L) =
    (let q : MonoidalCategoryStruct (DerivedCategory (Sheaf X.smallEtaleTopology A)) := inferInstance
     @tensorObj (DerivedCategory (Sheaf X.smallEtaleTopology A)) _ q K L) := by
  sorry

private def head (e : Expr) : String :=
  match e.getAppFn with
  | .const n _ => s!"{n}"
  | .proj n i _ => s!"{n}.{i}"
  | .fvar _ => "fvar"
  | _ => toString e.getAppFn.ctorName

private partial def findEq (env : Environment) (e : Expr) (label : String) : MetaM Unit := do
  match e with
  | .forallE n d body _ =>
    withLocalDeclD n d fun x => findEq env (body.instantiate1 x) label
  | _ =>
    let args := e.getAppArgs
    if e.isAppOfArity ``Eq 3 then
      let lhs := args[1]!
      let rhs := args[2]!
      let t0 ← IO.monoMsNow
      let result := Kernel.isDefEq env (← getLCtx) lhs rhs
      let t1 ← IO.monoMsNow
      let status := match result with | .ok b => s!"{b}" | .error _ => "error"
      logInfo m!"IM-TENSOR name={label} ms={t1-t0} result={status} lhs={head lhs} rhs={head rhs} lhsSize={lhs.sizeWithoutSharing} rhsSize={rhs.sizeWithoutSharing} exact={lhs.equal rhs}"
    else
      logInfo m!"IM-TENSOR invalid name={label} propositionHead={head e}"

set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  for (n, label) in [(``imTensorMatched, "matched"), (``imTensorAligned, "aligned")] do
    let some info := env.find? n | throwError m!"missing {n}"
    liftTermElabM <| findEq env info.type label

end AlgebraicGeometry
