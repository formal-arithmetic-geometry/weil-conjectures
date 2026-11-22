import WeilConjectures.CategoryTheory.DerivedCategory.Complete.Defs

open Lean Elab Command Meta
open CategoryTheory Limits MonoidalCategory Opposite

universe u

namespace HistoricalIM

variable {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
  (J : GrothendieckTopology C) {R : Type (u + 1)} [CommRing R] (I : Ideal R)

noncomputable def objLeft
    (K : DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))) :
    ℕᵒᵖ ⥤ DerivedCategory (Sheaf J (ModuleCat.{u + 1} R)) :=
  DerivedCategory.derivedCompletionDiagram J I K

noncomputable def objRight
    (K : DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))) :
    ℕᵒᵖ ⥤ DerivedCategory (Sheaf J (ModuleCat.{u + 1} R)) :=
  DerivedCategory.derivedCompletionDiagram J I K

set_option debug.skipKernelTC true in
noncomputable def objectComparison
    (K : DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))) :
    (objLeft J I K).obj (op 0) = (objRight J I K).obj (op 0) := by
  sorry

set_option debug.skipKernelTC true in
noncomputable def mapComparison
    (K : DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))) :
    (objLeft J I K).map (𝟙 (op 0)) =
      (objRight J I K).map (𝟙 (op 0)) := by
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
      logInfo m!"IM-FUNCTOR operation={label} ms={t1-t0} result={status} lhs={head lhs} rhs={head rhs} lhsSize={lhs.sizeWithoutSharing} rhsSize={rhs.sizeWithoutSharing} exact={lhs.equal rhs}"
    else
      logInfo m!"IM-FUNCTOR invalid operation={label} propositionHead={head e}"

set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  for (n, label) in [(``objectComparison, "Functor.obj"), (``mapComparison, "Functor.map")] do
    let some info := env.find? n | throwError m!"missing {n}"
    liftTermElabM <| findEq env info.type label

end HistoricalIM
