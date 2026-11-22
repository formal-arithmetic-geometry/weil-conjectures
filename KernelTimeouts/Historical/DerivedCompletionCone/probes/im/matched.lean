import WeilConjectures.CategoryTheory.DerivedCategory.Complete.Defs

open Lean Elab Command Meta
open CategoryTheory Limits MonoidalCategory Opposite

universe u

namespace HistoricalIM

variable {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
  (J : GrothendieckTopology C) {R : Type (u + 1)} [CommRing R] (I : Ideal R)

noncomputable def matchedLeft
    (K : DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))) :
    ℕᵒᵖ ⥤ DerivedCategory (Sheaf J (ModuleCat.{u + 1} R)) :=
  DerivedCategory.derivedCompletionDiagram J I K

noncomputable def matchedRight
    (K : DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))) :
    ℕᵒᵖ ⥤ DerivedCategory (Sheaf J (ModuleCat.{u + 1} R)) :=
  DerivedCategory.derivedCompletionDiagram J I K

set_option debug.skipKernelTC true in
noncomputable def matchedCone
    (K : DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))) :
    Cone (matchedLeft J I K) :=
  show Cone (matchedRight J I K) from sorry

private def head (e : Expr) : String :=
  match e.getAppFn with
  | .const n _ => s!"{n}"
  | .proj n i _ => s!"{n}.{i}"
  | .fvar _ => "fvar"
  | _ => toString e.getAppFn.ctorName

private def phase (n : Name) : CommandElabM Unit := do
  let env ← getEnv
  let some info := env.find? n | throwError m!"missing {n}"
  let value := info.value! true
  let inferred ← match Kernel.check env default value with
    | .ok t => pure t
    | .error _ => throwError "value check failed"
  logInfo m!"IM-PAIR name={n} equal={inferred.equal info.type} inferredHead={head inferred} declaredHead={head info.type} inferredSize={inferred.sizeWithoutSharing} declaredSize={info.type.sizeWithoutSharing}"
  let t0 ← IO.monoMsNow
  let result := Kernel.isDefEq env default inferred info.type
  let t1 ← IO.monoMsNow
  let status := match result with | .ok b => s!"{b}" | .error _ => "error"
  logInfo m!"IM-ROOT name={n} ms={t1-t0} result={status}"

set_option maxHeartbeats 0 in
run_cmd phase ``matchedCone

end HistoricalIM
