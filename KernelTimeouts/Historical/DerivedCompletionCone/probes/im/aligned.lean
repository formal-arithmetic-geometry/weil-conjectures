import WeilConjectures.CategoryTheory.DerivedCategory.Complete.Defs

open Lean Elab Command Meta
open CategoryTheory Limits MonoidalCategory Opposite

universe u

namespace HistoricalIM

variable {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
  (J : GrothendieckTopology C) {R : Type (u + 1)} [CommRing R] (I : Ideal R)

noncomputable def alignedLeft
    (K : DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))) :
    ℕᵒᵖ ⥤ DerivedCategory (Sheaf J (ModuleCat.{u + 1} R)) :=
  DerivedCategory.derivedCompletionDiagram J I K

noncomputable def alignedRight
    (K : DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))) :
    ℕᵒᵖ ⥤ DerivedCategory (Sheaf J (ModuleCat.{u + 1} R)) :=
  DerivedCategory.derivedCompletionDiagram J I K

set_option debug.skipKernelTC true in
noncomputable def alignedCone
    (K : DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))) :
    Cone (alignedLeft J I K) :=
  show Cone (alignedRight J I K) from sorry

private def head (e : Expr) : String :=
  match e.getAppFn with
  | .const n _ => s!"{n}"
  | .proj n i _ => s!"{n}.{i}"
  | .fvar _ => "fvar"
  | _ => toString e.getAppFn.ctorName

set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let some info := env.find? ``alignedCone | throwError "missing alignedCone"
  let inferred ← match Kernel.check env default (info.value! true) with
    | .ok t => pure t
    | .error _ => throwError "value check failed"
  logInfo m!"IM-PAIR name=alignedCone equal={inferred.equal info.type} inferredHead={head inferred} declaredHead={head info.type} inferredSize={inferred.sizeWithoutSharing} declaredSize={info.type.sizeWithoutSharing}"
  let t0 ← IO.monoMsNow
  let result := Kernel.isDefEq env default inferred info.type
  let t1 ← IO.monoMsNow
  let status := match result with | .ok b => s!"{b}" | .error _ => "error"
  logInfo m!"IM-ROOT name=alignedCone ms={t1-t0} result={status}"

end HistoricalIM
