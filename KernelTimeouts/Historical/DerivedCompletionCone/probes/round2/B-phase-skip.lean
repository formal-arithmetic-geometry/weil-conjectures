import WeilConjectures.CategoryTheory.DerivedCategory.Complete.Defs

open Lean Elab Command Meta
open CategoryTheory Limits MonoidalCategory Opposite

universe w v' u' u

namespace HistoricalR2

variable {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
  (J : GrothendieckTopology C) {R : Type (u + 1)} [CommRing R] (I : Ideal R)

set_option debug.skipKernelTC true in
noncomputable def inlineConeSkip
    (K : DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))) :
    Cone (DerivedCategory.quotPowFunctor J I ⋙ tensorLeft K) := sorry

noncomputable def namedAbbrevDiagram
    (K : DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))) :
    ℕᵒᵖ ⥤ DerivedCategory (Sheaf J (ModuleCat.{u + 1} R)) :=
  DerivedCategory.quotPowFunctor J I ⋙ tensorLeft K

noncomputable def namedDefDiagram
    (K : DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))) :
    ℕᵒᵖ ⥤ DerivedCategory (Sheaf J (ModuleCat.{u + 1} R)) :=
  DerivedCategory.quotPowFunctor J I ⋙ tensorLeft K

@[reducible] noncomputable def namedReducibleDiagram
    (K : DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))) :
    ℕᵒᵖ ⥤ DerivedCategory (Sheaf J (ModuleCat.{u + 1} R)) :=
  DerivedCategory.quotPowFunctor J I ⋙ tensorLeft K

set_option debug.skipKernelTC true in
noncomputable def namedAbbrevConeSkip
    (K : DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))) :
    Cone (namedAbbrevDiagram J I K) := sorry

set_option debug.skipKernelTC true in
noncomputable def namedDefConeSkip
    (K : DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))) :
    Cone (namedDefDiagram J I K) := sorry

set_option debug.skipKernelTC true in
noncomputable def namedReducibleConeSkip
    (K : DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))) :
    Cone (namedReducibleDiagram J I K) := sorry

set_option debug.skipKernelTC true in
noncomputable def inlineConeExplicitSkip
    [MC : MonoidalCategory (DerivedCategory (Sheaf J (ModuleCat.{u + 1} R)))]
    (K : DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))) :
    Cone (DerivedCategory.quotPowFunctor J I ⋙ tensorLeft K) := sorry

private def phase (n : Name) : CommandElabM Unit := do
  let env ← getEnv
  let some info := env.find? n | throwError m!"missing {n}"
  let v := info.value! true
  let t := info.type
  let t0 ← IO.monoMsNow
  let ci := Kernel.check env default t
  let t1 ← IO.monoMsNow
  let v0 ← IO.monoMsNow
  let cv := Kernel.check env default v
  let v1 ← IO.monoMsNow
  logInfo m!"[R2 B1.1] {n} typeMs={t1-t0} valueMs={v1-v0} valueSize={v.sizeWithoutSharing} typeSize={t.sizeWithoutSharing}"
  let f0 ← IO.monoMsNow
  match ci, cv with
  | .ok it, .ok _ =>
    let fr := Kernel.isDefEq env default it t
    let f1 ← IO.monoMsNow
    match fr with
    | .ok b => logInfo m!"[R2 B1.1] {n} finalResult={b} finalMs={f1-f0}"
    | .error _ => logInfo m!"[R2 B1.1] {n} finalResult=error finalMs={f1-f0}"
  | _, _ => logInfo m!"[R2 B1.1] {n} kernelCheck=error"

private def hints (n : Name) : CommandElabM Unit := do
  let env ← getEnv
  match env.find? n with
  | some (.defnInfo v) =>
    let hs := match v.hints with
      | .opaque => "opaque"
      | .abbrev => "abbrev"
      | .regular h => s!"regular:{h}"
    logInfo m!"[R2 B2.1] hint {n} {hs}"
  | _ => logInfo m!"[R2 B2.1] hint {n} unavailable"

set_option maxHeartbeats 0 in
run_cmd do
  phase ``inlineConeSkip
  phase ``namedAbbrevConeSkip
  phase ``namedDefConeSkip
  phase ``namedReducibleConeSkip
  phase ``inlineConeExplicitSkip
  hints ``namedAbbrevDiagram
  hints ``namedDefDiagram
  hints ``namedReducibleDiagram

end HistoricalR2
