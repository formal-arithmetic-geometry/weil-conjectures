import WeilConjectures.CategoryTheory.DerivedCategory.Complete.Defs

open Lean Elab Command Meta
open CategoryTheory Limits MonoidalCategory Opposite

universe w v' u' u

namespace HistoricalAD

variable {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
  (J : GrothendieckTopology C) {R : Type (u + 1)} [CommRing R] (I : Ideal R)

set_option debug.skipKernelTC true in
noncomputable def inlineCone
    (K : DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))) :
    Cone (DerivedCategory.quotPowFunctor J I ⋙ tensorLeft K) := sorry

private def headName (e : Expr) : String :=
  match e.getAppFn with
  | .const n _ => toString n
  | .proj n i _ => s!"{n}.{i}"
  | x => toString x.ctorName

private partial def inspect (env : Environment) (a b : Expr) (path : String) : MetaM Nat := do
  if a.equal b then return 0
  if (← isProof a) && (← isProof b) then
    let lctx ← getLCtx
    match Kernel.check env lctx a, Kernel.check env lctx b with
    | .ok ta, .ok tb =>
      let start ← IO.monoMsNow
      let result := Kernel.isDefEq env lctx ta tb
      let stop ← IO.monoMsNow
      let status := match result with
        | .ok true => "equal"
        | .ok false => "unequal"
        | .error _ => "error"
      logInfo m!"AD-POSITION path={path} left={headName a} right={headName b} typeLeft={headName ta} typeRight={headName tb} ms={stop-start} result={status}"
      return 1
    | _, _ =>
      logInfo m!"AD-INVALID path={path} left={headName a} right={headName b}"
      return 0
  match a, b with
  | .forallE n d body _, .forallE _ d' body' _ =>
    let domains ← inspect env d d' s!"{path}/domain"
    let bodies ← withLocalDeclD n d fun x =>
      inspect env (body.instantiate1 x) (body'.instantiate1 x) s!"{path}/body"
    return domains + bodies
  | .app f x, .app g y =>
    let functions ← inspect env f g s!"{path}/fn"
    let arguments ← inspect env x y s!"{path}/arg"
    return functions + arguments
  | _, _ =>
    logInfo m!"AD-NONPROOF path={path} left={headName a} right={headName b}"
    return 0

set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let some info := env.find? ``inlineCone | throwError "missing inlineCone"
  let inferred ← match Kernel.check env default (info.value! true) with
    | .ok ty => pure ty
    | .error _ => throwError "Kernel.check failed"
  let count ← liftTermElabM <| inspect env inferred info.type "root"
  logInfo m!"AD-POSITION-COUNT {count}"

end HistoricalAD
