module
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
@[expose] public section
universe u
open CategoryTheory
namespace AlgebraicGeometry.ProEtale
open Scheme
set_option profiler true
set_option profiler.threshold 5
set_option maxHeartbeats 400000

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ]
  {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The explicit body of `upperStarFromPointComp f`. -/
noncomputable abbrev explicitIso :=
  Functor.associator pointUpperStar.{u} (toSpecZ Y)^*[Ab.{u + 1}] (f)^*[Ab.{u + 1}] ≪≫
    Functor.isoWhiskerLeft pointUpperStar ((upperStarComp Ab.{u + 1} f (toSpecZ Y)).symm ≪≫
      eqToIso (congrArg (upperStar Ab.{u + 1}) (comp_toSpecZ f)))

-- t0: control (known fast)
theorem t0 : condensedPullbackHom Λ f = (upperStarFromPointComp f).hom.app Λ := rfl
-- t1: iso level
theorem t1 : upperStarFromPointComp f = explicitIso f := rfl
-- t2: hom level
theorem t2 : (upperStarFromPointComp f).hom = (explicitIso f).hom := rfl
-- t4: source functor
theorem t4 : (upperStarFromPoint Y ⋙ (f)^*[Ab.{u + 1}]) =
    ((pointUpperStar.{u} ⋙ (toSpecZ Y)^*[Ab.{u + 1}]) ⋙ (f)^*[Ab.{u + 1}]) := rfl
-- t5: source object
theorem t5 : (upperStarFromPoint Y ⋙ (f)^*[Ab.{u + 1}]).obj Λ =
    ((pointUpperStar.{u} ⋙ (toSpecZ Y)^*[Ab.{u + 1}]) ⋙ (f)^*[Ab.{u + 1}]).obj Λ := rfl
-- t3: component (the failing shape), kernel skipped for replay
set_option debug.skipKernelTC true in
theorem t3 : (upperStarFromPointComp f).hom.app Λ = (explicitIso f).hom.app Λ := rfl
open Lean Elab Command

partial def diffs (path : String) (a b : Expr) : Array (String × Expr × Expr) :=
  if a.equal b then #[]
  else match a, b with
  | .app .., .app .. =>
      let fa := a.getAppFn; let fb := b.getAppFn
      let aa := a.getAppArgs; let ab := b.getAppArgs
      if fa.equal fb && aa.size == ab.size then Id.run do
        let mut out := #[]
        for h : i in [0:aa.size] do
          out := out ++ diffs s!"{path}.{i}" aa[i]! ab[i]!
        return out
      else #[(path, a, b)]
  | .forallE _ d₁ b₁ _, .forallE _ d₂ b₂ _ =>
      diffs (path ++ ".dom") d₁ d₂ ++ diffs (path ++ ".bod") b₁ b₂
  | .lam _ d₁ b₁ _, .lam _ d₂ b₂ _ =>
      diffs (path ++ ".dom") d₁ d₂ ++ diffs (path ++ ".bod") b₁ b₂
  | .mdata _ x, y => diffs path x y
  | x, .mdata _ y => diffs path x y
  | .proj _ _ x, .proj _ _ y => diffs (path ++ ".p") x y
  | _, _ => #[(path, a, b)]

def logLine (s : String) : IO Unit := do
  let h ← IO.FS.Handle.mk "/tmp/claude-1002/-home-nguan-gnl1-weil-conjectures/1e356a9f-8fcc-409a-815a-ddcd6a947d04/scratchpad/kdiag.log" .append
  h.putStrLn s; h.flush

run_cmd do
  let env ← getEnv
  let some info := env.find? `AlgebraicGeometry.ProEtale.t3 | throwError "no t3"
  let value := info.value! true
  let declared := info.type
  let t0 ← IO.monoMsNow
  let .ok _ := Lean.Kernel.check env {} declared | throwError "check type failed"
  let t1 ← IO.monoMsNow
  logLine s!"Kernel.check(type): {t1 - t0} ms"
  let .ok inferred := Lean.Kernel.check env {} value | throwError "check value failed"
  let t2 ← IO.monoMsNow
  logLine s!"Kernel.check(value): {t2 - t1} ms"
  logLine s!"Expr.equal inferred declared: {inferred.equal declared}"
  -- strip the binders: both are ∀ ..., Eq _ lhs rhs
  let ds := diffs "T" inferred declared
  logLine s!"number of minimal differences: {ds.size}"
  for d in ds do
    let (p, a, b) := d
    let isPrf : Expr → Bool := fun e => (e.find? (fun s => s.isConst && (s.constName!.toString.splitOn "_proof").length > 1)).isSome
    let pa := a.getAppFn.constName?; let pb := b.getAppFn.constName?
    logLine s!"  {p}: heads {pa} vs {pb}; sizes {a.sizeWithoutSharing} vs {b.sizeWithoutSharing}; proof consts {isPrf a}/{isPrf b}"
  logInfo m!"logged"

open Meta in
run_cmd liftTermElabM do
  let env ← getEnv
  let some info := env.find? `AlgebraicGeometry.ProEtale.t3 | throwError "no t3"
  forallTelescope info.type fun _ body => do
    let lctx ← getLCtx
    let some (_, lhs, rhs) := body.eq? | throwError "not eq"
    let ds := diffs "B" lhs rhs
    for d in ds do
      let (p, a, b) := d
      let t0 ← IO.monoMsNow
      let r := Lean.Kernel.isDefEq env lctx a b
      let t1 ← IO.monoMsNow
      logLine s!"pair {p}: isDefEq = {match r with | .ok b => toString b | .error _ => "error"}, {t1 - t0} ms"

run_cmd do
  let env ← getEnv
  for n in [``CategoryTheory.NatTrans.app, ``CategoryTheory.Iso.hom,
      ``CategoryTheory.CategoryStruct.comp, ``CategoryTheory.Functor.comp,
      ``CategoryTheory.Iso.trans, ``CategoryTheory.Functor.obj,
      ``AlgebraicGeometry.ProEtale.upperStarFromPoint,
      ``AlgebraicGeometry.ProEtale.upperStarFromPointComp,
      ``AlgebraicGeometry.ProEtale.condensedPullbackHom] do
    match env.find? n with
    | some (.defnInfo d) =>
        let h := match d.hints with
          | .opaque => "opaque" | .abbrev => "abbrev" | .regular k => s!"regular {k}"
        logLine s!"hint {n}: {h}"
    | some _ => logLine s!"hint {n}: not a definition"
    | none => logLine s!"hint {n}: not found"

namespace AlgebraicGeometry.ProEtale

/-- A regular (non-abbreviation) wrapper for `NatTrans.app`. -/
def appR {C D : Type*} [Category C] [Category D] {F G : C ⥤ D} (τ : F ⟶ G) (c : C) :
    F.obj c ⟶ G.obj c := τ.app c

-- H1: implicit functor arguments forced to agree
set_option debug.skipKernelTC true in
theorem h1 : (upperStarFromPointComp f).hom.app Λ =
    (explicitIso f : upperStarFromPoint Y ⋙ (f)^*[Ab.{u + 1}] ≅ upperStarFromPoint X).hom.app Λ :=
  rfl

-- H2: regular head, implicit arguments still mismatched
theorem h2 : appR (upperStarFromPointComp f).hom Λ = appR (explicitIso f).hom Λ := rfl

end AlgebraicGeometry.ProEtale

open Meta in
run_cmd liftTermElabM do
  let env ← getEnv
  let some info := env.find? `AlgebraicGeometry.ProEtale.AlgebraicGeometry.ProEtale.h1 | throwError "no h1"
  forallTelescope info.type fun _ body => do
    let some (_, lhs, rhs) := body.eq? | throwError "not eq"
    let ds := diffs "H1" lhs rhs
    logLine s!"H1 minimal differences: {ds.size}"
    for d in ds do
      let (p, a, b) := d
      logLine s!"  {p}: {a.getAppFn.constName?} vs {b.getAppFn.constName?}"

namespace AlgebraicGeometry.ProEtale
set_option diagnostics true in
set_option diagnostics.threshold 200 in
set_option maxHeartbeats 20000 in
theorem t3small : (upperStarFromPointComp f).hom.app Λ = (explicitIso f).hom.app Λ := rfl
end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale
-- H1': implicit functor arguments genuinely forced to agree (only the iso differs)
set_option maxHeartbeats 20000 in
theorem h1' : (upperStarFromPointComp f).hom.app Λ =
    @NatTrans.app _ _ _ _ (upperStarFromPoint Y ⋙ (f)^*[Ab.{u + 1}]) (upperStarFromPoint X)
      (@Iso.hom _ _ (upperStarFromPoint Y ⋙ (f)^*[Ab.{u + 1}]) (upperStarFromPoint X)
        (explicitIso f)) Λ := rfl

-- H2 again, timed under the same small budget
set_option maxHeartbeats 20000 in
theorem h2' : appR (upperStarFromPointComp f).hom Λ = appR (explicitIso f).hom Λ := rfl
end AlgebraicGeometry.ProEtale
