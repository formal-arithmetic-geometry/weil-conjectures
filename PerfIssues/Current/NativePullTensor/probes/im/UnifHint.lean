module

import all WeilConjectures.WeilSheaf.Native.NativePullTensor

open Lean Lean.Meta CategoryTheory

universe u₁ v₁ u₂ v₂

def auditRegularObj {C : Type u₁} {D : Type u₂}
    [Category.{v₁} C] [Category.{v₂} D] (F : C ⥤ D) (X : C) : D :=
  F.obj X

abbrev auditAbbrevObj {C : Type u₁} {D : Type u₂}
    [Category.{v₁} C] [Category.{v₂} D] (F : C ⥤ D) (X : C) : D :=
  F.obj X

set_option maxHeartbeats 10000000

private partial def bodyAfterLambdas (e : Expr) : Expr :=
  match e with
  | .lam _ _ b _ => bodyAfterLambdas b
  | _ => e

run_meta do
  let env ← getEnv
  for name in [`CategoryTheory.Functor.obj, ``auditRegularObj, ``auditAbbrevObj] do
    match (← getConstInfo name) with
    | .defnInfo d =>
      let after := bodyAfterLambdas d.value
      let bodyShape := match after with
        | .proj n i _ => s!"projection {n}.{i}"
        | .app .. => match after.getAppFn with
          | .const n _ => s!"application {n}"
          | _ => "application with nonconstant head"
        | _ => "other"
      logInfo m!"{name}: hint={match d.hints with | .regular h => s!"regular {h}" | .abbrev => "abbrev" | .opaque => "opaque"}; immediate post-lambda body={bodyShape}"
    | _ => logInfo m!"{name}: not a definition"
  let info ← getConstInfo `AlgebraicGeometry.ProEtaleWeilSheaf.nativePullTotalTensor
  let value := info.value! (allowOpaque := true)
  lambdaTelescope value fun xs body => do
    let lctx ← getLCtx
    let .ok actual := Kernel.check env lctx body
      | throwError "body did not Kernel-check"
    let mut expected := info.type
    for x in xs do
      match expected with
      | .forallE _ _ rest _ => expected := rest.instantiate1 x
      | _ => throwError "declared type has too few binders"
    let actualArgs := actual.getAppArgs
    let expectedArgs := expected.getAppArgs
    let leftEndpoint := actualArgs[2]!
    let rightEndpoint := expectedArgs[2]!
    let leftEndpointArgs := leftEndpoint.getAppArgs
    let rightEndpointArgs := rightEndpoint.getAppArgs
    let leftObj := leftEndpointArgs[6]!
    let rightObj := rightEndpointArgs[6]!
    let la := leftObj.getAppArgs
    let ra := rightObj.getAppArgs
    let levels := match leftObj.getAppFn with
      | .const _ ls => ls
      | _ => []
    let levelArray := levels.toArray
    let wrapperLevels := [levelArray[2]!, levelArray[0]!,
      levelArray[3]!, levelArray[1]!]
    let mkWrapper (name : Name) (args : Array Expr) :=
      mkAppN (mkConst name wrapperLevels)
        #[args[0]!, args[2]!, args[1]!, args[3]!, args[4]!, args[5]!]
    let leftReg := mkWrapper ``auditRegularObj la
    let rightReg := mkWrapper ``auditRegularObj ra
    let leftAbr := mkWrapper ``auditAbbrevObj la
    let rightAbr := mkWrapper ``auditAbbrevObj ra
    for (label, e) in [("regular left", leftReg), ("regular right", rightReg),
        ("abbrev left", leftAbr), ("abbrev right", rightAbr)] do
      let result := Kernel.check env lctx e
      logInfo m!"{label}: well typed={match result with | .ok _ => "yes" | .error _ => "no"}"
      match result with
      | .error _ => throwError "wrapper control did not Kernel-check"
      | .ok _ => pure ()
    for (label, a, b) in [("original", leftObj, rightObj),
        ("same-body regular", leftReg, rightReg),
        ("same-body abbrev", leftAbr, rightAbr),
        ("mixed regular/raw", leftReg, rightObj),
        ("mixed abbrev/raw", leftAbr, rightObj)] do
      let start ← IO.monoMsNow
      let result := Kernel.isDefEq env lctx a b
      let stop ← IO.monoMsNow
      logInfo m!"{label}: {stop - start} ms, result={match result with | .ok true => "equal" | .ok false => "unequal" | .error _ => "error"}"
