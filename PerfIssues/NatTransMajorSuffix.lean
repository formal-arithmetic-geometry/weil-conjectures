
open Lean Lean.Meta

set_option maxHeartbeats 10000000

private def natHead (e : Expr) : String :=
  match e.getAppFn with
  | .const n _ => s!"const {n}"
  | .proj n i _ => s!"proj {n}.{i}"
  | .fvar .. => "fvar"
  | .bvar i => s!"bvar {i}"
  | .lam .. => "lambda"
  | .forallE .. => "forall"
  | .letE .. => "let"
  | .mdata .. => "metadata"
  | _ => "other"

private partial def peelNatLambdas (e : Expr) : Expr :=
  match e with
  | .lam _ _ b _ => peelNatLambdas b
  | _ => e

run_meta do
  let env ← getEnv
  for name in [`CategoryTheory.CategoryStruct.comp, `CategoryTheory.NatTrans.app] do
    match (← getConstInfo name) with
    | .defnInfo d =>
      let body := peelNatLambdas d.value
      logInfo m!"{name}: hint={match d.hints with | .regular h => s!"regular {h}" | .abbrev => "abbrev" | .opaque => "opaque"}; one-step post-lambda body={natHead body}"
    | _ => logInfo m!"{name}: other declaration kind"
  let info ← getConstInfo `AlgebraicGeometry.ProEtale.leftDerivedUpperStarTensorComparison_app_app_fac
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
    let actualEqArgs := actual.getAppArgs
    let expectedEqArgs := expected.getAppArgs
    let actualComp := actualEqArgs[1]!
    let expectedComp := expectedEqArgs[1]!
    let actualCompArgs := actualComp.getAppArgs
    let expectedCompArgs := expectedComp.getAppArgs
    let left := actualCompArgs[5]!
    let right := expectedCompArgs[5]!
    let la := left.getAppArgs
    let ra := right.getAppArgs
    logInfo m!"NatTrans.app pair: args={la.size}/{ra.size}, head identical={left.getAppFn == right.getAppFn}"
    for i in [:min la.size ra.size] do
      let a := la[i]!
      let b := ra[i]!
      let start ← IO.monoMsNow
      let result := Kernel.isDefEq env lctx a b
      let stop ← IO.monoMsNow
      logInfo m!"NatTrans arg {i}: {natHead a}/{natHead b}, structural={a == b}, defeq={stop - start} ms, result={match result with | .ok true => "equal" | .ok false => "unequal" | .error _ => "error"}"
    let majorIndex := la.size - 2
    let aligned := mkAppN right.getAppFn (ra.set! majorIndex la[majorIndex]!)
    let .ok alignedType := Kernel.check env lctx aligned
      | throwError "aligned NatTrans.app did not Kernel-check"
    let .ok rightType := Kernel.check env lctx right
      | throwError "original NatTrans.app did not Kernel-check"
    logInfo m!"aligned major argument {majorIndex}; result type structurally equal={alignedType == rightType}"
    for (label, a, b) in [("original", left, right),
        ("aligned", left, aligned), ("right/aligned", right, aligned)] do
      let start ← IO.monoMsNow
      let result := Kernel.isDefEq env lctx a b
      let stop ← IO.monoMsNow
      logInfo m!"NatTrans.app {label}: {stop - start} ms, result={match result with | .ok true => "equal" | .ok false => "unequal" | .error _ => "error"}"
