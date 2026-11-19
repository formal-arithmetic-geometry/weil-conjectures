
open Lean Lean.Meta

set_option maxHeartbeats 10000000

private partial def closingLets (e : Expr) : Expr :=
  match e with
  | .letE _ _ value body _ => closingLets (body.instantiate1 value)
  | _ => e

private def headName (e : Expr) : String :=
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

run_meta do
  let env ← getEnv
  match (← getConstInfo `CategoryTheory.NatTrans.app) with
  | .defnInfo d =>
    logInfo m!"NatTrans.app hint={match d.hints with | .regular h => s!"regular {h}" | .abbrev => "abbrev" | .opaque => "opaque"}"
  | _ => pure ()
  let info ← getConstInfo
    `AlgebraicGeometry.ProEtale.not_preservesColimitsOfShape_rightDerivedLowerStar_of_isAbelianVariety
  lambdaTelescope (info.value! (allowOpaque := true)) fun _ raw => do
    let body := closingLets raw
    lambdaTelescope body.getAppArgs[4]! fun _ branch => do
      lambdaTelescope branch.getAppArgs[17]! fun _ inner => do
        lambdaTelescope inner.getAppArgs[4]! fun _ intro => do
          lambdaTelescope intro.getAppArgs[3]! fun _ proofBody => do
            let lctx ← getLCtx
            let congrTerm := proofBody.getAppArgs[0]!.getAppArgs[1]!.getAppArgs[2]!
            let args := congrTerm.getAppArgs
            let appPrefix := mkAppN congrTerm.getAppFn (args.extract 0 7)
            let .ok actual := Kernel.check env lctx args[7]!
              | throwError "zero_comp proof did not Kernel-check"
            let .ok fnType := Kernel.check env lctx appPrefix
              | throwError "congr prefix did not Kernel-check"
            let .ok (.forallE _ expected _ _) := Kernel.whnf env lctx fnType
              | throwError "congr final binder missing"
            let left := actual.getAppArgs[1]!.getAppArgs[6]!
            let right := expected.getAppArgs[1]!.getAppArgs[6]!
            let la := left.getAppArgs
            let ra := right.getAppArgs
            logInfo m!"NatTrans pair {headName left}/{headName right}; args={la.size}/{ra.size}; same head={left.getAppFn == right.getAppFn}"
            for i in [:min la.size ra.size] do
              let a := la[i]!
              let b := ra[i]!
              let start ← IO.monoMsNow
              let result := Kernel.isDefEq env lctx a b
              let stop ← IO.monoMsNow
              logInfo m!"NatTrans arg {i}: {headName a}/{headName b}, structural={a == b}, defeq={stop - start} ms, result={match result with | .ok true => "equal" | .ok false => "unequal" | .error _ => "error"}"
            let majorIndex := la.size - 2
            let aligned := mkAppN right.getAppFn (ra.set! majorIndex la[majorIndex]!)
            let .ok alignedType := Kernel.check env lctx aligned
              | throwError "aligned NatTrans did not Kernel-check"
            let .ok rightType := Kernel.check env lctx right
              | throwError "original NatTrans did not Kernel-check"
            logInfo m!"aligned major {majorIndex}; result type structurally equal={alignedType == rightType}"
            for (label, a, b) in [("original", left, right),
                ("aligned", left, aligned), ("right/aligned", right, aligned)] do
              let start ← IO.monoMsNow
              let result := Kernel.isDefEq env lctx a b
              let stop ← IO.monoMsNow
              logInfo m!"NatTrans {label}: {stop - start} ms, result={match result with | .ok true => "equal" | .ok false => "unequal" | .error _ => "error"}"
