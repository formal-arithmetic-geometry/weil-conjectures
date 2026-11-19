
open Lean Lean.Meta

private def spineHead (e : Expr) : String :=
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

private partial def traceRightSpine (e : Expr) (path : String) (fuel : Nat) : MetaM Unit := do
  if fuel == 0 then return
  match e with
  | .lam n _ body _ =>
    logInfo m!"{path}: lambda {n}"
    traceRightSpine body (path ++ ".body") (fuel - 1)
  | .letE n _ value body _ =>
    logInfo m!"{path}: let {n}, value={spineHead value}"
    traceRightSpine body (path ++ ".body") (fuel - 1)
  | .mdata _ body =>
    logInfo m!"{path}: metadata"
    traceRightSpine body (path ++ ".body") (fuel - 1)
  | .app .. =>
    let args := e.getAppArgs
    logInfo m!"{path}: app {spineHead e}, args={args.size}"
    for i in [args.size - 2:args.size] do
      let arg := args[i]!
      logInfo m!"{path}.arg{i}: {spineHead arg}"
      traceRightSpine arg (path ++ s!".arg{i}") (fuel - 1)
  | _ => logInfo m!"{path}: terminal {spineHead e}"

private partial def stripClosingFrames (e : Expr) : Expr :=
  match e with
  | .lam _ _ body _ => stripClosingFrames body
  | .letE _ _ _ body _ => stripClosingFrames body
  | .mdata _ body => stripClosingFrames body
  | _ => e

run_meta do
  let info ← getConstInfo `AlgebraicGeometry.ProEtale.not_preservesColimitsOfShape_rightDerivedLowerStar_of_isAbelianVariety
  let body := stripClosingFrames (info.value! (allowOpaque := true))
  let args := body.getAppArgs
  logInfo m!"outer proof body={spineHead body}, args={args.size}"
  let branch := args[4]!
  traceRightSpine branch "branch" 16
