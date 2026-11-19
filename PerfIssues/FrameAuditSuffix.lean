
open Lean Lean.Meta

private def frameHead (e : Expr) : String :=
  match e.getAppFn with
  | .const n _ => s!"const {n}"
  | .proj n i major => s!"proj {n}.{i} major={match major.getAppFn with | .const m _ => toString m | _ => "other"}"
  | .fvar .. => "fvar"
  | .bvar i => s!"bvar {i}"
  | .lam .. => "lambda"
  | .forallE .. => "forall"
  | .letE .. => "let"
  | .mdata .. => "metadata"
  | _ => "other"

private partial def peelFrames (e : Expr) (steps : Array String := #[]) : Array String × Expr :=
  match e with
  | .lam n _ body _ => peelFrames body (steps.push s!"lambda {n}")
  | .letE n _ value body _ =>
    peelFrames body (steps.push s!"let {n}, value={frameHead value}")
  | .mdata _ body => peelFrames body (steps.push "metadata")
  | _ => (steps, e)

run_meta do
  let name := `AUDIT_TARGET
  let info ← getConstInfo name
  let value := info.value! (allowOpaque := true)
  let (frames, body) := peelFrames value
  logInfo m!"{name}: raw frames={frames.size}"
  for step in frames do logInfo m!"frame: {step}"
  logInfo m!"{name}: terminal body={frameHead body}, args={body.getAppArgs.size}"
  for i in [:min body.getAppArgs.size 32] do
    logInfo m!"terminal arg {i}: {frameHead body.getAppArgs[i]!}"
