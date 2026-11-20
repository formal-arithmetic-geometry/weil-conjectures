module

import all WeilConjectures.WeilSheaf.Native.NativePullTensor

open Lean Lean.Meta

set_option pp.explicit true
set_option pp.universes true
set_option pp.maxSteps 100000

private def shape : Expr → String
  | .app .. => "app"
  | .const n _ => s!"const {n}"
  | .proj n i _ => s!"proj {n}.{i}"
  | .lam .. => "lambda"
  | .forallE .. => "forall"
  | .letE .. => "let"
  | .fvar .. => "fvar"
  | .bvar .. => "bvar"
  | .mdata .. => "metadata"
  | .sort .. => "sort"
  | .lit .. => "literal"
  | .mvar .. => "mvar"

private def hintText : ReducibilityHints → String
  | .abbrev => "abbrev"
  | .opaque => "opaque"
  | .regular h => s!"regular height {h}"

private def describe (label : String) (e : Expr) : MetaM Unit := do
  let args := e.getAppArgs
  let head := e.getAppFn
  logInfo m!"{label}: outer={shape e}; head={shape head}; args={args.size}"
  match head with
  | .const n ls =>
    logInfo m!"{label}: universes {ls}"
    let info ← getConstInfo n
    match info with
    | .defnInfo d =>
      logInfo m!"{label}: definition, Kernel hint {hintText d.hints}, body outer={shape d.value}, body head={shape d.value.getAppFn}"
    | .thmInfo _ => logInfo m!"{label}: theorem (opaque to ordinary delta)"
    | .axiomInfo _ => logInfo m!"{label}: axiom"
    | _ => logInfo m!"{label}: other declaration kind"
  | .proj n i major =>
    logInfo m!"{label}: projection {n}.{i}, major outer={shape major}, major head={shape major.getAppFn}"
  | _ => pure ()
  for i in [:min args.size 12] do
    let a := args[i]!
    logInfo m!"{label}: arg {i} outer={shape a}, head={shape a.getAppFn}"

private partial def stripForalls (e : Expr) (n : Nat := 0) : Nat × Expr :=
  match e with
  | .forallE _ _ body _ => stripForalls body (n + 1)
  | _ => (n, e)

run_meta do
  let env ← getEnv
  let name := `AlgebraicGeometry.ProEtaleWeilSheaf.nativePullTotalTensor
  let info ← getConstInfo name
  let value := info.value! (allowOpaque := true)
  match Kernel.check env {} value with
  | .error _ => throwError "Kernel.check failed"
  | .ok inferred =>
    logInfo m!"conversion NPT-final: original elaborated expressions are stored as the inferred type of {name}'s value and its declared type"
    describe "actual" inferred
    describe "expected" info.type
    let (actualBinders, lhs) := stripForalls inferred
    let (expectedBinders, rhs) := stripForalls info.type
    logInfo m!"actual binders={actualBinders}; expected binders={expectedBinders}"
    describe "actual result" lhs
    describe "expected result" rhs
