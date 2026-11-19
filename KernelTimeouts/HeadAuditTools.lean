module
public import Lean

public section

open Lean Lean.Meta Lean.Elab.Tactic

namespace HeadAuditTools

def shape (e : Expr) : String :=
  match e with
  | .app .. => "app"
  | .const .. => "const"
  | .proj .. => "proj"
  | .lam .. => "lam"
  | .forallE .. => "forall"
  | .letE .. => "let"
  | .fvar .. => "fvar"
  | .bvar .. => "bvar"
  | .sort .. => "sort"
  | .mvar .. => "mvar"
  | .lit .. => "lit"
  | .mdata .. => "mdata"

def head (e : Expr) : String :=
  match e.getAppFn with
  | .const n _ => n.toString
  | .proj n i _ => s!"proj {n}.{i}"
  | .fvar _ => "fvar"
  | .lam .. => "lambda"
  | .forallE .. => "forall"
  | .letE .. => "let"
  | .sort .. => "sort"
  | .bvar .. => "bvar"
  | .mvar .. => "mvar"
  | .lit .. => "literal"
  | .mdata .. => "metadata"
  | .app .. => "nested-app"

def hint (h : ReducibilityHints) : String :=
  match h with
  | .abbrev => "abbrev"
  | .opaque => "opaque"
  | .regular n => s!"regular height {n}"

def metadata (label : String) (e : Expr) : TacticM Unit := do
  match e.getAppFn with
  | .const n us =>
    logInfo m!"{label}: universes={us}"
    match (← getConstInfo n) with
    | .defnInfo v =>
      logInfo m!"{label}: def, {hint v.hints}, immediate body={shape v.value}/{head v.value}"
      let args := v.value.getAppArgs
      for i in [:min args.size 5] do
        logInfo m!"{label}: body arg {i+1}={shape args[i]!}/{head args[i]!}"
    | .thmInfo _ => logInfo m!"{label}: theorem"
    | .axiomInfo _ => logInfo m!"{label}: axiom"
    | .opaqueInfo _ => logInfo m!"{label}: opaque declaration"
    | .recInfo _ => logInfo m!"{label}: recursor"
    | .ctorInfo _ => logInfo m!"{label}: constructor"
    | .inductInfo _ => logInfo m!"{label}: inductive"
    | .quotInfo _ => logInfo m!"{label}: quotient"
  | .proj n i major =>
    logInfo m!"{label}: projection {n}.{i}, major={shape major}/{head major}"
  | _ => pure ()

partial def firstDiff (label : String) (a b : Expr) (fuel : Nat := 25) : TacticM Unit := do
  logInfo m!"{label}: {shape a}/{head a} ({a.getAppArgs.size} args) vs {shape b}/{head b} ({b.getAppArgs.size} args); syntactic={a == b}"
  if a == b then return
  if head a != head b then
    metadata s!"{label} actual" a
    metadata s!"{label} expected" b
  if fuel == 0 then return
  let aa := a.getAppArgs
  let ba := b.getAppArgs
  if aa.size > 0 && aa.size == ba.size && head a == head b then
    for i in [:aa.size] do
      if aa[i]! != ba[i]! then
        firstDiff s!"{label}.{i+1}" aa[i]! ba[i]! (fuel-1)
        return
  match a, b with
  | .proj _ _ am, .proj _ _ bm => firstDiff s!"{label}.major" am bm (fuel-1)
  | .mdata _ av, _ => firstDiff label av b (fuel-1)
  | _, .mdata _ bv => firstDiff label a bv (fuel-1)
  | .letE _ aType av ab _, .letE _ bType bv bb _ =>
    if aType != bType then firstDiff s!"{label}.letType" aType bType (fuel-1)
    else if av != bv then firstDiff s!"{label}.letValue" av bv (fuel-1)
    else firstDiff s!"{label}.letBody" ab bb (fuel-1)
  | .forallE _ aType ab _, .forallE _ bType bb _ =>
    if aType != bType then firstDiff s!"{label}.domain" aType bType (fuel-1)
    else firstDiff s!"{label}.body" ab bb (fuel-1)
  | _, _ => pure ()

partial def letChain (label : String) (a b : Expr) (fuel : Nat := 8) : TacticM Unit := do
  match a, b with
  | .letE an aType av ab _, .letE bn bType bv bb _ =>
    logInfo m!"{label}: let {an} vs {bn}"
    firstDiff s!"{label}.type" aType bType
    firstDiff s!"{label}.value" av bv
    if fuel > 0 then letChain s!"{label}.body" ab bb (fuel-1)
  | _, _ => firstDiff label a b

def pair (actual expected : Expr) : TacticM Unit := do
  let actual := (← instantiateMVars actual).consumeMData
  let expected := (← instantiateMVars expected).consumeMData
  logInfo m!"actual: {shape actual}/{head actual}, argc={actual.getAppArgs.size}"
  metadata "actual" actual
  logInfo m!"expected: {shape expected}/{head expected}, argc={expected.getAppArgs.size}"
  metadata "expected" expected
  let aa := actual.getAppArgs
  let ba := expected.getAppArgs
  if aa.size == 0 && ba.size == 0 then
    if actual.isLet && expected.isLet then letChain "whole" actual expected
    else firstDiff "whole" actual expected
  else if aa.size == ba.size then
    for i in [:aa.size] do
      firstDiff s!"arg{i+1}" aa[i]! ba[i]!
  else firstDiff "whole" actual expected

def applicationArguments (application : Expr) (selected : Option Nat := none)
    (selectedActual : Option Expr := none) : TacticM Unit := do
  let application ← instantiateMVars application
  let fn := application.getAppFn
  let args := application.getAppArgs
  logInfo m!"application: {shape application}/{head application}, argc={args.size}"
  let mut fnType ← inferType fn
  for i in [:args.size] do
    let ty ← whnf fnType
    match ty with
    | .forallE _ domain body _ =>
      let arg := args[i]!
      let actual ← inferType arg
      logInfo m!"binder {i+1}: arg={shape arg}/{head arg}, type={shape actual}/{head actual}, expected={shape domain}/{head domain}, syntactic={actual == domain}"
      if selected == some i then
        let actual ← match selectedActual with
          | some e => inferType e
          | none => pure actual
        pair actual domain
      fnType := body.instantiate1 arg
    | _ =>
      logInfo m!"binder {i+1}: no Pi; remaining type={shape ty}/{head ty}"
      return

end HeadAuditTools
