/-
Copyright (c) 2023 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Lean

/-! Bounded, instrumented adaptation of Lean 4.33.1 Lean/Replay.lean.
Run with watchdog.py to impose a wall-clock deadline per kernel declaration.
All declarations are checked at trust level zero. No bypasses are used.
-/
open Lean

namespace ComparatorRepro

namespace Replay

structure Context where
  newConstants : Std.HashMap Name ConstantInfo
  typeFirst : Bool := false

structure State where
  env : Kernel.Environment
  remaining : NameSet := {}
  pending : NameSet := {}
  postponedConstructors : NameSet := {}
  postponedRecursors : NameSet := {}

abbrev M := ReaderT Context <| StateRefT State IO

/-- Check if a `Name` still needs processing. If so, move it from `remaining` to `pending`. -/
def isTodo (name : Name) : M Bool := do
  let r := (← get).remaining
  if r.contains name then
    modify fun s => { s with remaining := s.remaining.erase name, pending := s.pending.insert name }
    return true
  else
    return false

/-- Use the current `Environment` to throw a `Kernel.Exception`. -/
def throwKernelException (ex : Kernel.Exception) : M Unit := do
  throw <| .userError <| (← ex.toMessageData {} |>.toString)

/-- Add a declaration, possibly throwing a `Kernel.Exception`. -/
def addDecl (d : Declaration) : M Unit := do
  let out ← IO.getStdout
  let names := d.getTopLevelNames
  if (← read).typeFirst then
    if let .thmDecl v := d then
      let probe := Declaration.thmDecl { v with
        name := .str v.name "_repro_typeOnly"
        type := .forallE `h v.type v.type .default
        value := .lam `h v.type (.bvar 0) .default
        all := [] }
      out.putStrLn s!"BEGIN TYPE_ONLY {names}"
      out.flush
      let start ← IO.monoNanosNow
      match (← get).env.addDeclCore 0 0 probe (cancelTk? := none) with
      | .ok _ => pure ()
      | .error ex => throwKernelException ex
      out.putStrLn s!"END TYPE_ONLY {names} {(← IO.monoNanosNow) - start} ns"
      out.flush
  out.putStrLn s!"BEGIN {names}"
  out.flush
  let start ← IO.monoNanosNow
  match (← get).env.addDeclCore 0 0 d (cancelTk? := none) with
  | .ok env => modify fun s => { s with env }
  | .error ex => throwKernelException ex
  let elapsed := (← IO.monoNanosNow) - start
  out.putStrLn s!"END {names} {elapsed / 1000000} ms ({elapsed} ns)"
  out.flush

mutual
/--
Check if a `Name` still needs to be processed (i.e. is in `remaining`).

If so, recursively replay any constants it refers to,
to ensure we add declarations in the right order.

The construct the `Declaration` from its stored `ConstantInfo`,
and add it to the environment.
-/
partial def replayConstant (name : Name) : M Unit := do
  if ← isTodo name then
    let some ci := (← read).newConstants[name]? | unreachable!
    replayConstants ci.getUsedConstantsAsSet
    -- Check that this name is still pending: a mutual block may have taken care of it.
    if (← get).pending.contains name then
      try
        match ci with
        | .defnInfo   info =>
          addDecl (Declaration.defnDecl   info)
        | .thmInfo    info =>
          -- Ignore duplicate theorems. This code is identical to that in `finalizeImport` before it
          -- added extended duplicates support for the module system, which is not relevant for us
          -- here as we always load all .olean information. We need this case *because* of the module
          -- system -- as we have more data loaded than it, we might encounter duplicate private
          -- theorems where elaboration under the module system would have only one of them in scope.
          if let some (.thmInfo info') := (← get).env.find? ci.name then
            if info.name == info'.name &&
              info.type == info'.type &&
              info.levelParams == info'.levelParams &&
              info.all == info'.all
            then
              return
          addDecl (Declaration.thmDecl    info)
        | .axiomInfo  info =>
          addDecl (Declaration.axiomDecl  info)
        | .opaqueInfo info =>
          addDecl (Declaration.opaqueDecl info)
        | .inductInfo info =>
          let lparams := info.levelParams
          let nparams := info.numParams
          let all ← info.all.mapM fun n => do pure <| ((← read).newConstants[n]!)
          for o in all do
            modify fun s =>
              { s with remaining := s.remaining.erase o.name, pending := s.pending.erase o.name }
          let ctorInfo ← all.mapM fun ci => do
            pure (ci, ← ci.inductiveVal!.ctors.mapM fun n => do
              pure ((← read).newConstants[n]!))
          -- Make sure we are really finished with the constructors.
          for (_, ctors) in ctorInfo do
            for ctor in ctors do
              replayConstants ctor.getUsedConstantsAsSet
          let types : List InductiveType := ctorInfo.map fun ⟨ci, ctors⟩ =>
            { name := ci.name
              type := ci.type
              ctors := ctors.map fun ci => { name := ci.name, type := ci.type } }
          addDecl (Declaration.inductDecl lparams nparams types false)
        -- We postpone checking constructors,
        -- and at the end make sure they are identical
        -- to the constructors generated when we replay the inductives.
        | .ctorInfo info =>
          modify fun s => { s with postponedConstructors := s.postponedConstructors.insert info.name }
        -- Similarly we postpone checking recursors.
        | .recInfo info =>
          modify fun s => { s with postponedRecursors := s.postponedRecursors.insert info.name }
        | .quotInfo _ =>
          -- `Quot.lift` and `Quot.ind` have types that reference `Eq`,
          -- so we need to ensure `Eq` is replayed before adding the quotient declaration.
          replayConstant `Eq
          addDecl (Declaration.quotDecl)
        modify fun s => { s with pending := s.pending.erase name }
      catch ex =>
        throw <| .userError s!"while replaying declaration '{name}':\n{ex}"

/-- Replay a set of constants one at a time. -/
partial def replayConstants (names : NameSet) : M Unit := do
  for n in names do replayConstant n

end

/--
Check that all postponed constructors are identical to those generated
when we replayed the inductives.
-/
def checkPostponedConstructors : M Unit := do
  for ctor in (← get).postponedConstructors do
    match (← get).env.find? ctor, (← read).newConstants[ctor]? with
    | some (.ctorInfo info), some (.ctorInfo info') =>
      if ! (info == info') then throw <| IO.userError s!"Invalid constructor {ctor}"
    | _, _ => throw <| IO.userError s!"No such constructor {ctor}"

/--
Check that all postponed recursors are identical to those generated
when we replayed the inductives.
-/
def checkPostponedRecursors : M Unit := do
  for ctor in (← get).postponedRecursors do
    match (← get).env.find? ctor, (← read).newConstants[ctor]? with
    | some (.recInfo info), some (.recInfo info') =>
      if ! (info == info') then throw <| IO.userError s!"Invalid recursor {ctor}"
    | _, _ => throw <| IO.userError s!"No such recursor {ctor}"

end Replay

open Replay


def run (newConstants : Std.HashMap Name ConstantInfo) (env : Environment)
    (typeFirst := false) : IO Unit := do
  let mut remaining : NameSet := ∅
  for (n, ci) in newConstants.toList do
    if !ci.isUnsafe && !ci.isPartial then remaining := remaining.insert n
  let start ← IO.monoMsNow
  let (_, _) ← StateRefT'.run (s := { env := env.toKernelEnv, remaining }) do
    ReaderT.run (r := { newConstants, typeFirst }) do
      for n in remaining do replayConstant n
      checkPostponedConstructors
      checkPostponedRecursors
  IO.println s!"COMPLETE {remaining.size} constants {(← IO.monoMsNow) - start} ms"

end ComparatorRepro

/-- Reproduce the exporter's two expression transformations independently. -/
partial def normalizeExpr (mode : String) (e : Expr) : StateM (Std.HashMap Expr Expr) Expr := do
  if let some e' := (← get)[e]? then return e'
  let norm := normalizeExpr mode
  let e' ← match e with
    | .mdata _ a =>
      if mode == "lets" then return e.updateMData! (← norm a) else norm a
    | .app f a => return e.updateApp! (← norm f) (← norm a)
    | .lam _ t b _ => return e.updateLambdaE! (← norm t) (← norm b)
    | .forallE _ t b _ => return e.updateForallE! (← norm t) (← norm b)
    | .letE _ t v b nd =>
      return e.updateLet! (← norm t) (← norm v) (← norm b) (mode == "mdata" && nd)
    | .proj _ _ a => return e.updateProj! (← norm a)
    | _ => pure e
  modify (·.insert e e')
  return e'

def normalizeConstant (mode : String) (ci : ConstantInfo) : ConstantInfo := Id.run do
  let norm := fun e => (normalizeExpr mode e).run' {}
  match ci with
  | .defnInfo v => return .defnInfo { v with type := norm v.type, value := norm v.value }
  | .thmInfo v => return .thmInfo { v with type := norm v.type, value := norm v.value }
  | .opaqueInfo v => return .opaqueInfo { v with type := norm v.type, value := norm v.value }
  | _ => return ci

/-- Definitions whose bodies are hidden in ordinary imports, in kernel-relevant closure.
Theorem proofs are roots only for this module; imported theorem proofs are never unfolded.
-/
def auditVisibility (own : Array ConstantInfo) (deps : Environment)
    (imports : Array Import) (arts : NameMap ImportArtifacts) : IO Unit := do
  let exported ← importModules imports {} 0 (level := .exported) (arts := arts)
  let ownMap := own.foldl (fun m ci => m.insert ci.name ci)
    ({} : Std.HashMap Name ConstantInfo)
  let mut todo : List (Name × Nat) := []
  for ci in own do
    for n in ci.getUsedConstantsAsSet do todo := (n, 0) :: todo
  let mut seen : NameSet := {}
  let mut hidden : Array (Nat × Name × Name) := #[]
  while !todo.isEmpty do
    let (n, depth) := todo.head!
    todo := todo.tail!
    if seen.contains n then continue
    seen := seen.insert n
    let some ci := ownMap[n]? <|> deps.find? n | continue
    let mut used := ci.type.getUsedConstantsAsSet
    if let .defnInfo v := ci then
      used := used ++ v.value.getUsedConstantsAsSet
      if !(exported.find? n).any (fun c => c matches .defnInfo _) then
        if let some idx := deps.getModuleIdxFor? n then
          hidden := hidden.push (depth, deps.header.moduleNames[idx.toNat]!, n)
    for m in used do todo := (m, depth + 1) :: todo
  for (depth, mod, n) in hidden.qsort (fun a b => a.1 < b.1) do
    IO.println s!"HIDDEN depth={depth} {mod} {n}"
  IO.println s!"AUDIT reachable={seen.size} hidden_definitions={hidden.size}"

/-- Follow actual proof and opaque-definition bodies, rejecting unexpected axioms. -/
def auditAxioms (own : Array ConstantInfo) (deps : Environment) : IO Unit := do
  let ownMap := own.foldl (fun m ci => m.insert ci.name ci)
    ({} : Std.HashMap Name ConstantInfo)
  let mut todo := own.toList.map (·.name)
  let mut seen : NameSet := {}
  let mut axioms : NameSet := {}
  while !todo.isEmpty do
    let n := todo.head!
    todo := todo.tail!
    if seen.contains n then continue
    seen := seen.insert n
    let some ci := ownMap[n]? <|> deps.find? n
      | throw <| IO.userError s!"unavailable dependency {n}"
    if ci matches .axiomInfo _ then axioms := axioms.insert n
    for m in ci.getUsedConstantsAsSet do todo := m :: todo
  for n in axioms do IO.println s!"AXIOM {n}"
  for n in axioms do
    unless n == ``propext || n == ``Classical.choice || n == ``Quot.sound do
      throw <| IO.userError s!"unexpected axiom {n}"
  IO.println s!"AXIOM_AUDIT_PASS {seen.size} declarations"

def main (args : List String) : IO Unit := do
  initSearchPath (← findSysroot)
  let mod := (args[0]?.getD
    "WeilConjectures.AlgebraicGeometry.EtaleBaseChangeRestrictScalars").toName
  let mode := args[1]?.getD "private"
  let start ← IO.monoMsNow
  let path ← match ← IO.getEnv "CL953_OLEAN" with
    | some path => pure (System.FilePath.mk path)
    | none => findOLean mod
  let parts ← readModuleDataParts #[path, OLeanLevel.server.adjustFileName path,
    OLeanLevel.private.adjustFileName path]
  let some (data, _) := parts.back? | throw <| IO.userError "missing private module data"
  IO.println s!"LOADED {mod}: {data.constants.size} own constants {(← IO.monoMsNow) - start} ms"
  (← IO.getStdout).flush
  let extra : Array Import := (args.drop 2).toArray.map fun s =>
    { module := s.toName, importAll := true }
  let mut arts : NameMap ImportArtifacts := {}
  if let some replacement := ← IO.getEnv "CL953_REPLACE_OLEAN" then
    let some modName := ← IO.getEnv "CL953_REPLACE_MODULE"
      | throw <| IO.userError "CL953_REPLACE_OLEAN requires CL953_REPLACE_MODULE"
    let path := System.FilePath.mk replacement
    arts := arts.insert modName.toName <| .ofArrays #[
      #[path, OLeanLevel.server.adjustFileName path, OLeanLevel.private.adjustFileName path],
      #[path.withExtension "ir.sig", path.withExtension "ir"]]
    IO.println s!"REPLACE {modName} {path}"
    (← IO.getStdout).flush
  if let some manifest := ← IO.getEnv "CL953_EXTRA_ARTIFACTS" then
    for line in (← IO.FS.readFile manifest).splitOn "\n" do
      if line.isEmpty then continue
      let [modName, filename] := line.splitOn "\t"
        | throw <| IO.userError "expected MODULE<TAB>OLEAN in artifact manifest"
      let path := System.FilePath.mk filename
      arts := arts.insert modName.toName <| .ofArrays #[
        #[path, OLeanLevel.server.adjustFileName path, OLeanLevel.private.adjustFileName path],
        #[path.withExtension "ir.sig", path.withExtension "ir"]]
      IO.println s!"EXTRA_ARTIFACT {modName} {path}"
    (← IO.getStdout).flush
  -- Imports live until process exit; avoid traversing them for reference-count updates.
  let deps ← importModules (data.imports ++ extra) {} 0 (leakEnv := true)
    (level := if mode == "exported" || mode.startsWith "mixed" then .exported else .private)
    (arts := arts)
  if mode == "axioms" then
    auditAxioms data.constants deps
    return
  if mode == "audit" then
    auditVisibility data.constants deps data.imports arts
    return
  let base ← if mode == "fresh" then mkEmptyEnvironment else pure deps
  let mut constants : Std.HashMap Name ConstantInfo := {}
  if mode == "fresh" then
    for (n, ci) in deps.constants.toList do constants := constants.insert n ci
  for ci in data.constants do
    let ci := if mode == "normalize" || mode == "lets" || mode == "mdata" then
      normalizeConstant mode ci else ci
    constants := constants.insert ci.name ci
  IO.println s!"REPLAY mode={mode} constants={constants.size} dependency_modules={base.header.moduleNames.size}"
  (← IO.getStdout).flush
  ComparatorRepro.run constants base (typeFirst := mode == "type-first" || mode == "mixed-types")
