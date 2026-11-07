/-
Copyright (c) 2023 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Lean

/-!
# Per-declaration kernel type-checking times

Usage, in a project tree that is already built (this never builds anything):

```
lake env lean --run scripts/tech_debt/KernelTimes.lean [--threshold-ms N] [--level exported|private] MODULE...
```

For each module, its imports are loaded from their `.olean` files, and then the module's own
declarations (read from its `.olean`, `.olean.server` and `.olean.private` parts) are sent
through the kernel again, one at a time and in dependency order, as `Lean.Environment.replay`
(Lean 4.33.1, `Lean/Replay.lean`) does. Every kernel call is timed; nothing is elaborated, and
no project code runs (`importModules` with `loadExts := false` runs no `initialize`).

`--level exported` (the default) imports the dependencies as the build does under the module
system; `--level private` imports all dependency bodies, as the comparator does (see
`scripts/comparator_repro` on `sheaf/replay-harness`, from which this is adapted).

Output, one tab-separated line per item, on stdout:

* `DECL <ms> <module> <name>` for every kernel call taking at least the threshold (default 1000 ms);
* `MODULE <module> <kernel ms> <declarations> <import ms>` once the module is done;
* `ERROR <module> <message>` if a module could not be replayed (the others still are).
-/
open Lean

namespace KernelTimes

structure Context where
  newConstants : Std.HashMap Name ConstantInfo
  module : Name
  thresholdNs : Nat

structure State where
  env : Kernel.Environment
  remaining : NameSet := {}
  pending : NameSet := {}
  postponedConstructors : NameSet := {}
  postponedRecursors : NameSet := {}
  totalNs : Nat := 0
  count : Nat := 0

abbrev M := ReaderT Context <| StateRefT State IO

def isTodo (name : Name) : M Bool := do
  let r := (← get).remaining
  if r.contains name then
    modify fun s => { s with remaining := s.remaining.erase name, pending := s.pending.insert name }
    return true
  else
    return false

/-- Add a declaration through the kernel, timing the call. -/
def addDecl (d : Declaration) : M Unit := do
  let start ← IO.monoNanosNow
  match (← get).env.addDeclCore 0 0 d (cancelTk? := none) with
  | .ok env => modify fun s => { s with env }
  | .error ex => throw <| .userError <| (← ex.toMessageData {} |>.toString)
  let elapsed := (← IO.monoNanosNow) - start
  modify fun s => { s with totalNs := s.totalNs + elapsed, count := s.count + 1 }
  if elapsed ≥ (← read).thresholdNs then
    let names := ", ".intercalate (d.getTopLevelNames.map toString)
    IO.println s!"DECL\t{elapsed / 1000000}\t{(← read).module}\t{names}"

mutual
partial def replayConstant (name : Name) : M Unit := do
  if ← isTodo name then
    let some ci := (← read).newConstants[name]? | unreachable!
    replayConstants ci.getUsedConstantsAsSet
    if (← get).pending.contains name then
      try
        match ci with
        | .defnInfo info => addDecl (.defnDecl info)
        | .thmInfo info =>
          -- Duplicate private theorems (see `Lean/Replay.lean`).
          if let some (.thmInfo info') := (← get).env.find? ci.name then
            if info.name == info'.name && info.type == info'.type &&
                info.levelParams == info'.levelParams && info.all == info'.all then
              return
          addDecl (.thmDecl info)
        | .axiomInfo info => addDecl (.axiomDecl info)
        | .opaqueInfo info => addDecl (.opaqueDecl info)
        | .inductInfo info =>
          let all ← info.all.mapM fun n => do pure ((← read).newConstants[n]!)
          for o in all do
            modify fun s =>
              { s with remaining := s.remaining.erase o.name, pending := s.pending.erase o.name }
          let ctorInfo ← all.mapM fun ci => do
            pure (ci, ← ci.inductiveVal!.ctors.mapM fun n => do pure ((← read).newConstants[n]!))
          for (_, ctors) in ctorInfo do
            for ctor in ctors do
              replayConstants ctor.getUsedConstantsAsSet
          let types : List InductiveType := ctorInfo.map fun ⟨ci, ctors⟩ =>
            { name := ci.name, type := ci.type
              ctors := ctors.map fun ci => { name := ci.name, type := ci.type } }
          addDecl (.inductDecl info.levelParams info.numParams types false)
        | .ctorInfo info =>
          modify fun s => { s with postponedConstructors := s.postponedConstructors.insert info.name }
        | .recInfo info =>
          modify fun s => { s with postponedRecursors := s.postponedRecursors.insert info.name }
        | .quotInfo _ =>
          replayConstant `Eq
          addDecl .quotDecl
        modify fun s => { s with pending := s.pending.erase name }
      catch ex =>
        throw <| .userError s!"while replaying declaration '{name}': {ex}"

partial def replayConstants (names : NameSet) : M Unit := do
  for n in names do replayConstant n
end

def checkPostponed : M Unit := do
  for c in (← get).postponedConstructors do
    match (← get).env.find? c, (← read).newConstants[c]? with
    | some (.ctorInfo i), some (.ctorInfo i') =>
      unless i == i' do throw <| IO.userError s!"Invalid constructor {c}"
    | _, _ => throw <| IO.userError s!"No such constructor {c}"
  for r in (← get).postponedRecursors do
    match (← get).env.find? r, (← read).newConstants[r]? with
    | some (.recInfo i), some (.recInfo i') =>
      unless i == i' do throw <| IO.userError s!"Invalid recursor {r}"
    | _, _ => throw <| IO.userError s!"No such recursor {r}"

/-- Replay one module's own declarations on top of its imports. -/
def measureModule (mod : Name) (level : OLeanLevel) (thresholdNs : Nat) : IO Unit := do
  let start ← IO.monoNanosNow
  let path ← findOLean mod
  let parts ← readModuleDataParts #[path, OLeanLevel.server.adjustFileName path,
    OLeanLevel.private.adjustFileName path]
  let some (data, _) := parts.back? | throw <| IO.userError "missing module data"
  -- `leakEnv`: the imports are never freed, which saves traversing them at the end; the
  -- driver runs few modules per process.
  let deps ← importModules data.imports {} 0 (leakEnv := true) (level := level)
  let importNs := (← IO.monoNanosNow) - start
  let mut newConstants : Std.HashMap Name ConstantInfo := {}
  let mut remaining : NameSet := {}
  for ci in data.constants do
    newConstants := newConstants.insert ci.name ci
    if !ci.isUnsafe && !ci.isPartial then remaining := remaining.insert ci.name
  let (_, s) ← StateRefT'.run (s := { env := deps.toKernelEnv, remaining }) do
    ReaderT.run (r := { newConstants, module := mod, thresholdNs }) do
      for n in remaining do replayConstant n
      checkPostponed
  IO.println s!"MODULE\t{mod}\t{s.totalNs / 1000000}\t{s.count}\t{importNs / 1000000}"

end KernelTimes

def main (args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  let mut thresholdMs := 1000
  let mut level := OLeanLevel.exported
  let mut mods : Array Name := #[]
  let mut rest := args
  while !rest.isEmpty do
    match rest with
    | "--threshold-ms" :: n :: r =>
      thresholdMs := n.toNat!
      rest := r
    | "--level" :: "exported" :: r => level := .exported; rest := r
    | "--level" :: "private" :: r => level := .private; rest := r
    | m :: r => mods := mods.push m.toName; rest := r
    | [] => rest := []
  let mut failed := false
  for mod in mods do
    try
      KernelTimes.measureModule mod level (thresholdMs * 1000000)
    catch e =>
      IO.println s!"ERROR\t{mod}\t{(toString e).replace "\n" " "}"
      failed := true
    (← IO.getStdout).flush
  return if failed then 1 else 0
