/-
The sorry route of target declarations (launcher, 2026-10-16): the modules of the project declarations whose own term
contains `sorry` and that the targets' proofs actually use (transitively, through types and values). Stage 3 is
top-down: only these modules are work; a sorry in a module the targets import but do not use is not a task.
`stops` (the human, 2026-10-17: the declarations the batch assumes, coord/assumed.tsv) are axioms: the walk
neither enters nor reports them.

2026-10-20 (b69): the walk no longer imports the target into an environment. Since the upstream sync the project holds
twin modules (Sheaf.X and WeilConjectures.X declaring the same names); each is reached only through private imports, so
the module build never sees both, but a plain file importing a target loads the whole closure and Lean refused it
("environment already contains 'SheafOfModules.IsFlat'"), so every walk failed from 2026-10-19 17:24. A `module`
scratch file avoids that but sees no proof bodies below the target. The walk now reads the project modules' compiled
data directly (`.olean`, and for module-system files the complete `.olean.private` part), without an environment:
a constant name is resolved to the module that declares it, and where twins declare the same name, to the one in the
import closure of the module whose declaration uses it. Mathlib and core are not read (the walk never entered them).
tools/sorry_route.py writes a scratch file `import Lean` + this file's body + one `#eval SorryRoute.run ...`.
-/
import Lean
open Lean

namespace SorryRoute

def isProject (m : Name) : Bool := m.getRoot == `Sheaf || m.getRoot == `WeilConjectures

/-- The complete compiled data of a module: the `.olean` of a plain file, the `.olean.private` part of a module-system
file (each part includes the previous ones). -/
def readFull (mod : Name) : IO ModuleData := do
  let f ← findOLean mod
  let some (main, _) := (← readModuleDataParts #[f])[0]? | throw <| IO.userError s!"cannot read {f}"
  if !main.isModule then return main
  try
    let parts ← readModuleDataParts #[f, OLeanLevel.server.adjustFileName f, OLeanLevel.private.adjustFileName f]
    let some (full, _) := parts.back? | return main
    return full
  catch e =>
    IO.println s!"WARN {mod}: no private part ({e}); only its exported data is read"
    return main

def closureOf (imports : Std.HashMap Name (Array Name)) (m : Name) : NameSet := Id.run do
  let mut seen : NameSet := {}
  let mut todo := #[m]
  while h : todo.size > 0 do
    let x := todo.back
    todo := todo.pop
    if seen.contains x then continue
    seen := seen.insert x
    for i in imports.getD x #[] do
      todo := todo.push i
  return seen

/-- Prints `TARGETDECLS n`, `STOPDECLS k n` (with stop modules), then `ROUTE module declaration` for every sorried
project declaration the declarations of `targetMods` use, not entering `stops` nor any declaration of `stopMods`. -/
def run (targetMods : Array Name) (stops : Array Name := #[]) (stopMods : Array Name := #[]) : IO Unit := do
  if (← searchPathRef.get).isEmpty then initSearchPath (← findSysroot)
  -- load the project part of the import closure
  let mut imports : Std.HashMap Name (Array Name) := {}
  let mut decls : Std.HashMap Name (Array Name) := {}
  let mut owners : Std.HashMap Name (Array (Name × ConstantInfo)) := {}
  let mut todo := targetMods
  while h : todo.size > 0 do
    let m := todo.back
    todo := todo.pop
    if imports.contains m then continue
    let md ← readFull m
    let imps := (md.imports.map (·.module)).filter isProject
    imports := imports.insert m imps
    decls := decls.insert m md.constNames
    for ci in md.constants do
      owners := owners.alter ci.name fun o => some ((o.getD #[]).push (m, ci))
    for i in imps do
      unless imports.contains i do todo := todo.push i
  let mut targets : Array (Name × Name) := #[]
  for m in targetMods do
    for n in decls.getD m #[] do
      unless n.isInternalDetail do targets := targets.push (m, n)
  IO.println s!"TARGETDECLS {targets.size}"
  let stopSet : NameSet := stops.foldl (fun s n => s.insert n) {}
  let mut stopModSet : NameSet := {}
  unless stopMods.isEmpty do
    let loaded := stopMods.filter imports.contains
    stopModSet := loaded.foldl (fun s n => s.insert n) {}
    IO.println s!"STOPDECLS {loaded.size} {loaded.foldl (fun k m => k + (decls.getD m #[]).size) 0}"
  -- the walk; a visited declaration is (module, name), so twins are distinct
  let mut seen : Std.HashSet (Name × Name) := {}
  let mut cache : Std.HashMap Name NameSet := {}
  let mut stack := targets
  let mut out : Array (Name × Name) := #[]
  while h : stack.size > 0 do
    let (ctx, n) := stack.back
    stack := stack.pop
    if stopSet.contains n then continue
    let some cands := owners[n]? | continue
    let mut pick := cands[0]!
    if cands.size > 1 then
      let cl := match cache[ctx]? with
        | some s => s
        | none => closureOf imports ctx
      cache := cache.insert ctx cl
      if let some c := cands.find? (fun (m, _) => cl.contains m) then pick := c
    let (m, ci) := pick
    if stopModSet.contains m || seen.contains (m, n) then continue
    seen := seen.insert (m, n)
    let tc := ci.type.getUsedConstants
    let vc := match ci.value? (allowOpaque := true) with | some v => v.getUsedConstants | none => #[]
    if vc.contains ``sorryAx || tc.contains ``sorryAx then out := out.push (n, m)
    for c in tc ++ vc do
      if owners.contains c then stack := stack.push (m, c)
  for (d, m) in out do
    IO.println s!"ROUTE {m} {d}"

end SorryRoute
