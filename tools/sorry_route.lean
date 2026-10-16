/-
The sorry route of target declarations (launcher, 2026-10-16): the modules of the project declarations whose own term
contains `sorry` and that the targets' proofs actually use (transitively, through types and values). Stage 3 is
top-down: only these modules are work; a sorry in a module the targets import but do not use is not a task.
Run: SORRY_ROUTE_TARGETS="A.b C.d" SORRY_ROUTE_OUT=out.txt  with this file's imports replaced by the targets' modules
(tools/sorry_route.py writes and compiles it per target module through tools/lean_file.sh).
-/
import Lean
open Lean Meta

def sorryRoute (targets : List Name) : MetaM (Array (Name × Name)) := do
  let env ← getEnv
  let mods := env.header.moduleNames
  let modOf (n : Name) : Option Name := do
    let i ← env.getModuleIdxFor? n; mods[i.toNat]?
  let mut seen : NameSet := {}
  let mut stack := targets.toArray
  let mut out : Array (Name × Name) := #[]
  while h : stack.size > 0 do
    let n := stack.back
    stack := stack.pop
    if seen.contains n then continue
    seen := seen.insert n
    let some ci := env.find? n | continue
    let some m := modOf n | continue
    let root := m.getRoot
    if root != `Sheaf && root != `WeilConjectures then continue
    let tc := ci.type.getUsedConstants
    let vc := match ci.value? (allowOpaque := true) with | some v => v.getUsedConstants | none => #[]
    if vc.contains ``sorryAx || tc.contains ``sorryAx then out := out.push (n, m)
    for c in tc ++ vc do
      unless seen.contains c do stack := stack.push c
  return out
