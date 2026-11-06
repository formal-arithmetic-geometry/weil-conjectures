import WeilConjectures.LeanEval.WeilConjectures

/-!
# Kernel time of the declarations found by `scripts/instance_mix_sweep.lean`

Reads the names listed in `scripts/instance_mix_sweep.txt` and re-checks each declaration in
the kernel under a fresh name, recording the wall-clock time and whether the check finished.
A check is interrupted after `timeLimitMs`. With `INSTANCE_MIX_UNFOLD=1`, every occurrence of
the shortcut `ModuleCat.isGrothendieckAbelian_of_commRing R _` is first replaced by its value,
so that only Mathlib's `instIsGrothendieckAbelianModuleCat` remains: a large drop of the time
means that the cost comes from identifying the two instances.

Not imported by the library. Run from the repository root with
`INSTANCE_MIX_SHARD=i/k lake lean scripts/instance_mix_kernel_time.lean`, which checks every
`k`-th declaration starting from the `i`-th one and writes `scripts/instance_mix_kernel_time.i-k.txt`
(or `instance_mix_kernel_time_unfolded.i-k.txt`). The names can also be given in a file
`INSTANCE_MIX_NAMES`, one per line.
-/

open Lean

namespace InstanceMixSweep

/-- Wall-clock limit of one kernel check. -/
def timeLimitMs : UInt32 := 120000

def shortcut : Name := `ModuleCat.isGrothendieckAbelian_of_commRing

/-- Parse a printed name, reading numeric components (as in private names) as numbers. -/
def parseName (s : String) : Name :=
  (s.splitOn ".").foldl (fun n c => match c.toNat? with
    | some k => .num n k
    | none => .str n c) .anonymous

/-- Replace the shortcut instance by its value. -/
def unfoldShortcut (env : Environment) (e : Expr) : Expr :=
  match env.find? shortcut with
  | none => e
  | some ci => e.replace fun s => match s.getAppFn with
    | .const n ls =>
      if n == shortcut then
        (ci.value? (allowOpaque := true)).map fun v =>
          let v := (v.instantiateLevelParams ci.levelParams ls).beta s.getAppArgs
          -- the value is `inferInstance _ (instIsGrothendieckAbelianModuleCat R _)`
          if v.isAppOf ``inferInstance then v.appArg! else v
      else none
    | _ => none

def recheck (unfold : Bool) (n : Name) : CoreM String := do
  let env ← getEnv
  let some ci := env.find? n | return "missing"
  let f := if unfold then unfoldShortcut env else id
  let n' := `_instanceMixRecheck ++ n
  let decl : Declaration ← match ci with
    | .thmInfo v => pure <| .thmDecl { v with name := n', type := f v.type, value := f v.value }
    | .defnInfo v => pure <| .defnDecl { v with
        name := n', type := f v.type, value := f v.value, safety := .safe }
    | _ => return "skipped (not a theorem/definition)"
  let tk ← IO.CancelToken.new
  let _ ← IO.asTask do IO.sleep timeLimitMs; tk.set
  let t0 ← IO.monoMsNow
  let r := Environment.addDeclCore env 0 512 decl (some tk)
  let res := match r with
    | .ok _ => "ok"
    | .error .interrupted => "INTERRUPTED"
    | .error _ => "error"
  -- `res` depends on `r`, so the kernel check is done before the clock is read again
  let t1 ← if res.length > 0 then IO.monoMsNow else pure 0
  let msg ← match r with
    | .error .interrupted => pure ""
    | .error e => pure s!" ({(← (e.toMessageData {}).toString).take 300})"
    | .ok _ => pure ""
  return s!"{t1 - t0} ms | {res}{msg}"

def runKernelTimes : CoreM Unit := do
  let shard := ((← IO.getEnv "INSTANCE_MIX_SHARD").getD "0/1").splitOn "/"
  let i := shard[0]!.toNat!
  let k := shard[1]!.toNat!
  let unfold := (← IO.getEnv "INSTANCE_MIX_UNFOLD") == some "1"
  let names ← match ← IO.getEnv "INSTANCE_MIX_NAMES" with
    | some file => pure ((← IO.FS.lines file).toList.filter (· ≠ "")).toArray
    | none => do
      let lines ← IO.FS.lines "scripts/instance_mix_sweep.txt"
      pure <| (lines.drop 3).filterMap fun l => (l.splitOn " | ").head?
  let out := if unfold then "instance_mix_kernel_time_unfolded" else "instance_mix_kernel_time"
  -- `INSTANCE_MIX_START=m` skips the first `m` names and appends to the output, to resume a run
  let start := ((← IO.getEnv "INSTANCE_MIX_START").bind String.toNat?).getD 0
  let h ← IO.FS.Handle.mk s!"scripts/{out}.{i}-{k}.txt" (if start = 0 then .write else .append)
  for s in names, j in [0:names.size] do
    unless j % k == i && start ≤ j do continue
    h.putStrLn s!"{s} | {← recheck unfold (parseName s)}"
    h.flush

end InstanceMixSweep

#eval InstanceMixSweep.runKernelTimes
