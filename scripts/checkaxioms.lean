/-
`checkaxioms` — the companion to `lake exe checkdecls`.

`checkdecls` answers *"does the declaration named by a blueprint `\lean{...}` field
exist?"*. It cannot answer *"is it proved?"*: a blueprint statement carrying
`\leanok` whose Lean declaration is closed by `sorry` passes `checkdecls` and is
still a false claim of formalisation. `lakefile.toml` sets `warn.sorry = false`,
so `lake build` is silent about it too.

This tool answers the second question. For every name in the input file that
exists, it reports whether the declaration's axiom set contains `sorryAx`.

    lake exe checkaxioms [--list-missing] <file-with-one-declaration-name-per-line>

The input format is the one `checkdecls` takes, so both tools can be run against
the same `blueprint/lean_decls` (written by `leanblueprint web`).

Names that do **not** exist are counted but do **not** fail the run, and are
listed only under `--list-missing`: existence is `checkdecls`' question, and
keeping the two apart is what lets this check be switched on while blueprint
references are still being repaired. Exit code is 0 iff no listed declaration is
`sorry`-backed.

Taint is read with `Lean.collectAxioms`, which consults the axiom set recorded in
the `.olean`. Do not reimplement it by walking `Expr.getUsedConstants` from an
importing module: under the module system the values of imported declarations
that are not `@[expose]` are absent from the environment, so such a walk silently
sees the type closure only. Measured on this repository, that mistake reports 7
of the 8 `sorry`-backed declarations on master as clean — every one that is a
theorem rather than a `def`.
-/
import Lake.CLI.Main

open Lake Lean

unsafe def main (args : List String) : IO UInt32 := do
  let (listMissing, rest) :=
    match args with
    | "--list-missing" :: rest => (true, rest)
    | rest => (false, rest)
  let [arg] := rest
    | println! "usage: checkaxioms [--list-missing] <file-with-one-declaration-name-per-line>"
      return 1
  let filename : System.FilePath := arg
  unless ← filename.pathExists do
    println! "Could not find declaration list {filename}."
    return 1
  -- Discover the `lean_lib` roots from `lakefile.toml`, exactly as `checkdecls`
  -- does, so that adding a library does not silently drop it from the check.
  let (elanInstall?, leanInstall?, lakeInstall?) ← findInstall?
  let config ← MonadError.runEIO <| mkLoadConfig { elanInstall?, leanInstall?, lakeInstall? }
  let (ws?, log) ← (loadWorkspace config).run?
  log.replay (logger := .stderr)
  let some ws := ws? | return 1
  let imports := ws.root.leanLibs.flatMap (·.config.roots.map fun module => { module })
  -- see comments in https://github.com/leanprover/lean4/pull/6325
  enableInitializersExecution
  let env ← importModules imports {}
  -- Keep the line as written next to the parsed name: a blueprint field that is
  -- not a legal Lean identifier parses to `Name.anonymous`, and reporting that
  -- back tells the reader nothing about which field is at fault.
  let entries := (← IO.FS.lines filename).filterMap fun line =>
    let line := line.trimAscii.toString
    if line.isEmpty then none else some (line, line.toName)
  let check : CoreM (Nat × Nat × Nat) := do
    let mut proved := 0
    let mut sorried := 0
    let mut missing := 0
    for (line, n) in entries do
      if !(← getEnv).contains n then
        if listMissing then println! "{line} is missing."
        missing := missing + 1
      else if (← collectAxioms n).contains ``sorryAx then
        println! "{line} is sorry-backed."
        sorried := sorried + 1
      else
        proved := proved + 1
    return (proved, sorried, missing)
  let ((proved, sorried, missing), _) ←
    check.toIO { fileName := "<checkaxioms>", fileMap := default } { env }
  println! "checkaxioms: {proved} proved, {sorried} sorry-backed, \
    {missing} missing (missing names are `checkdecls`' job and do not fail this check)."
  return if sorried == 0 then 0 else 1
