import Lean
/-! Names declared by two modules of the library, read from the compiled files (every part of a module); nothing is
elaborated. Run by `tools/name_clashes.sh`, which names the file listing the modules in `SHEAF_CLASH_MODULES`.
A file that is not of Lean's module system and imports two modules declaring one name with different types or
universe parameters, or two definitions, fails with "environment already contains": `tools/target_types.sh`, the
comparator and `lean/Challenge.lean` import the whole closure of the targets that way. Two theorems with the same name,
type and universe parameters are accepted by Lean (helper lemmas such as `congr_simp` generated on demand). -/
open Lean in
#eval show IO Unit from do
  let lib : System.FilePath := ".lake/build/lib/lean"
  let some list ← IO.getEnv "SHEAF_CLASH_MODULES" | throw <| IO.userError "set SHEAF_CLASH_MODULES"
  let mods := (← IO.FS.lines list).filter (· ≠ "")
  let mut seen : Std.HashMap Name (Array (String × String × UInt64 × List Name)) := {}
  for m in mods do
    let base := lib / (m.replace "." "/")
    let mut parts : Array System.FilePath := #[]
    for ext in ["olean", "olean.server", "olean.private"] do
      let p : System.FilePath := ⟨base.toString ++ "." ++ ext⟩
      if ← p.pathExists then parts := parts.push p
    if parts.isEmpty then
      IO.println s!"NOOLEAN {m}"
      continue
    let data ← readModuleDataParts parts
    let mut mine : Std.HashMap Name (String × UInt64 × List Name) := {}
    for (d, _) in data do
      for c in d.constants do
        let kind := match c with
          | .thmInfo _ => "thm" | .axiomInfo _ => "ax" | .defnInfo _ => "def" | .opaqueInfo _ => "opaque"
          | .inductInfo _ => "ind" | .ctorInfo _ => "ctor" | .recInfo _ => "rec" | .quotInfo _ => "quot"
        -- the fullest record of the module wins over the stub of its public part
        match mine[c.name]? with
        | some (k, _, _) => if k == "ax" then mine := mine.insert c.name (kind, hash c.type, c.levelParams)
        | none => mine := mine.insert c.name (kind, hash c.type, c.levelParams)
    for (n, (k, h, ls)) in mine do
      seen := seen.insert n ((seen.getD n #[]).push (m, k, h, ls))
  for (n, ms) in seen do
    if ms.size > 1 then
      let (_, k0, h0, l0) := ms[0]!
      let same := ms.all fun (_, k, h, l) => h == h0 && l == l0 && k == k0
      let tag := if same && k0 == "thm" then "SAME-THM" else if same then s!"SAME-{k0}" else "DIFFERENT"
      IO.println s!"CLASH {tag} {n} {ms.map (·.1)} {ms.map (·.2.1)}"
