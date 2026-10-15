/-
For every declaration of the project: where it is, whether its own term contains `sorry`, and which
project declarations it uses. One JSON object per line, written to the file named by SORRY_MAP_OUT.
Run inside a checkout of the Lean project:  SORRY_MAP_OUT=out.jsonl lake env lean sorry_map.lean
Auxiliary declarations (`_proof_1`, matchers, equation lemmas) are reported with their owner in `o`.
-/
import WeilConjectures
open Lean Meta

partial def ownerOf (env : Environment) (n : Name) : Name :=
  if n.isInternalDetail then
    match n with
    | .str p _ | .num p _ => if p.isAnonymous then n else ownerOf env p
    | .anonymous => n
  else n

def kindOf (env : Environment) (n : Name) : ConstantInfo → String
  | .thmInfo _ => "theorem"
  | .defnInfo _ => if isInstanceCore env n then "instance" else "def"
  | .axiomInfo _ => "axiom"
  | .opaqueInfo _ => "opaque"
  | .inductInfo _ => if isStructure env n then "structure" else "inductive"
  | .ctorInfo _ => "ctor"
  | .recInfo _ => "rec"
  | .quotInfo _ => "quot"

#eval show MetaM Unit from do
  let env ← getEnv
  let out ← IO.getEnv "SORRY_MAP_OUT"
  let h ← IO.FS.Handle.mk (out.getD "sorry_map.jsonl") .write
  let inProj (n : Name) : Option Name := do
    let i ← env.getModuleIdxFor? n
    let m := env.header.moduleNames[i.toNat]!
    if m.getRoot == `WeilConjectures then some m else none
  let mut count := 0
  for (n, ci) in env.constants.map₁.toList do
    let some m := inProj n | continue
    let tc := ci.type.getUsedConstants
    let vc := match ci.value? (allowOpaque := true) with | some v => v.getUsedConstants | none => #[]
    let deps := (tc ++ vc).filter (fun c => c != n && (inProj c).isSome) |>.toList.eraseDups
    let r ← findDeclarationRanges? n
    let (l1, l2) := match r with | some r => (r.range.pos.line, r.range.endPos.line) | none => (0, 0)
    let o := ownerOf env n
    let o := if env.contains o then o else n
    let j := Json.mkObj [("n", toString n), ("o", toString o), ("k", kindOf env n ci), ("m", toString m),
      ("l1", l1), ("l2", l2), ("s", vc.contains ``sorryAx), ("ts", tc.contains ``sorryAx),
      ("d", Json.arr (deps.map (fun d => Json.str (toString d))).toArray)]
    h.putStrLn j.compress
    count := count + 1
  IO.println s!"{count} declarations"
