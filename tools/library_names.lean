/-
Every non-internal declaration of the libraries the project imports (Mathlib, Lean core, Std, Batteries, ...):
name, module and kind, one tab-separated line each, written to the file named by LIBRARY_NAMES_OUT.
Run inside a checkout of the Lean project:  LIBRARY_NAMES_OUT=out.tsv lake env lean library_names.lean
Project declarations (roots WeilConjectures and Weil) are left out: the sorry map has them.
-/
import WeilConjectures
open Lean Meta

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
  let out ← IO.getEnv "LIBRARY_NAMES_OUT"
  let h ← IO.FS.Handle.mk (out.getD "library_names.tsv") .write
  let mut count := 0
  for (n, ci) in env.constants.map₁.toList do
    if n.isInternalDetail then continue
    let some i := env.getModuleIdxFor? n | continue
    let m := env.header.moduleNames[i.toNat]!
    if m.getRoot == `WeilConjectures || m.getRoot == `Weil then continue
    h.putStrLn s!"{n}\t{m}\t{kindOf env n ci}"
    count := count + 1
  IO.println s!"{count} library declarations"
