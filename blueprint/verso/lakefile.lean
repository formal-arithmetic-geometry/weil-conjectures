import Lake
open Lake DSL

/-!
Verso Blueprint for Nagata's compactification theorem.

This is a package of its own so that the main `weil-conjectures` build is not made to depend
on Verso. It requires the project by path, so that the `(lean := "...")` attachments of the
Blueprint nodes resolve against the actual declarations of `WeilConjectures`.

See `README.md` in this directory for the two possible wirings and their trade-offs.
-/

require VersoBlueprint from git "https://github.com/leanprover/verso-blueprint" @ "v4.33.0"
require «weil-conjectures» from ".." / ".."

package NagataBlueprint where
  precompileModules := false
  leanOptions := #[⟨`experimental.module, true⟩]

@[default_target]
lean_lib NagataBlueprint where

@[default_target]
lean_exe «nagata-blueprint» where
  root := `NagataBlueprintMain
  supportInterpreter := true
