## What changed

Repaired the returned delivery by removing the two private declarations
`diagonalMap_proj₁` and `diagonalMap_proj₂`, which duplicated statements already present in
`Sheaf.AlgebraicGeometry.DualNumbersDiagonal`. Their fully proved arguments now appear as
local facts inside `infDerivation_diagonal_coefficients`, where they are used to construct and
verify the diagonal. The target signature and all public interfaces are unchanged.

## Proved and sorry left

Closed the original hole `AlgebraicGeometry.GrpObj.infDerivation_diagonal_coefficients`.
No `sorry` remains in this module, and no new holes or modules were added.

## No longer needed

The duplicate private declarations `diagonalMap_proj₁` and `diagonalMap_proj₂` are no longer
module declarations; their local proofs are needed by the target proof. No imports or DAG
nodes were otherwise pruned.

## Where the brief, the DAG or earlier work was wrong

The earlier delivery exported private theorem declarations whose statements duplicated
existing declarations in `Sheaf.AlgebraicGeometry.DualNumbersDiagonal`, triggering the import
prune check. Since those declarations are private and cannot be imported by name, the repair
keeps their proofs local to the target theorem and avoids duplicate declarations.

## Second reading by F2

1. Compared the delivered module with the repository version. The target declaration and all
existing public signatures are unchanged; only the target proof and private local proof terms
differ. Verdict: pass.
2. Compiled the module with `lcompile.py`; it succeeds with no errors, and the module contains
no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by`. Verdict: pass.
3. Searched the library for the helper statements and confirmed the removed helpers duplicated
existing diagonal projection facts; no new split-off statement or node was added. Verdict: pass.
4. Checked the proof route from the target downward: it uses the existing dual-number diagonal
construction and derives the coefficient identity sectionwise, with no unnecessary imports or
new declarations. Verdict: pass.
5. Checked the target node's statement and route against the Lean declaration. The statement is
unchanged and the unit route remains realized through the existing diagonal construction.
Verdict: pass.

Changed: moved the duplicate projection and coefficient arguments into local facts inside the
target proof, preserving the public interface and eliminating duplicate private declarations.
