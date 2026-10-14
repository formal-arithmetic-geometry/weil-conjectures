## What changed
Added `StandardSingleBaseChangeTopRestrictionAux` with two intermediate public theorems splitting the source isomorphism existence from the compatibility equation. The target theorem is proved by applying these two declarations.

## Proved and sorry left
The target `AlgebraicGeometry.standardSingleBaseChange_topRestriction_comparison` is proved. The auxiliary declarations `standardSingleBaseChange_topRestriction_source` and `standardSingleBaseChange_topRestriction_compatibility` remain `sorry`, with nodes listed under `## New nodes`.

## No longer needed
None; the target's existing import was retained.

## Where the brief, the DAG or earlier work was wrong
The planned two-step derived mate argument is not yet available as executable Lean glue, so it was split into source-isomorphism and compatibility intermediate statements.

## New nodes
`lem-pc-standard-single-base-change-top-restriction-source` and `lem-pc-standard-single-base-change-top-restriction-compatibility`.

## Earlier second reading (a previous round; superseded)
The target proof compiles unchanged against the two auxiliary declarations. The auxiliary statements are strict decomposition steps: one supplies the source isomorphism and the other supplies the target isomorphism and compatibility equation.

## Second reading by A3

1. Compared the delivered item module with the repository version. The existing target signature and all preceding declarations are byte-for-byte unchanged; only its proof and the added proof-only import differ. Verdict: pass.
2. Compiled both sandbox modules with `lcompile.py --all`; compilation succeeds. The target has no `sorry`; the two explicitly named auxiliary theorem holes remain and are recorded by nodes. No forbidden declarations or hollow definitions were introduced. Verdict: pass.
3. Checked the split statements against the target. The source theorem supplies only the missing source isomorphism, and the compatibility theorem is universally quantified over that isomorphism and supplies only the target isomorphism and factorization equation. The source statement now exactly matches its node and has no redundant `True`. Verdict: pass.
4. The target proof uses the two auxiliary declarations directly; no shorter proved declaration was found in the local library search. The item import remains proof-only, and no old proof dependency is removed. Verdict: pass.
5. The DAG records match the Lean declarations, including proof origins, node statements, and the three search records with verdicts. The unit route remains represented by the original target node and its two strictly simpler split nodes. Verdict: pass.

Changed the source auxiliary statement to remove the redundant `True`, updated the target destructuring accordingly, added required search verdict metadata, and added this second-reading report.
