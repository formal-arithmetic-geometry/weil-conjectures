## What changed

Completed the assigned one-module quarantine restoration. Restored
`lean/Sheaf/SixFunctorsBasics/BrownHypotheses.lean` from the exact archive named in
`coord/rework.tsv`. Replaced its withdrawn public import
`Sheaf.CategoryTheory.CompactObject` with
`WeilConjectures.CategoryTheory.CompactObject`, the canonical definition module
already recorded by node `def-pc-compact-object`. This fixes the actual compiler
failure: unknown `IsCompactObject` in the Brown bundle and its assembly lemma.
Every declaration, signature, definition body and theorem proof is preserved.
The corrected file compiles cleanly with `lcompile.py` in 3.8 seconds.

Change record:
`coord/changes/C3-brown-hypotheses-compact-import-restoration.md`.
The live and archived consumer audit finds no required adaptation. The original
DAG attachment and all proof dependencies are preserved.

## Proved and sorry left

This delivery repairs compilation and restores the missing source; it does not
claim new mathematical proof progress. Original holes closed: 0 of 1. Holes added:
0. The sole remaining hole is `CategoryTheory.brownHypotheses`, node
`sk-lem-brown-hypotheses`, unchanged and already marked `STATEMENT-DISPUTED` in the
archive. All four existing private helpers remain proved without holes:
`localizingClosure_isLocalizing`, `isZero_of_localizingClosure_orthogonal`,
`localizingClosure_generatingFamily`, and `brownHypothesesFor_of_compact`.
No theorem is split off and no definition contains a hole.

## No longer needed

Removed the import of the withdrawn empty module
`Sheaf.CategoryTheory.CompactObject`; the exact canonical notion is publicly
imported from `WeilConjectures.CategoryTheory.CompactObject` instead. No
mathematical dependency, DAG node, declaration, or module is withdrawn or pruned.
The recorded unit route is unchanged.

## Where the brief, the DAG or earlier work was wrong

The current work queue identifies this as a failed one-module restoration,
although the generic brief describes proving an ordinary open theorem. The
archived public import predates the withdrawal of the duplicate Sheaf compactness
module. Compiling the unchanged archive reproduces the failure; correcting that
import suffices to repair the assigned restoration.

The original theorem's mathematical dispute is preserved. Its arbitrary
positive-characteristic field hypothesis does not supply the `FiniteFieldDatum`
required by `WeilConjectures.brownHypothesesGeneration`. Its admissibility
predicate also retains all-continuous-map algebraic-closure coefficients, whereas
the generation and smallness dependencies use finite-subextension-valued
coefficients. These are distinct coefficient objects. Restricting the original
statement would not discharge the two archived arbitrary-field calls in
`LocalizingExceptionalAdjoint`. This packet neither changes those statements nor
claims a counterexample or a proof of the disputed assertion.

## Second reading by C3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
