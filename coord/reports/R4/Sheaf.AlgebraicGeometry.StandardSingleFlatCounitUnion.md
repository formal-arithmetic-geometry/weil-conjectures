## What changed

Added the per-module Mayer--Vietoris gluing theorem in
`StandardSingleFlatCounitUnionPresentation.lean` and used it to prove
`standardSingleFlatCounitOnOpen_union` by unfolding the universal predicate.
The new theorem is the only remaining mathematical hole; the target theorem's
original `sorry` is closed. The proof-only import of the new module was added.

## Proved and sorry left

Closed `AlgebraicGeometry.standardSingleFlatCounitOnOpen_union`.
The new declaration `AlgebraicGeometry.standardSingleFlatCounitPresentation_union_of_open_presentations`
remains `sorry` (node `lem-pc-standard-single-flat-counit-union-presentation`).

## No longer needed

No existing imports or DAG dependencies were removed; the target proof uses the
new per-module theorem.

## Where the brief, the DAG or earlier work was wrong

The original DAG proof expands the per-module Mayer--Vietoris construction in
three long steps. This delivery isolates that construction as one strictly
smaller per-module statement, leaving the universal quantification as a real
Lean proof.

## New nodes

`lem-pc-standard-single-flat-counit-union-presentation` records the per-module
cone construction and is stated in
`lean/Sheaf/AlgebraicGeometry/StandardSingleFlatCounitUnionPresentation.lean`.

## Second reading by R4

1. **Declarations unchanged.** I diffed `StandardSingleFlatCounitUnion.lean` against the repository. The target theorem signature and all existing declarations are byte-for-byte unchanged; the only interface addition is the explicitly split per-module theorem and its proof-only import.

2. **Proof compilation and axioms.** Both delivered modules compile with `lcompile.py --all`. The union target closes its original proof by applying the per-module theorem. The per-module theorem remains the single named `sorry` listed above; no `sorry` occurs in a definition, and no forbidden declarations occur. Its remaining `sorryAx` is therefore confined to the documented split theorem.

3. **Split statement review.** I searched Mathlib and the library with leanfinder, loogle, and grep (recorded in `searches.jsonl`); no existing theorem states this presentation-gluing result. The split theorem is strictly per-module and has exactly the data needed by the target's universal predicate, so it is a genuine reduction rather than a restatement. Its source, proof sketch, and DAG node agree.

4. **Pruning and imports.** The target proof uses the new module as a proof-only import. The public presentation import remains required by the target statement. No existing proof dependency can be removed, and no unused public import was introduced.

5. **Unit route and DAG agreement.** The unit's union step is retained: the target unfolds `StandardSingleFlatCounitOnOpen` and invokes the per-module Mayer--Vietoris node. The node's declaration, statement, proof dependencies, source, and `split` status match the delivered Lean theorem.

I changed only the second-reader report and recorded the required search results; no mathematical statement or definition was changed during review.
