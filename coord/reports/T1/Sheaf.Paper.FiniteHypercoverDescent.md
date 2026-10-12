## What changed
Added `FiniteHypercoverDescentParts`, splitting the three independent clauses of finite hypercover descent into named intermediate theorems, and proved the target theorem by assembling those clauses. The intermediate proofs remain explicitly named obligations with their own DAG nodes.

## Proved and sorry left
`AlgebraicGeometry.finite_hypercover_descent` is proved by conjunction assembly. Sorries remain in `finite_hypercover_descent_objects`, `finite_hypercover_descent_morphisms`, and `finite_hypercover_descent_equalities`, each corresponding to a strict clause of the target and recorded by a new node.

## No longer needed
None; the stated proof dependencies remain available to the split clauses.

## Where the brief, the DAG or earlier work was wrong
The original single theorem combines three substantial finite-data descent arguments, so they must be tracked as separate named obligations for a compilable reduction.

## New nodes
`lemma-weil-pbc-finite-hypercover-descent-objects`, `lemma-weil-pbc-finite-hypercover-descent-morphisms`, and `lemma-weil-pbc-finite-hypercover-descent-equalities`.

## Earlier second reading (a previous round; superseded)
Pending independent second reading of the split clauses and their DAG records.

## Second reading by T1

1. Compared the delivered main module with the repository version. The target theorem signature and all existing declaration statements are byte for byte unchanged; only its proof and the explicitly reported split module are added.
2. Compiled both delivered modules with lcompile. They compile without errors; the only remaining sorries are the three named split theorems, each with a corresponding DAG node. No axiom, unsafe, opaque, extern, implemented_by, or hollow definition was introduced.
3. Checked the three split statements against the finite hypercover descent clauses and searched the library and Mathlib for existing declarations. Each is a strict independent clause, true as stated and needed by the conjunction proof; no duplicate declaration was found.
4. The conjunction proof uses the shortest available route: it applies the three split clauses directly. The main module's plain import of `Sheaf.Paper.EtaleFiniteDataDescent` was unused after this reduction and was removed. The unit route is preserved because the three split clauses realize the three recorded steps.
5. Checked the DAG records: each new node has matching Lean statement, proof dependency, source, unit and chapter metadata, and the item's proof now records the three declarations it applies. No old proof dependency is pruned from the split module's planned route.

Changed the report and removed the now-unused direct `EtaleFiniteDataDescent` import from the main module. No mathematical statement or definition was changed.
