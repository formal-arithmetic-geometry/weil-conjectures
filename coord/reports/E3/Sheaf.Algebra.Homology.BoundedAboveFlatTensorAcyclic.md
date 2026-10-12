## What changed
Added a reduction of `CochainComplex.acyclic_mapBifunctor_of_boundedAbove_flat_sheaf` to
fixed-degree exactness. The remaining finite truncation and spectral-sequence argument is
isolated as `isZero_homology_mapBifunctor_of_boundedAbove_flat_sheaf` in a new module.
Both files compile; the original module imports only the reduction module in addition to its
existing proof imports.

## Proved and sorry left
The target theorem `CochainComplex.acyclic_mapBifunctor_of_boundedAbove_flat_sheaf` is
proved from the fixed-degree theorem. The new theorem
`CochainComplex.isZero_homology_mapBifunctor_of_boundedAbove_flat_sheaf` remains `sorry`
(node `lem-pc-bounded-above-flat-tensor-acyclic-degree`).

## No longer needed
No imports or DAG proof dependencies were pruned; the stated tensor, acyclicity and
flatness declarations remain the intended dependencies of the isolated argument.

## Where the brief, the DAG or earlier work was wrong
The full truncation and spectral-sequence proof is too large to complete in this session;
no statement or definition was changed.

## New nodes
Added `lem-pc-bounded-above-flat-tensor-acyclic-degree`, a fixed-degree exactness statement
strictly below the target. It is sourced from the fixed-total-degree portion of Stacks Project,
Cohomology on Sites, Lemma 21.17.8 (Tag 06YQ), and is needed to combine degreewise exactness
into acyclicity.

## Earlier second reading (a previous round; superseded)
A second worker should verify the fixed-degree statement and that the target proof uses it without changing the target signature.

## Second reading by E3

1. I compared both delivered modules with the repository versions. The target declaration and all existing signatures are byte for byte unchanged; the only target change is its proof, and the added declaration is in a new module.
2. Both sandbox modules compile with `lcompile.py --all`. The target has no remaining `sorry`; the fixed-degree declaration is the sole named split-off `sorry`, and it has a docstring, source, and matching DAG node. No axiom, unsafe, opaque, extern, or hollow definition was introduced.
3. I searched the local Sheaf and Mathlib homology sources and ran the recorded LeanFinder/grep searches. I found no existing theorem with the fixed-degree statement. The statement is a genuine degreewise reduction of acyclicity (and is strictly simpler than the all-degree target), though its spectral-sequence proof remains open.
4. The target proof applies the fixed-degree theorem at an arbitrary integer degree. Imports are sufficient and no unused proof dependency was identified. The route remains the bounded-above truncation/spectral-sequence route recorded for the item; no unit step was bypassed.
5. The target node's Lean proof now matches this reduction, and the new node records the fixed-degree statement, source, proof plan, and dependencies. The unit's `realized` route is unchanged.

I changed only the target proof, added the fixed-degree module and node, and recorded this second reading. No import or DAG dependency was pruned.
