## What changed
Proved the target theorem by unfolding constructibility and applying a new intermediate refinement theorem. Added `IrreducibleLisseRefinement` as a named strict subproblem.

## Proved and sorry left
`exists_irreducible_lisse_stratification` is proved. `exists_irreducible_refinement` remains `sorry`; it isolates the topological/scheme refinement argument described in blueprint proof step 2.

## No longer needed
No imports or planned nodes were pruned.

## Where the brief, the DAG or earlier work was wrong
The original module's proof plan requires a substantial refinement construction, so it was split into the intermediate theorem above.

## New nodes
`lem-weil-pbc-irreducible-refinement`: strict intermediate theorem asserting refinement of a finite lisse stratification to irreducible strata while preserving finite local constancy; source is blueprint proof step 2 in `sec-smooth-purity/sk-prop-sf-cbc`.

## Earlier second reading (a previous round; superseded)
The reduction compiles in the sandbox; the remaining theorem is a strict refinement subproblem with the blueprint's component-removal proof recorded in its docstring and node.

## Second reading by U2
1. **Diff and statements:** Compared the delivered stratum module with the repository version. The existing theorem signature is unchanged byte for byte; the only added declaration is the explicitly split refinement theorem.
2. **Compilation and proof:** Compiled both modules with `lcompile.py --all`; they compile without errors. The target theorem has no `sorry`, while `exists_irreducible_refinement` is the single named split theorem. It contains no forbidden declarations or hollow definitions.
3. **Split statement:** Checked the refinement statement against the component-removal argument and edge cases (including empty strata). It is a strict intermediate result, with a source, docstring proof description, and matching DAG node; no existing library or Mathlib declaration duplicates it.
4. **Pruning and route:** The target proof follows the unit route through constructibility and the refinement node. Removed the now-unused proof-only `Sheaf.AlgebraicGeometry.PullbackFiniteLocallyConstant` import from the target module; retained the public Noetherian import because other modules depend on it. Removed the corresponding no-longer-direct proof dependencies from its DAG node.
5. **DAG agreement:** The target node's proof and `proof_deps` now match the actual short proof, and the refinement node's Lean record matches its module and declaration. The unit's realized route remains intact.

Changed the target imports and DAG proof dependencies as described above; no theorem statements or definitions were changed.
