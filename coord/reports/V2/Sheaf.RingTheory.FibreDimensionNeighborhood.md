## What changed

Proved `Algebra.exists_away_fibre_dimension_le` using the bounded-open theorem, the basic-open
basis, and a named localized-fibre comparison theorem. Added `Sheaf.RingTheory.FibreDimensionLocalizedBound`.

## Proved and sorry left

`Algebra.exists_away_fibre_dimension_le` is proved. `Algebra.localized_fibre_dimension_le_of_basicOpen`
remains `sorry`, recorded by node `lem-weil-pbc-fibre-dimension-neighborhood-localized-bound`.

## No longer needed

None.

## Where the brief, the DAG or earlier work was wrong

The DAG omitted a separately stated Lean bridge for the localized fibre/open-subspace comparison.

## New nodes

`lem-weil-pbc-fibre-dimension-neighborhood-localized-bound`.

## Earlier second reading (a previous round; superseded)

The target proof preserves the node statement and uses the existing bounded-open and basic-open declarations. The new localized comparison statement is a strict subclaim with fixed `g` and no equality hypothesis.

## Second reading by V2

1. **Diff and statements.** Compared the delivered module with the repository version. The existing declaration signature is unchanged; the only interface addition is the explicitly recorded split-off theorem. No target or definition changed.
2. **Compilation and axioms.** Compiled both sandbox modules with `lcompile.py --all`; both compile cleanly. The only remaining `sorry` is the named split theorem `Algebra.localized_fibre_dimension_le_of_basicOpen`, with its DAG node and source docstring. No forbidden declarations or hollow definitions are present.
3. **Split statement.** Checked the localized-fibre comparison statement against its intended localization and open-subspace argument. It is a strict subclaim with fixed `g` and `d`, and is true with exactly the needed hypotheses; it does not restate the target.
4. **Pruning and route.** The target proof uses the bounded-open theorem, the basic-open basis, and the split localized comparison. The import is proof-only and is plain `import`. The node proof and `proof_deps` were updated to match this route; no unused imported module was found.
5. **DAG and unit.** The new node has complete metadata, source, proof, and Lean declaration. The target node now records the two actual proof steps and their dependencies; the unit route through the bounded-open theorem and localization comparison is preserved.

Changed the target DAG proof metadata to match the implemented proof and expanded this second-reading report. No Lean statement or definition was changed.
