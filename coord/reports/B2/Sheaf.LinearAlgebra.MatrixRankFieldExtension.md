## What changed

Proved `Matrix.rank_map_field_extension` in the sandbox module. The proof imports the existing
source theorem `WeilConjectures.Mathlib.LinearAlgebra.Matrix.Rank.le_rank_map_iff` and uses
Mathlib's `linearIndependent_algebraMap_comp_iff`; no new declarations were added.

## Proved and sorry left

Closed the only `sorry`, `Matrix.rank_map_field_extension`. No `sorry` remains.

## No longer needed

The proof does not use the nine planned Sheaf proof-dependency nodes (field-extension setup,
row-span maximal independent subfamilies, or the three dimension lemmas), so they are pruned from
this route. The public Mathlib imports remain required by the statement and proof.

## Where the brief, the DAG or earlier work was wrong

The DAG's long maximal-independent-subfamily route is unnecessary: the existing source-library
minor characterization of rank gives both inequalities directly.

## New nodes

None.

## Second reading by B2

1. **Comparison.** Compared the sandbox module with the repository version. The theorem statement and
all existing declarations are byte-for-byte unchanged; only the proof, imports, and DAG proof metadata
changed.
2. **Compilation and axioms.** Compiled the module with `lcompile.py`; it succeeds with no warnings.
The proof contains no `sorry`, forbidden declarations, or hollow definitions. Its ingredients are the
field injectivity theorem, the determinant rank criterion, and Mathlib's base-change independence
criterion.
3. **Statements and dependencies.** The target statement is unchanged and true, including the empty
index cases. No split-off statements were added. The old planned Sheaf dependencies are not used and
were removed from `proof_deps`; the proof uses only existing declarations and Mathlib.
4. **Route and pruning.** The determinant-minor characterization gives the rank equality directly,
while `linearIndependent_algebraMap_comp_iff` gives the equivalent row-family clause. This is shorter
than the old maximal-independent-subfamily route. The proof-only BaseChange import is now private.
5. **Unit and DAG.** The unit route is respected: this node still realizes the matrix-rank step. The
node's proof and `proof_deps` now match the implementation, with no new nodes.

Changed the BaseChange import from public to proof-only, updated the node's proof metadata and pruned
its obsolete proof dependencies, and recorded this second reading.

The import visibility change is recorded in `coord/changes/MatrixRankFieldExtension-import.md`.
