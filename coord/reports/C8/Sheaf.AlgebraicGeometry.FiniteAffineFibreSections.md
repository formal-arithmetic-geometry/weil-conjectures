## What changed

Proved `AlgebraicGeometry.finite_affine_fibre_sections` by applying the existing proved
`AlgebraicGeometry.Spec.exists_ringEquiv_stalk_tensorProduct_fiber` from
`WeilConjectures.AlgebraicGeometry.FiniteAffineFibreSections`, added as a private proof import.
The statements, definitions, public imports and existing docstrings are unchanged.
Updated the item node's proof, proof dependencies and proof origin to record this reuse.
The unit has no realized proof steps to bypass.

Validation: the module compiled successfully through lcompile.py. A temporary
`#print axioms` check reports only `propext`, `Classical.choice` and `Quot.sound`.
The import-direction check permits the new import. No changes to the source library.

## Proved and sorry left

Closed 1 of 1 holes: `AlgebraicGeometry.finite_affine_fibre_sections`
(node `lem-pc-finite-affine-fibre-sections`). Added 0 holes; 0 holes remain in this module.
No statements were split off. The applied source theorem proves the exact same conclusion
for arbitrary algebras, and all algebra structures and four compatibility clauses match
by definitional equality. The finiteness assumption remains in the assigned statement.

## No longer needed

The item's proof no longer separately needs these planned dependency nodes:

- `lem-weil-pbc-spec-tilde-free-module`;
- `lem-weil-pbc-pushforward-tilde-spec`;
- `lem-weil-pbc-spec-tilde-stalk-localization`;
- `lem-weil-pbc-fibre-product-affine-spectra` as a proof dependency.

The existing proved source theorem supplies the entire affine calculation using its own
pushout/localization proof. The affine fibre-product node remains a statement dependency.
No existing imports were removed: both public Mathlib imports support the unchanged statement.
No modules are withdrawn, and these nodes may still be needed by other consumers.

## Where the brief, the DAG or earlier work was wrong

The DAG plan predates the source-library theorem, which now proves the complete statement
without a finite-module hypothesis. The three tilde-module proof-dependency nodes and the
affine fibre-product proof-dependency node currently have no `lean` record, contrary to the
brief's general availability description; this does not obstruct the proof because the
adopted source theorem is already fully proved and available in the compile snapshot.
The source twin was deliberately retained in the earlier retirement wave because a consumer
was in another pending landing. This delivery preserves the existing Sheaf interface and
closes its hole without touching that consumer or retiring the module.

## Second reading by C8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
