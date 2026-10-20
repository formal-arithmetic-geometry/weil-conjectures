## What changed

Restored the quarantined module
`Sheaf.Algebra.Homology.TorIndependentProjectiveComplexTensor`, replacing its
obsolete public import of the withdrawn Sheaf model with
`WeilConjectures.Algebra.Homology.BaseDerivedTensorCohomologyModel`.
This repairs the assigned post-sync visibility error. All other source text,
including the theorem signature and complete proof, is preserved verbatim.

The proof uses finite-projective Tor acyclicity, the termwise universal-counit
comparison and flat localization exactly as the node specifies. All four declared
proof dependencies remain needed. The node and its canonical model attachment
were checked; no route, node or unit change is necessary. Searches with LeanFinder,
Loogle and ripgrep confirmed the existing assembly and its Mathlib ingredients.
The restored file compiles cleanly through lcompile.py in 2.2 seconds.

Change record: `coord/changes/G4-tor-independent-projective-canonical-model.md`.

## Proved and sorry left

This is a zero-hole repair. The archived module has 0 sorries, and the restored
module has 0 sorries. Its existing complete theorem is
`ModuleCat.torIndependent_projectiveComplex_tensor`
(node `lem-pc-tor-independent-projective-complex-tensor`).
Holes closed: 0. Holes added: 0. Split off: 0. No remaining sorry declarations
in the item or added elsewhere. The existing proof is retained, not counted as
new proof progress.

## No longer needed

Removed the obsolete import
`Sheaf.Algebra.Homology.BaseDerivedTensorCohomologyModel`, whose implementation
was already withdrawn in favor of upstream. Replaced it with the canonical
upstream import; no mathematical dependency, node or module is pruned. No other
import is removed. All existing proof dependencies are retained.

## Where the brief, the DAG or earlier work was wrong

The item has no sorry to fill: it is the assigned rework repair recorded in
coord/rework.tsv. Its archived public model import became obsolete after the
upstream migration. The canonical dependency modules already use the upstream
model. Restoring that import resolves the visibility error without changing the
statement, proof or model. No error in the mathematical DAG was found.

## Second reading by G4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
