## What changed

Proved `AlgebraicGeometry.Scheme.fieldBasePoint_fibre_isomorphism` in
`Sheaf.AlgebraicGeometry.FieldBasePointFibreIsomorphism`, preserving its signature
and all imports. The field isomorphism is the composite of
`Ideal.algEquivResidueFieldOfField` with the inverse of `Spec.residueFieldIso`.
The two residue-field compatibility lemmas identify its prescribed forward map
and its spectrum. `ΓSpecIso_naturality` gives the global-section equation.
Pullback isomorphism instances and `IsPullback.isoPullback` supply both fibre
presentations; `pullback.hom_ext` proves uniqueness of the comparison.

Updated the existing DAG proof to record these Mathlib specializations. Its
statement and dependency sets are unchanged. No definition or consumer changed.

## Proved and sorry left

Closed the one original hole in
`AlgebraicGeometry.Scheme.fieldBasePoint_fibre_isomorphism`
(node `lem-weil-pbc-field-base-point-fibre-isomorphism`).
Added zero holes; zero holes remain. No split-off statements.

The server single-file compile passed (2.8 seconds). A temporary `#print axioms`
check reported exactly `propext`, `Classical.choice`, and `Quot.sound`; the
diagnostic command was removed from the delivered source.

## No longer needed

None. No imports, declared proof dependencies, nodes, or modules are pruned.
All six declared dependencies are used through their Mathlib realizations.
The explicit fraction calculation and manual pullback inverse construction are
handled by existing Mathlib equivalence and pullback lemmas.

## Where the brief, the DAG or earlier work was wrong

No statement defect found. The DAG’s field and pullback calculations already
have canonical Mathlib implementations, so they need no new intermediate
statements. The proof is uniform in the field and arbitrary schemes, including
empty or nonreduced schemes, and does not impose finiteness or characteristic
conditions. The blueprint unit route is unchanged.

## Second reading by F9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
