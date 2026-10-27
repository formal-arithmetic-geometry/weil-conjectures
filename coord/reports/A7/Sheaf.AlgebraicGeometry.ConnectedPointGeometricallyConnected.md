## What changed

Proved `AlgebraicGeometry.GeometricallyConnected.of_connectedSpace_of_isAlgebraic_residueField`
in `Sheaf.AlgebraicGeometry.ConnectedPointGeometricallyConnected`, following the existing
DAG's two steps and Stacks Tags 04KV, 037P and 056R. Installed the canonical residue-field
algebra, applied `geometricallyIrreducible_of_isAlgebraic_mem`, and used the proved source
lemma `GeometricallyIrreducible.geometricallyConnected`. Identified its structure map with
the residue-field point followed by the structure morphism, using
`Scheme.Hom.specMap_residueFieldAlgebraMap`. The resulting morphism over the base satisfies
the hypotheses of `GeometricallyConnected.of_connectedSpace_of_geometricallyConnected`.

Added proof-only imports `WeilConjectures.PointCount` and
`WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Integral` for those existing
proved bridge lemmas. All existing signatures, public imports and definitions are unchanged.
The DAG route is unchanged; no node edits or new nodes are necessary.

Validation: the complete module compiled through `lcompile.py` with exit code 0
in 4.7 seconds and no warnings or errors.

## Proved and sorry left

Closed 1 of 1 holes:
`AlgebraicGeometry.GeometricallyConnected.of_connectedSpace_of_isAlgebraic_residueField`
(node `lem-trf-connected-point-geometrically-connected`). Zero holes remain in the item;
zero holes are added or split off.

The proof uses the existing, still unproved declarations
`AlgebraicGeometry.geometricallyIrreducible_of_isAlgebraic_mem`
(node `lem-zl-field-extension-algebraically-closed-geometric`) and
`AlgebraicGeometry.GeometricallyConnected.of_connectedSpace_of_geometricallyConnected`
(node `lem-trf-geometrically-connected-image-criterion`). They remain their own items;
this delivery proves the assigned theorem from their unchanged statements.

## No longer needed

None. Both original proof-dependency imports and all declared DAG dependencies remain used.
The irreducible-implies-connected Mathlib leaf is used through the existing proved bridge.
No modules, declarations or nodes are withdrawn.

## Where the brief, the DAG or earlier work was wrong

No mathematical error found. The source and the existing two-step DAG argument agree;
the chosen point rules out an empty scheme, and no finite-type, separability or
perfectness assumption was added. The canonical algebra structure in the hypothesis
is the same one installed in the proof. The existing unit route is preserved.

## Second reading by A7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
