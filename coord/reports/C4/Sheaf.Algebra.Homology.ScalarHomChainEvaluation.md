## What changed

Proved `SheafOfModules.StrictScalarHom.exists_scalarHomChainEvaluation` without changing
its statement. Added the private proof import
`Sheaf.Algebra.Homology.SliceScalarHomChainAdjunction` and proved private helpers for the
ordinary adjunction on chain maps, local evaluation extensionality, and functoriality.
Constructed sigma by transposing `H_R(id, transpose(q))` through theta and the ordinary
adjunction. Constructed alpha from sigma with identity q, transported through nu and theta.
Updated the existing node proof to match this shorter route. No definition or public
interface changed. A change record documents the private helper `omit` commands
classified by the preflight scanner:
`coord/changes/scalar-hom-chain-evaluation-private-helpers.md`.

Validation: the complete file compiles without warnings through `lcompile.py` in 6.5 seconds.
The new proof import passes `tools/import_direction.py may`.

## Proved and sorry left

Closed 1 hole: `SheafOfModules.StrictScalarHom.exists_scalarHomChainEvaluation`
(node `lem-sfb-scalar-hom-chain-evaluation`). Added 0 holes. No sorry remains in the item.
The proof uses the existing declared dependency
`SheafOfModules.StrictScalarHom.exists_sliceScalarHomChainAdjunction`, whose own proof is
outside this item. No result is split off.

## No longer needed

No existing import was removed. The direct coordinate construction of alpha and the direct
sheafification construction of sigma are unnecessary: the normalized ordinary and internal
Hom adjunctions construct these maps as chain maps. Consequently this node no longer directly
uses `def-weil-pbc-module-tensor-product`,
`def-weil-presheaf-modules-sheafification`, or `def-pur-localized-ringed-site` as proof
steps; they remain available through the slice-adjunction dependency and are not withdrawn.
`def-pur-hom-complex` remains a statement dependency, with the concrete product-projection
API used for the proof. No module is withdrawn or claimed globally unnecessary.

## Where the brief, the DAG or earlier work was wrong

The original ten-step coordinate plan is mathematically sound but repeats constructions
already supplied by the normalized slice adjunction. The shorter route reuses those
constructions and their chain equations. The slice-adjunction declaration needs slice
sheafification instances in addition to the item's global assumptions; these follow from
the site's size using the existing coefficient-universe instances. No new hypothesis is
added. The unit has no realized nodes or steps to bypass.

## Second reading by C4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
