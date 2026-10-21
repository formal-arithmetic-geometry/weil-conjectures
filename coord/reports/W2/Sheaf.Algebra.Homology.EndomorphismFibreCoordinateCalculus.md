## What changed

Proved all eleven theorem holes in
`Sheaf.Algebra.Homology.EndomorphismFibreCoordinateCalculus`.
The public signatures, definitions, attributes and imports are unchanged.
Validation: the complete module compiled without errors or warnings in 3.3 seconds
through `lcompile.py`.

Two proved private helpers express incoming-map extensionality and the
zero-second-coordinate decomposition, directly from `mappingCocone.id_X`.

The biproduct isomorphism has the displayed projections as its forward map
and the two cocone inclusions as its inverse. Its differential formula
specializes Mathlib's `mappingCone.d_snd_v` after shifting by minus one.
The diagonal cocone inclusion formulas establish additivity and map coordinates.
The forward signed comparison coordinates and coherence specialize the existing
proved `SignedMappingCoconeShift` API; cancellation gives the inverse coordinates.
The strict lift coordinates, naturality and shift compatibility then follow
from Mathlib's lift equations and the two private helpers.

Updated the item's DAG proof and proof dependencies to record this use of
`lem-weil-signed-mapping-cocone-shift`. This is a generic, proved tool for
mapping cocones, not a replacement of the derived-Nakayama unit's route.

## Proved and sorry left

Closed eleven holes, all under namespace `CochainComplex`:

- `endomorphismPairTransformation_commShift`
- `endomorphismFibre_coordinates`
- `endomorphismFibre_additive`
- `endomorphismFibre_map_coordinates`
- `endomorphismFibreShift_coordinates`
- `endomorphismFibreShift_coherence`
- `endomorphismFibreAugmentation_condition`
- `endomorphismFibreAugmentation_coordinates`
- `endomorphismFibreAugmentation_naturality`
- `endomorphismFibreAugmentation_shift_condition`
- `endomorphismFibreAugmentation_shift`

All eleven realize `lem-pe-endomorphism-fibre-coordinate-calculus`.
No holes remain in the item; zero holes added; zero statements split off.

## No longer needed

None: all three existing public imports supply structures or definitions used
by the unchanged public declarations, and both original proof dependencies
remain needed. No modules or nodes are withdrawn. Reproving the generic signed
comparison and coherence calculations here is unnecessary because the existing
proved signed-cocone theorem already supplies them.

## Where the brief, the DAG or earlier work was wrong

The mathematical statement is correct. The original node proof listed only
abelian-category and derived-category definitions; the written Lean proof also
uses the existing proved signed-cocone coordinate and coherence theorem.
The updated proof dependency records that theorem explicitly. No definition
repair, statement change, consumer adaptation or new node is needed.

## Second reading by W2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
