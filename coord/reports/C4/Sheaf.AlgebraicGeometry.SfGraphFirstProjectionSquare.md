## What changed

Repair of the 2026-10-26 return: updated the private
`word_projection_components` calculation to unfold `sfGraphProjectionWord`,
which now defines the public `sfGraphWordProjection` wrapper. The compile server
still uses the earlier inline definition, so the calculation first tries the new
wrapper and otherwise normalizes the earlier associator expression. Each branch
uses only the simplifications for its definition version; the new branch avoids
the obsolete simplifications identified by the return.
The prior delivery was restored from the recovery commit named in the return.

Proved `AlgebraicGeometry.Etale.sfGraphFirstSideIso_projection` in
`Sheaf.AlgebraicGeometry.SfGraphFirstProjectionSquare`, preserving its statement,
public imports, and docstring. The proof expands the first graph side into section
insertion, Cartesian proper/open exchange, and the direct-image compositor.
Proved private categorical pasting and coefficient-transport lemmas combine their
tensor squares.

The section insertion reuses the proved private `section_tensor` and
`derived_star_id_conjugate` helpers from `SfEtaleGraphTransferTensor` and
`SfExactExchangePasting`, transported through the exact/left-derived comparison
and composition of adjunction conjugates. The exchange and compositor reuse
proved private strength lemmas from `CompactificationProjectionComposition`.
Private imports of `UpperStarRestrictScalars` and `UpperStarIdCoherence` supply
canonical identity-pullback calculations. All five added imports are proof imports.

Private projection-map constructions with explicit types and calculation lemmas
separate the successive projections from their coefficient compositors. Terminal
expressions use the presentation fields directly, avoiding expensive unfolding
of graph and derived-functor constructions during kernel conversion. All new
helpers are private and proved; all new data are explicit constructions.
Updated only the item's DAG proof, proof dependencies, and proof origin to record
this route. No existing definition or other module changed.

## Proved and sorry left

Closed 1 original hole:
`AlgebraicGeometry.Etale.sfGraphFirstSideIso_projection`
(node `lem-sf-graph-first-projection-square`).
Added 0 holes. There are no remaining `sorry` declarations in the item and no
split-off statements or modules. No axiom declarations were added.

The repaired single-file compile through `lcompile.py` passed in 54.6 seconds
with no errors or warnings, using the default heartbeat budget. The theorem-local
unused/unreachable tactic linter settings cover the compatibility branch for the
other definition version. No profiling or kernel-check bypass option is enabled. The public theorem's signature was checked against the current
repository source and is unchanged.

## No longer needed

Imports removed: none. No modules are withdrawn or pruned, and the blueprint unit
route is unchanged.

The planned generic nodes `lem-sfb-ringed-projection-tensor-composition` and
`lem-sfb-ringed-derived-monoidal-comparisons` are not needed as direct proof
dependencies: the existing concrete etale projection-composition, section, and
pullback-compositor APIs supply the required specializations. Their modules were
not imported originally and are not added.

`lem-sf-etale-proper-open-tensor-square` is also unnecessary as a direct proof
dependency: its underlying proved `mixed_twisted_projection` helper is reused
from `CompactificationProjectionComposition` with arbitrary coefficient maps.
These nodes and modules remain available for other consumers.

## Where the brief, the DAG or earlier work was wrong

No statement defect found. The planned generic ringed-topos interface requires
more transport than the existing concrete etale lemmas. The canonical
direct-image identity normalization and monoidality of the pullback section
comparison already have proved private helpers in the library. The proof needs
no quasi-compactness or boundedness hypothesis and never inverts a projection
map. It applies equally to zero objects, identity/open maps, and empty graph
neighborhoods.

The returned global build uses the extracted `sfGraphProjectionWord`, while the
compile server still uses the earlier inline `sfGraphWordProjection` body.
The private calculation handles both definition forms explicitly. The repaired
statement and all mathematical proof steps remain unchanged.

The earlier missing dependency-overlay artifacts no longer block compilation.
The retained candidate needed repairs to the identity-adjunction calculation and
the identification of the direct-image compositor with its conjugate. The
completed proof also normalizes the typed projection components explicitly;
leaving aliases of large derived constructions in the final conversion caused
excessive kernel checking time. No proof or file was split to meet the time limit.

## Second reading by C4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
