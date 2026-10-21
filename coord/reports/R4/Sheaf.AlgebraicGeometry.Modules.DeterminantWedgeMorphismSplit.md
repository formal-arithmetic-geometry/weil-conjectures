## What changed

Completed the retirement assigned by coord/retire-items.tsv:918. Withdraw
Sheaf.AlgebraicGeometry.Modules.DeterminantWedgeMorphismSplit and attach its node
to the complete adopted WeilConjectures theorem. Adapt the sole direct consumer,
Sheaf.AlgebraicGeometry.Modules.DeterminantShortExactExists, to transport its
morphism through the existing exteriorSheafPowerIso comparisons and use the
adopted theorem. Preserve its public signature, public imports and docstring.
Update both nodes' proof descriptions and the parent's comparison dependency.
Change record: coord/changes/R4-retire-determinant-wedge-morphism-split.md.

## Proved and sorry left

The item already has zero textual holes. Closed 0, added 0, split off 0; no
remaining sorry in the delivered consumer. The existing
AlgebraicGeometry.Scheme.Modules.determinant_shortExact_exists is completely
proved with the new transport argument. The replacement
AlgebraicGeometry.Scheme.Modules.determinant_wedgeMorphism_bijective_of_split
is the unchanged, already proved adopted theorem. This is a retirement repair,
not a newly closed mathematical hole or a decomposition.

Validation: the adapted consumer compiles without warnings (4.6 seconds), and
the sandbox --all compile passes (6.2 seconds). The unchanged next consumer,
Sheaf.AlgebraicGeometry.Modules.DeterminantShortExact, also compiles against the
adapted consumer (4.2 seconds). The import-direction check permits the new import.
Searches were recorded through msearch.py (LeanFinder, Loogle and grep), and direct
repository searches found the adopted theorem and existing comparison API.

## No longer needed

Retire the duplicate module
Sheaf.AlgebraicGeometry.Modules.DeterminantWedgeMorphismSplit and remove its
private import from DeterminantShortExactExists. Its duplicated generation,
comparison, local lifting and gluing helpers are no longer needed in Sheaf;
the full adopted theorem retains these arguments. Keep the mathematical node
lem-sc-determinant-wedge-morphism-split and the parent's dependency on it.
The retired node no longer needs lem-sc-exterior-sheaf-power-comparison; that
implementation bridge is now used directly by its legacy parent.

No additional node or module is claimed pruned. In particular the eight old-route
modules listed in retire-items.tsv are historical candidates, not withdrawals
in this packet: their other consumers and unchanged adopted proofs are preserved.
The actual retirement removes only this duplicate; its replacement still needs
lem-sc-determinant-split-comparison and def-sc-sheaf-exterior-power.

## Where the brief, the DAG or earlier work was wrong

The generic proving brief describes an obligation split off twice, but the current
item is already proved and the queue explicitly assigns retirement. The Sheaf and
adopted theorem signatures differ in exterior-sheaf representation, so a bare
import substitution would fail. The comparison isomorphisms and wedge equations
supply the required real consumer adaptation. No mathematical error or change of
the unit route was found. No return or rework entry applies to this item.

## Second reading by R4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
