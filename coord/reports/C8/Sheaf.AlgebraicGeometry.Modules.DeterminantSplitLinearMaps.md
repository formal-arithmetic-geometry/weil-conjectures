## What changed

Completed the retirement explicitly listed for this item in coord/retire-items.tsv,
following coord/changes/retire-sheaf-twins-20261020.md. Withdrew the 619-line Sheaf
DeterminantSplitLinearMaps copy through deleted.txt and redirected
lem-sc-split-determinant-linear-maps to the existing, fully proved upstream theorem.
No upstream file is edited.

Adapted its sole direct consumer, Sheaf.AlgebraicGeometry.Modules.DeterminantSplitComparison,
which is unclaimed. Its public signature and docstring remain verbatim. It imports the
upstream theorem and transports its linear family through the already proved
exteriorSheafPowerIso. A private proved helper supplies forward wedge compatibility;
tensor-section compatibility and morphism naturality give the same formula and restriction
equation. The same local-bijectivity theorem completes the construction. The explicit
LinearMap/Equiv.ofBijective structure retains the original forward maps.

Updated both relevant DAG proof descriptions and dependency lists. The canonical
comparison dependency moves from the retired theorem's proof to its old-API consumer.
The unit route and every mathematical hypothesis and conclusion stay unchanged.

Validation: the original item compiles (19.3 s); the final adapted consumer compiles
(3.6 s) and its unmodified direct importer DeterminantWedgeMorphismSplit compiles against
the delivered overlay (9.8 s). The delivery preflight checks the axioms.

Change record: coord/changes/C8-retire-determinant-split-linear-maps.md.

## Proved and sorry left

This is a listed retirement repair with zero original holes. Holes closed: 0. Holes
added: 0. Split off: 0. No sorry remains in any delivered Lean source.

AlgebraicGeometry.Scheme.Modules.determinant_split_linear_maps_exists is already fully
proved in the retained upstream module; this delivery does not claim its proof as a new
hole closure. AlgebraicGeometry.Scheme.Modules.determinant_split_comparison_exists is
fully proved after API transport. The new private exteriorSheafPowerIso_hom_wedge is
fully proved from the existing inverse wedge compatibility and inv_hom_id.

## No longer needed

Pruned module: Sheaf.AlgebraicGeometry.Modules.DeterminantSplitLinearMaps. Its sole
consumer no longer imports it; no Lean file in the source tree still imports the retired
module after the delivered adaptation. The node is retained and redirected to the official
proof, including for DAG parents whose proofs are not yet complete.

Removed the consumer's unused private import WeilConjectures.LinearAlgebra.ExteriorTopDirectSum;
it is not used by this proof. The retired copy's private local evaluation, local generator
induction, lift-independence and pairing-transport implementations are no longer duplicated.
The upstream proof still needs lem-sc-exterior-tensor-local-pairing,
new-j1-exterior-sheaf-rank-wedge-zero and def-sc-sheaf-exterior-power, so none is pruned.
lem-sc-exterior-sheaf-power-comparison remains needed by the adapted old-API consumer,
but is removed from the upstream theorem's own proof dependencies. No other nodes or
modules are claimed to be unnecessary.

## Where the brief, the DAG or earlier work was wrong

The generic brief describes a proof item repeatedly split five times, but the current
item and its upstream twin both contain complete proofs and zero sorry. The current
retirement manifest explicitly assigns removal of this duplicate, so this packet performs
that concrete repair rather than reporting a new mathematical proof or a no-op.

The node still pointed to the Sheaf copy although its reviewed_proof record referred to
a prior retirement. It now points to the actual retained upstream declaration and records
its exact current exteriorPower/wedge signature. The old exteriorSheaf statement is
preserved at the consumer by a proved canonical transport, without adding any rank,
positivity, nonempty or nonzero-ring hypothesis. There is no current C8 return or rework
row for this item, and no quarantine path is deleted.

## Second reading by C8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
