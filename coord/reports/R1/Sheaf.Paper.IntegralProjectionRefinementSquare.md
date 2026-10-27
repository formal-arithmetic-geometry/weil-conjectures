## What changed

Replaced the sorry in
`WeilConjectures.FixProjectionCompactification.integralRefinementProjection` by the
simultaneous-system argument, without changing its signature or its public imports.
The proof imports `IntegralCompactificationSystemRealization` and the new
`IntegralProjectionSystemCoordinates` privately. It obtains normalized system operations,
applies the existing system clause of `refinementProjectionCounit`, applies total limit,
substitutes the individual-arrow realization identities, and uses faithfulness of the
constructible-category inclusion. Explicit cancellation of the inverse refinement comparison
then gives the forward square; bifunctoriality cancels the two tensor comparison maps.

The missing interface is isolated as
`WeilConjectures.FixProjectionCompactification.integralProjectionSystemCoordinates` in a new
module. It supplies source/target realization isomorphisms for individual projections and
identifies the two individual refinement arrows. It states no equality between the two
routes around the square. In particular the system counit equation used in the item is
neither assumed by nor concluded by this new statement. The node's proof now records the
actual coordinate substitution and cancellation argument. Two proved private categorical
helpers perform the transport and inverse-square cancellation without unfolding the large derived-limit construction;
local irreducibility attributes keep that construction and the concrete operation words
out of rewriting. No existing definition is changed.

Existing declarations reused:
`WeilConjectures.IntegralSystemRealization.integralCompactificationSystemRealization`,
`AlgebraicGeometry.ProEtale.AmbientProperOpen.refinementProjectionCounit`,
`WeilConjectures.IntegralSystemRealization.RefinementProjection.systemComparison`, and
`WeilConjectures.IntegralSystemRealization.compactificationProjection`.
This delivery contains no copy of a landed theorem and changes no existing definition,
statement, source-library declaration or consumer interface.

## Proved and sorry left

Closed the one original hole in
`WeilConjectures.FixProjectionCompactification.integralRefinementProjection`
(node `lem-sf-integral-projection-refinement-square`). Its proof is complete from the
stated dependencies and the new individual-map coordinate lemma.

Added one hole:
`WeilConjectures.FixProjectionCompactification.integralProjectionSystemCoordinates`
(node `lem-sf-integral-projection-system-coordinates`). Its proof is exactly `by sorry`;
its docstring and node give the source and complete intended proof.

Thus this is a decomposition: one upper hole closed, one lower hole added, zero net
holes closed. No sorry remains in the assigned module. No sorry occurs in a definition.
Validation: `lcompile.py --all` compiled both sandbox modules with exit code 0.
The assigned statement is unchanged, and the new statement record matches its Lean source.

The existing dependency `refinementProjectionCounit` retains its own upstream hole;
this delivery neither changes nor duplicates it.

## No longer needed

No original import was removed, and no module is withdrawn or claimed globally pruned.
The assigned module now directly needs only the system-realization theorem, the system
counit/projection equation, and the individual-arrow coordinate lemma. Its former direct
proof dependencies `lem-coef-integral-residue-tor`, `lem-sf-open-tensor-normalization`,
`lem-sf-integral-direct-image-constructible`,
`lem-pur-integral-operations-preserve-constructible`, `lem-sf-proetale-constructible-origin`,
`lem-weil-pbc-finite-type-over-noetherian`,
`lem-weil-pbc-locally-noetherian-quasi-separated`, and
`lem-cbc-completed-extension-zero-comparison` are now dependencies of the coordinate lemma;
they have not become globally unnecessary.

The tensor-mate equation `lem-sf-proper-open-tensor-compatibility` is not used directly:
the existing `lem-sf-refinement-projection-counit` already packages its system calculation.
Its module remains needed by that dependency. We do not introduce or prove another copy.

## Where the brief, the DAG or earlier work was wrong

The plan's last step combines two different interfaces. The expression-tree realization
provides canonical integral maps in its own interpretation; it does not expose a ready-made
identification with every individual map of the supplied `SixFunctorOperationDatum`.
The new coordinate lemma records exactly this missing transport, including shared endpoint
isomorphisms. No faithfulness of derived finite evaluation is assumed. The only faithfulness
used by the item is that of the actual full-subcategory inclusion.

Checked the source compactification-independence sentence and the unit record
`sk-rem-sf-pf-done`: this argument retains its route. The new statement allows identity
refinements, zero inputs and empty opens; its equations then use identity/zero maps and
impose no extra nonemptiness or Tor hypothesis on K.

## New nodes

`lem-sf-integral-projection-system-coordinates` owns the one new theorem in
`Sheaf.Paper.IntegralProjectionSystemCoordinates`. It isolates realization of individual
projection and comparison maps, independently of their commutativity. The Mathlib searches
(LeanSearch, LeanFinder and grep) found no matching coordinate bridge. Local searches found
and reused the system comparison and projection declarations; the blueprint search found no
duplicate. No change record is necessary because all existing signatures and definitions
are preserved.

## Second reading by R1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
