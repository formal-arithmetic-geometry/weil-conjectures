## What changed

Retired `Sheaf.AlgebraicGeometry.AbelianRepresentableGeneratorCoherence`, the
zero-hole retirement listed in `coord/retire-items.tsv`, in favor of the identical
proved theorem in its `WeilConjectures` twin. The coherence node now points at that
source theorem, whose source file and proof remain unchanged.

Preserved the existing public `AlgebraicGeometry.Etale.sectionsEquiv_precomp`
with its exact signature and proof in the new module
`Sheaf.AlgebraicGeometry.EtaleRepresentableSectionsNaturality`. Unlike the source
module's private helper, this API is needed by the open-cohomology comparison.
Changed its sole direct consumer's private import to the new helper module.
Added a dedicated attachment node for this already proved helper and changed the
consumer node's corresponding proof dependency. No target statement, definition,
or unit route changes.

Change record: `coord/changes/retire-abelian-representable-generator-coherence.md`.

Validation: `lcompile.py --all` compiled the helper and the adapted direct consumer
(8.7 s and 49.4 s). A separate combined-import probe compiled and printed only
`propext`, `Classical.choice`, and `Quot.sound` for both the official coherence
theorem and the retained public helper. The old item also compiled before the
change, confirming that this is a zero-hole retirement, not an unreported proof.

## Proved and sorry left

The assigned module initially contained zero holes. Holes closed: 0. Holes added:
0. Split-off unfinished statements: 0. No `sorry` remains in any delivered module.

`AlgebraicGeometry.Etale.abelianRepresentableGenerator_coherence` is reused from
the adopted source library with its identical statement and complete proof.
`AlgebraicGeometry.Etale.sectionsEquiv_precomp` retains its existing complete
adjunction-naturality proof. The consumer proof is unchanged.

## No longer needed

Pruned module: `Sheaf.AlgebraicGeometry.AbelianRepresentableGeneratorCoherence`.
Its duplicate coherence theorem, seven private theorem helpers, and two private
definitions are no longer redeclared in the Sheaf tree. The upstream copies are
preserved verbatim; their proof dependencies remain needed there.

The withdrawn item's three imports are no longer needed by the retained helper:
`WeilConjectures.AlgebraicGeometry.CyclicDerivedHomComparisonMap`,
`WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence`, and
`WeilConjectures.AlgebraicGeometry.ConstantSectionAdjunctPullback`.
The helper needs only
`WeilConjectures.AlgebraicGeometry.EtaleOpenCohomologyComparison`.

Removed the consumer's import of the retired item and its node dependency on
`lem-sbc-abelian-representable-generator-coherence`, replacing them with the
retained helper module and its dedicated node. The generator-coherence node
remains needed by the upstream cohomology-map naturality argument; no mathematical
node or unit step is withdrawn. No source-library declaration is pruned.

## Where the brief, the DAG or earlier work was wrong

The generic proving brief describes an outstanding hole and repeated unfinished
splits, but the current assigned file is fully proved and is listed as a
retirement. The actual API difference is that the Sheaf copy exposes
`sectionsEquiv_precomp` while the official twin keeps it private. Deleting the
whole copy without preserving that public helper would break the current
open-cohomology consumer. The existing generator node attached both results;
its primary statement now points to the official theorem, while the helper gets
a separate attachment. The retirement table's other listed Sheaf consumer is
already absent from the current tree.

## New nodes

`lem-sbc-abelian-representable-sections-precomp` records the existing, fully
proved public helper in `EtaleRepresentableSectionsNaturality`; it introduces no
new mathematical assumption or proof obligation. Its proof is the two
adjunction naturality equations followed by lifted Yoneda naturality, and works
for identity arrows, empty objects and zero coefficients.

## Second reading by D2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
