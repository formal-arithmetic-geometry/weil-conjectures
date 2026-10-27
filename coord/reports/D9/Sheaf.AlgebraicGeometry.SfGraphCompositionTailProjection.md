## What changed

Proved `AlgebraicGeometry.Etale.sfGraphCompositionTailIso_projection` by transporting the
Cartesian proper/open interchange projection square across the two graph-model comparisons,
then cancelling the first graph comparison. The actual compositor is identified using the
already proved `graphCompositor_normalization` and `diagramCompIso_raw` helpers; no endpoint
isomorphism is chosen.

Added `Sheaf.AlgebraicGeometry.SfGraphInterchangeProjection` with the reusable Cartesian
interchange square. Its proof specializes the existing compatible-tower calculation to
`(e,r)`, `(e k,p)`, `(i,q)`, evaluates it on `Ra M`, and pastes in the proper projection for
`a`. Two pullback associativity identities account for all coefficient maps. Existing
theorem signatures and source-library files are unchanged.

The unclaimed data module now implements `sfGraphWordProjection` as the
`ModuleCat A` specialization of the explicit construction in the new
`SfGraphProjectionWord` module. That construction composes precisely the original three
projection components and the original pullback compositor evaluated componentwise.
Its proper-prefix factorization is proved for a parameter coefficient category by
proper-projection naturality and inverse threefold pullback associativity. Keeping the
coefficient category and three morphisms as parameters avoids the expensive repeated
conversion of derived-category structures after constructing a graph record.

The two data definitions scope out the reflexive-quiver instance while elaborating their
signatures. Their existing signatures, visibility and declaration order remain unchanged.
The data module adds one public import because its public definition uses the new
construction; other added imports are proof imports. The change record explains the
equality with the original construction and the dependent target review. No data is
chosen from an existence theorem.

The proof imports the existing graph-word square, the new interchange square, and (with
`import all`) the existing graph-compositor normalization helpers. The new module similarly
reuses the existing tower and Cartesian-normalization helpers through proof imports.

The final four-module packet and all seven unchanged explicit consumers compiled cleanly
in import order. The generic construction/factorization took 38.7 seconds, data 29.4 seconds,
Cartesian interchange 27.5 seconds, and assigned tail 38.2 seconds. The seven consumers
took 33.3–50.8 seconds each. No consumer adaptation is included. The delivery compile and declaration probes also passed.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Etale.sfGraphCompositionTailIso_projection`
(node `lem-sf-etale-graph-composition-tail-projection`): 1 of 1 original holes.

Added no holes. The new theorems
`AlgebraicGeometry.Etale.sfGraphProjectionWord_proper_prefix` and
`AlgebraicGeometry.Etale.sfGraphInterchange_projection`
(nodes `lem-sf-etale-graph-proper-prefix-projection` and
`lem-sf-etale-graph-interchange-projection`) and all private helpers are proved.
The existing imported `sfGraphCompactificationComparison_projection` remains an existing
proof dependency; its module is unchanged.

## No longer needed

No original import was removed, and no module is withdrawn.

The original direct planned dependencies
`lem-sfb-ringed-projection-tensor-composition` and
`lem-sfb-ringed-derived-monoidal-comparisons` are unnecessary for this proof. Their separate
ringed-topos interfaces are replaced by the already proved constant-coefficient tower
calculation and the source library's canonical pullback composition identities.

The original direct node `lem-sf-etale-proper-open-tensor-square` and its standalone
module `Sheaf.AlgebraicGeometry.EtaleProperOpenTensorSquare` is not needed as
an additional import: its tensor calculation is already inside the tower proof reused here.
`lem-amb-open-projection-composition` remains used transitively by that tower calculation;
no pruning of it is claimed. The parent node's direct dependencies now record the actual
interchange, normalization and graph-square route. No claim is made that these planned
nodes are globally unused by other parents.

## Where the brief, the DAG or earlier work was wrong

No false statement or definition was found. The original proof plan can be shortened by
reusing two pieces of completed work: the general compatible-tower calculation and the
normalization of the actual graph compositor from the base-change work. These preserve the
specified graph maps and the unit route, and work for arbitrary schemes and unbounded
complexes. Empty or identity opens, zero coefficients and zero complexes are included;
there is no cancellation of a projection map and no extra quasi-compactness hypothesis.

The compatible-tower calculation is used as a generic projection calculation, and the
base-change module supplies only its explicit-map normalization helpers. Neither use
replaces a statement or a realized proof step of the assigned unit by another unit's
statement. The new nodes record these generic-tool uses for the reader.

## New nodes

`lem-sf-etale-graph-interchange-projection` records the Cartesian interchange square for the sequence
`Ra_*`, `De_!`, `Rr_*`, `Di_!`, `Rq_*` versus
`Ra_*`, `D(e k)_!`, `R(p q)_*`. It requires neither a compactification of `f` or
`f g` nor a neighborhood-shrinking comparison, and is a strict component of the assigned
tail argument. It is proved from existing tower and normalization helpers; no split-off
hole remains. Blueprint searches for proper/open projection, projection composition and
interchange found no duplicate tensor equation. The pro-etale existence/isomorphy result
`det-sf-comp-composition-interchange` concerns a different statement.

`def-sf-etale-explicit-graph-projection-word` records the explicit canonical construction
over a coefficient-category parameter and three supplied morphisms. It is the original
graph word with its final compositor evaluated componentwise, and is the implementation
of the existing constant-coefficient definition. It contains no postponed data or new
hypothesis on that existing definition.

`lem-sf-etale-graph-proper-prefix-projection` records the explicit successive projection
construction over a parameter coefficient category and its proper-prefix factorization.
The latter follows by expanding the compactification projection, proper-projection
naturality, and inverse pullback associativity; it does not eliminate a compactification
equality. The three factors are explicit parameters. The node's public construction
provides the actual implementation of the existing constant-coefficient graph-word map,
with its unchanged canonical components. The source and Mathlib searches found no
existing graph-word prefix statement. The construction and both new theorem nodes are complete.

Change record: `coord/changes/D9-graph-projection-quiver.md`. It records the scoped
quiver-instance settings and generic explicit-factor construction, unchanged mathematical
content, and all explicit consumers.

## Second reading by D9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
