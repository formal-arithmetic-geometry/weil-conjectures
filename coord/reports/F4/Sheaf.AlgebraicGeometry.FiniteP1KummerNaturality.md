## What changed

Replaced the proof hole in
`AlgebraicGeometry.Etale.exists_ordinaryFiniteP1KummerNaturality` by a construction
from the existing arbitrary-base class comparison and two component equations.
Surjectivity of `ordinaryFiniteClass_bijective_arbitraryBase` constructs the
Chern arrow on every base. Its injectivity proves equality with the specified
`projectiveLineTraceDatum.chern` on Noetherian bases. Each arrow is determined by
its cohomology class; the proof chooses no arbitrary object from mere existence.
A proved private categorical lemma combines component equations using additivity,
preservation of binary biproducts and biproduct extensionality.

Added two separate modules, each containing one strictly smaller component
obligation: `FiniteP1TwistedUnitBaseChange` and
`FiniteP1ChernAdjunctBaseChange`. The former concerns the first component for any
normalized transport and any commutative coefficient ring; it mentions no Chern
arrow. The latter concerns the adjunct of two already specified Chern arrows;
it asserts neither their existence, the twisted-unit equation, nor a family.
Neither statement is the assigned theorem with its hypotheses repackaged.
The main theorem combines both equations with the independently proved family
construction and Noetherian normalization. Its statement and all existing
public declarations, definitions and public imports are unchanged.

The original module's new imports are private proof imports. No module in the
adopted source tree is edited, and no definition or consumer repair is involved.
The node's proof and proof dependencies now describe this construction.

Validation: all three modules compiled through the prescribed remote compiler.
`FiniteP1ChernAdjunctBaseChange` took 41.5 seconds,
`FiniteP1TwistedUnitBaseChange` took 40.2 seconds, and the final assigned module
compiled cleanly in 30.6 seconds. The proof supplies the existing derived
pullback additivity instance explicitly, since synthesis does not see it through
the wrapper. A source comparison confirms that the assigned theorem's entire
signature is unchanged. All Lean lines have at most 100 characters, and every
node's proof dependencies equal the union of its steps' uses.

## Proved and sorry left

Closed the original one hole in
`AlgebraicGeometry.Etale.exists_ordinaryFiniteP1KummerNaturality`
(node `lem-sp-finite-p1-kummer-naturality`), relative to the two smaller
component obligations below. This is a decomposition, not a net proof of the
original obligation: one original hole closed, two holes added, net minus one.
There are zero holes in the assigned module after the change.

The two added holes are:

- `AlgebraicGeometry.Etale.ordinaryFiniteP1_twisted_unit_baseChange`
  (`lem-sp-finite-p1-twisted-unit-base-change`, new module
  `Sheaf.AlgebraicGeometry.FiniteP1TwistedUnitBaseChange`).
- `AlgebraicGeometry.Etale.ordinaryFiniteP1_chern_adjunct_baseChange`
  (`lem-sp-finite-p1-chern-adjunct-base-change`, new module
  `Sheaf.AlgebraicGeometry.FiniteP1ChernAdjunctBaseChange`).

Each is a public theorem with proof exactly `:= by sorry`, a source, a complete
proof in words, and a matching node. There are no other holes in the packet,
including in definitions or private helpers.

The component statements were checked on identity base changes, arbitrary
nonflat and nonreduced bases, empty schemes, zero coefficients, and N=1. The
Cartier equation is a polynomial variable over every base ring, and all the
comparison and mate identities remain valid in the degenerate cases. No
Noetherianity is used in either component statement. The zero-ring case with
N>0 has zero coefficient arrows, consistent with both equations.

## No longer needed

No existing import was removed, and no module is withdrawn or globally pruned.
The original direct Cartier-chart construction of the family is unnecessary:
existence and normalization follow from the existing arbitrary-base bijective
class comparison. Its chart, Cartier-ideal, dual-line and supported-Kummer
nodes remain needed by the Chern-component obligation, where the geometric
naturality argument belongs. The normalized finite-twist and exchange nodes
remain needed below the two component statements. They are not claimed pruned.

The other relevant library statement
`ordinaryFiniteP1_components_baseChange` was read but not imported: it concerns
the untwisted constant component and the negative-twist evaluation adjunct,
whereas this item uses the positive-twist unit and positive Chern adjunct.
Likewise `ordinaryFiniteP1_kummer_maps` has Noetherian hypotheses in its
naturality clause and cannot supply the arbitrary-base equation verbatim.
The naturality proof uses only the two component equations, not invertibility,
proper-exchange isomorphisms, diagonal integrals, or the universal Noetherian
base construction. No additional import of those modules is introduced.

## Where the brief, the DAG or earlier work was wrong

No false statement or definition was found. The original node's existence
argument need not reconstruct the supported Kummer map: the separately proved
arbitrary-base comparison already realizes every cohomology class uniquely.
The existing component base-change theorem has a different twist convention;
using it directly would require additional tensor and evaluation coherence.
This delivery instead records the two positive-twist components appearing in
the assigned statement itself, as separate strictly smaller steps.

The blueprint unit and its route are retained. The new nodes inherit the
original item's chapter and unit and trace their provenance to
`det-sp-tower-p1-adjunction` through the arbitrary-base integral obligation.

## New nodes

`lem-sp-finite-p1-twisted-unit-base-change`: naturality of the shifted twisted
unit alone. Its proof in words identifies the normalized transport by
uniqueness, applies its composition and shift coherence, and uses the
mate-unit identity for the exact exchange.

`lem-sp-finite-p1-chern-adjunct-base-change`: naturality of the Chern adjunct
alone, for two supplied arrows with the actual Kummer specifications. Its
proof in words uses the universally Cartier hyperplane, supported Kummer
pullback, class injectivity, transport uniqueness, and the adjunction mate
identities. It neither constructs a family nor asserts the unit-component
identity.

Both nodes have three kinds of Mathlib searches and separate new Lean modules.
The blueprint and local library searches found no exact duplicate. There are
no change records because no existing statement, definition or public import
is changed.

## Second reading by F4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
