## What changed

Proved `AlgebraicGeometry.ProEtale.etaleWitnessTransportData` in
`Sheaf.Paper.EtaleWitnessTransportData`, with its complete original signature and
all five existing constructions unchanged.

The proof uses `Scheme.finiteRing_constructibleDerived_origin` for the etale
witness and interval equivalence. The canonical exact intrinsic realization,
the derived composition isomorphism, and the bounded-below compatibility
isomorphism identify the coefficient presentations. Finite cohomological support
supplies explicit bounds; the resulting etale complex belongs to D+.

For each arbitrary witness, `comparison_torAmplitudeIn_iff` reflects the Tor
interval after transporting its universal representative test along the image
of the witness isomorphism. This tests every module sheaf. The canonical unit
normalization follows by simplifying the existing concrete comparison; the
identification inverse follows by composing its two factors. Naturality follows
by applying the transport functor to the assumed square, cancelling the witness
isomorphisms, and using the comparison's naturality. Neither beta nor h is
inverted, and no additivity or exactness of G is assumed.

Updated the existing node's proof, proof dependencies, proof origin and obsolete
tool-use entries to match these applications. No definitions, statements,
public imports, other modules, or node attachments were changed. No change
record or consumer adaptation is required. The unit's realized statement and
steps are preserved: this item is a comparison prerequisite below that route.

Validation: the complete sandbox module compiled cleanly through lcompile.py
(exit code 0, 41.2 seconds). Both new proof-dependency imports passed
`tools/import_direction.py may`. Read the existing declared dependencies before
selecting their more directly applicable finite-ring comparison results.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.ProEtale.etaleWitnessTransportData`
(node `lem-pur-etale-witness-transport-data`).

Proved 1 of 1 original sorries. Zero sorries remain in the delivered Lean module;
zero holes added and zero statements split off. Existing dependency theorems
are used as stated, without claiming to close their dependencies.

## No longer needed

Removed the following direct proof imports and direct proof dependencies:

- `Sheaf.Paper.ProEtaleConstructibleOrigin`, node
  `lem-sf-proetale-constructible-origin`: the general finite-ring essential-image
  theorem already uses exactly the intrinsic realization needed here, avoiding
  the additional continuous-function coefficient presentation in that theorem.
- `Sheaf.Paper.ComparisonPullbackExact`, node
  `lem-sf-comparison-pullback-exact`: the finite-ring origin theorem already
  contains the required cohomological interval equivalence.
- `Sheaf.Paper.ComparisonTorAmplitude`, node
  `lem-sf-comparison-tor-amplitude`: use its underlying general Tor-interval
  equivalence directly, avoiding unnecessary prime-invertibility hypotheses.

The first two obsolete top-level tool-use approvals were removed in their
original order; the site-comparison approval is retained. The new private
imports are `Sheaf.Paper.FiniteRingConstructibleDerivedOrigin`,
`Sheaf.AlgebraicGeometry.ComparisonTorInterval`, and
`WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`.
They supply, respectively, the essential image and intervals, Tor reflection,
and the derived composition and bounded-below compatibility isomorphisms.

These removals concern this item's direct proof dependencies only. No module
is withdrawn, and no claim is made that other consumers or transitive proofs
cease to need those nodes. All original public imports remain.

## Where the brief, the DAG or earlier work was wrong

No false statement or construction was found. The DAG's planned argument is
valid, but the general finite-ring origin theorem combines its first two
steps in the actual intrinsic coefficient presentation. Likewise the direct
Tor-interval theorem proves the third step without coefficient-prime
invertibility. The remaining categorical argument is exactly the stated plan.

Edge cases: finite-support bounds also work for empty support; coincident
bounds are handled by the same vanishing iff. The comparison proof works for
constant functors G and arbitrary noninvertible beta and h. Witness existence
uses no Tor premise, so bounded constructible objects of infinite Tor dimension
are not excluded. No arbitrary data are selected from an unproved existence
statement in a definition: every existing construction remains verbatim, and
existential witnesses are eliminated solely inside this theorem proof.

## Second reading by E1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
