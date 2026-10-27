## What changed

Proved the finite and integral pullback-square monoidality equations by categorical
cancellation of the composition comparisons. Proved finite domain closure using
the supplied operation datum, K-flat tensor representatives, finite Tor pullback,
and transport along the canonical tensor and square comparisons. Proved every
integral domain, including the four proper images, using integral operation
preservation and the supplied direct-image realization.

The main theorem assembles these results with two separate open-calculus lemmas.
The main proof compiled in 21.7 seconds during profiling. The cleaned four-module
compile passed with no diagnostics. An initial combined consumer compile timed
out; the unchanged consumer compiled against the published baseline in 38.7 seconds,
and its unchanged delivery-overlay recheck passed in 48.6 seconds.

All existing definitions move verbatim into OpenBaseChangeSquareData, publicly
reexported by the original module, to make the intermediate lemmas importable
without a cycle. No existing signature or target changes.

## Proved and sorry left

Closed: WeilConjectures.OpenProjectionBaseChange.openBaseChangeSquare (1 original
hole), by decomposition with complete proofs of monoidality and domain closure.

Added and left: WeilConjectures.OpenProjectionBaseChange.finite_open_cartesian_calculus
and WeilConjectures.OpenProjectionBaseChange.completed_open_cartesian_identity
(2 theorem holes), with nodes lem-sf-finite-open-cartesian-calculus and
lem-sf-completed-open-cartesian-identity, respectively. The former concerns the normalized ambient finite open maps and
their equation, independent of constructible-domain closure; the latter concerns
only the completed equation on already supplied domains. There are zero holes in
definitions or private helpers, and zero holes left in the item module. This is a decomposition, not a net hole reduction.

## No longer needed

Removed proof imports Sheaf.Paper.SfIntegralDirectImageConstructible,
Sheaf.Paper.CompletedCoefficientMonoidalAdjunctionTransport and
Sheaf.Paper.CompletedCoefficientPushforwardComparison. Their nodes
lem-sf-integral-direct-image-constructible,
lem-pur-completed-coefficient-monoidal-adjunction-transport and
lem-pur-completed-coefficient-pushforward-comparison are unnecessary for this
proof: SixFunctorDatum supplies the exact ambient direct-image comparison.
This makes no claim that those modules are globally unused.

The original finite domain route through new pulled-back stratifications and
Noetherian finite-type closure is unnecessary here. The finite pull/open functors
of SixFunctorDatum already take values in the constructible category and their
published comparisons identify the ambient objects. Removed direct proof imports:
Sheaf.Paper.ProEtaleFiniteLocalConstancyPullback,
Sheaf.Paper.OpenFiniteConstructibilityInterval,
WeilConjectures.ConstructibleSheaf.Pullback and
Sheaf.AlgebraicGeometry.ProEtaleConstantExact. This proof does not directly need
lem-pur-proetale-finite-local-constancy-pullback,
lem-sf-open-finite-constructibility-interval,
lemma-constructible-pullback-stratification,
lem-weil-pbc-finite-type-over-noetherian or
lem-sfb-finite-type-composition-base-change. Mathlib supplies the Noetherian instance
needed only to apply the existing finite-Tor pullback theorem along the open i.

The main assembly also removes its direct proof import of
Sheaf.SixFunctors.OpenTensorNormalization; the finite open calculus retains that
node as a dependency of its own. None of these removals withdraws any declaration. The corresponding obsolete
top-level tool_uses approvals are removed from the item node; the retained entries
keep their original order.

The original proof-only citations of def-exchange-projection and
def-weil-finite-torsion-constructibility are replaced by the data interface;
these definitions remain statement dependencies, so they are not globally
pruned. prop-weil-pbc-proetale-constant-exact is no longer a direct proof
dependency of this node; the intrinsic pullback realization supplies the exact
functor instances needed here.

## Where the brief, the DAG or earlier work was wrong

The DAG's integral direct-image domain step has a shorter route through the
supplied operation datum. The finite domain step can likewise use its supplied
constructible functors. The arbitrary base-change maps need no separatedness:
transport the constructibility of AV and HQ along the canonical comparison
isomorphisms instead of applying the separated finite-Tor pullback theorem to
them.

The remaining substantial glue is the identification of canonical finite and
completed tensor comparisons with the normalized open-unit formulas. The two
intermediate statements isolate those open-map calculations and retain the strict
completed normalization and ambient unbounded finite inputs.

## New nodes

- def-sf-open-base-change-square-data: existing definitions, moved verbatim, no holes.
- lem-sf-finite-open-cartesian-calculus: normalized ambient finite open calculus.
- lem-sf-completed-open-cartesian-identity: completed identity on supplied domains.

Change record: coord/changes/P2-open-base-change-square-data.md.

## Second reading by P2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
