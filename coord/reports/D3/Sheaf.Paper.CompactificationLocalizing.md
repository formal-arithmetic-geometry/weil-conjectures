## What changed

Proved the assigned `compactification_localizing` theorem with its signature unchanged, from the
open-immersion theorem and proper-image hypotheses. The proof constructs the intermediate
compactification as a scheme over the standing field, uses closure minimality for the object
assertion, ambient triangulatedness for exactness, lifted diagrams for coproducts, and composition
for preservation of constructible finite-Tor complexes.

This packet restores the existing F4 proof work from commit
289de412658de99d04951fa9fc8bcb631a5137db, which had subsequently been taken out of the live tree.
D3 inspected the restored proofs and their current dependencies, compiled all eight modules against
the current published build, refreshed the existing node from the current base, and removed stale
review records from the seven restored new nodes. The proof credit remains with F4. D3 removed the redundant private `admissible_of_representatives` wrapper, putting its seven-case
proof directly in the public theorem. The current library lacks the generic lower-bound lemma
mentioned by one source proof, so the explicit bounded-below compatibility argument is retained.

ProperLocalizingAdmissibleCoefficients transports proper-image hypotheses across coefficient-ring
isomorphisms and handles all seven cases of the current predicate. Its six literal cases use the
existing proper coefficient theorem; the full continuous algebraic-closure case has a separate
argument. ProperLocalizingContinuousAlgCl proves that argument from proper constructibility and a
uniform lower-tail estimate: truncation reduces coproducts to bounded-below continuity, cohomology
detects the comparison isomorphism, and small nonzero support handles every existing large
coproduct. The local finite-free and finite Tor modules are completely proved. Proper finiteness
for bounded complexes is reduced by the finite Postnikov filtration to proper finiteness for one
constructible sheaf.

No existing public signature, definition, instance or visibility changes. No held consumer is
adapted. The only remaining holes are the two separate geometric assertions listed below; the
compactification, coefficient transport, coproduct, and finite-Tor assembly proofs are complete.

## Proved and sorry left

Closed the assigned module's original hole:
`AlgebraicGeometry.ProEtale.CondensedRing.compactification_localizing`: 1 of 1; no sorry remains
in the assigned module.

Also proved, with no direct sorry in their bodies:

- `AlgebraicGeometry.ProEtale.CondensedRing.properLocalizingHypotheses_admissible`
  (`det-sf-comp-proper-admissible-hypotheses`).
- `AlgebraicGeometry.ProEtale.CondensedRing.properLocalizingHypotheses_continuousAlgCl`
  (`det-sf-comp-proper-continuous-algcl`).
- `AlgebraicGeometry.ProEtale.continuousAlgCl_lf`
  (`det-sf-comp-continuous-algcl-local-free`).
- `AlgebraicGeometry.ProEtale.continuousAlgCl_bounded_finiteTor`
  (`det-sf-comp-continuous-algcl-constructible-tor`).
- `AlgebraicGeometry.ProEtale.CondensedRing.continuousAlgCl_proper_finiteness`
  (`det-sf-comp-continuous-algcl-finiteness`).

Added exactly two named theorem holes, each with proof exactly `by sorry`:

- `AlgebraicGeometry.ProEtale.CondensedRing.continuousAlgCl_proper_heart_finiteness`
  (`det-sf-comp-continuous-algcl-heart-finiteness`): proper constructibility of the cohomology of
  one constructible sheaf for the full continuous algebraic-closure coefficient. It contains no
  bounded-complex devissage, Tor-amplitude assertion, coproduct assertion or compactification.
- `AlgebraicGeometry.ProEtale.CondensedRing.continuousAlgCl_proper_lowerTail`
  (`det-sf-comp-continuous-algcl-lower-tail`): the uniform proper cohomological lower-tail
  estimate on the localizing closure for that coefficient. It asserts no constructibility,
  coproduct preservation or compactification statement.

This is a decomposition: one original hole closed, two strictly smaller geometric holes added,
net minus one before accounting for imported pre-existing dependencies. It is not an axiom-free
proof of the target closure. Direct axiom probes show that `continuousAlgCl_lf` and
`continuousAlgCl_bounded_finiteTor` use only `propext`, `Classical.choice` and `Quot.sound`.
The assigned theorem still uses `sorryAx` through its named dependencies. Separate identity-map
probes prove both retained geometric conclusions for arbitrary coefficients: the lower-tail
bound holds with c = 0 for every complex, without a localizing assumption, and every higher image
of a constructible sheaf is constructible. Both checks use only the three allowed axioms.

## No longer needed

The conditional `proper_image_localizing_proper` theorem is unused: object preservation follows
from its hypothesis predicate by intersecting the source closure with the inverse image of the
target closure. Its module and node are still needed for the coefficient predicate and theorem;
no shared module is withdrawn and no blueprint unit is bypassed.

The assigned module replaces the direct proof import of
Sheaf.SixFunctors.ProperImageLocalizingProper with
Sheaf.Paper.ProperLocalizingAdmissibleCoefficients, and adds
Sheaf.Paper.LocalizingClosureExistence. The former remains a transitive dependency, so this is
not counted as a pruned module. The open-immersion dependency is retained.

The private `admissible_of_representatives` wrapper is removed; its complete proof is now the
public theorem body. No extra module or node is required for this simplification. No new dependency on
EllAdicProperLocalizingCoproducts or CompactTestsRightAdjointCoproducts is introduced.

## Where the brief, the DAG or earlier work was wrong

The stated proper coefficient theorem accepts six literal representatives. The assigned theorem
accepts an isomorphism-invariant predicate with seven cases, including both all continuous maps
into PadicAlgCl and finite-subextension-valued sections. The two rings are different, as the source
EllAdic module explicitly documents. The six-case theorem cannot supply the full continuous case
by definitional equality or by an unstated coefficient isomorphism.

The available rational proper finiteness, heart-bound and unbounded-window declarations require
a finite coefficient field or the finite-subextension-valued algebraic closure. New searches of
the current library, LeanFinder and Loogle found no matching full-continuous result. The existing
IntegralModel theorem supplies descent of compact matrix monodromy to a finite field, but does
not itself give the sheaf descent, proper scalar comparison and uniform ind-constructible bound
needed here. Those are precisely the geometric contents retained in the two separate holes.
The exceptional-preservation route imports this item and would form a cycle.

The first dry run was refused by the split-off policy; proof search, simplification and compiler
checks continued. No launcher script or budget metadata was changed. The restored F4 review
stamps are not evidence of independent review of this D3 packet and were removed from new nodes.

## New nodes

`det-sf-comp-proper-admissible-hypotheses`: proved seven-case coefficient-isomorphism transport;
module Sheaf.Paper.ProperLocalizingAdmissibleCoefficients.

`det-sf-comp-proper-continuous-algcl`: proved proper-generator and coproduct assembly for the full
continuous coefficient; module Sheaf.Paper.ProperLocalizingContinuousAlgCl.

`det-sf-comp-continuous-algcl-local-free`: proved local finite freeness for finitely presented
modules over the full continuous field; module Sheaf.Paper.ContinuousAlgClLocalFree.

`det-sf-comp-continuous-algcl-constructible-tor`: proved bounded constructible finite Tor
amplitude; module Sheaf.Paper.ContinuousAlgClConstructibleTor.

`det-sf-comp-continuous-algcl-finiteness`: proved bounded Postnikov assembly of constructible
proper cohomology; module Sheaf.Paper.ContinuousAlgClProperFiniteness.

`det-sf-comp-continuous-algcl-heart-finiteness`: the separate source proper-finiteness assertion
for a constructible sheaf, still sorry; module Sheaf.Paper.ContinuousAlgClProperHeartFiniteness.

`det-sf-comp-continuous-algcl-lower-tail`: the separate source uniform proper cohomological
bound, still sorry; module Sheaf.Paper.ContinuousAlgClProperLowerTail.

All seven nodes and their proofs originate in the prior F4 packet; they are absent from the
current base and are restored with current D3 delivery provenance. No change record is necessary
because no pre-existing public interface or definition changes.

## Second reading by D3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
