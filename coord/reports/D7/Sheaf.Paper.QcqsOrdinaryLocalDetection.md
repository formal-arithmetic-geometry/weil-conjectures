## What changed

Replaced the hole in `WeilConjectures.IntegralOnSlice.qcqsOrdinaryLocalDetection`
by a proof with its original signature, universes, hypotheses and conclusion.
Specialize the existing `qcqsOrdinaryRestrictionModels` to obtain exactness of
immersion restrictions, chart restrictions and their composites. Identify the
chosen ordinary left derived pullback with the functor induced by the exact
ordinary module pullback, using uniqueness of left derived functors.

Added `Sheaf.Paper.OrdinaryCompletedPullCoherence`, with a complete proof of
`ordinaryCompletedPullCoherence`. Fiber-product comparisons, finite coefficient
map compatibility and the uniqueness of the completed direct ring map give
identity and composition for module direct images. Uniqueness of left adjoints
gives identity and composition for ordinary module pullbacks. This part has no
new holes. The proof privately imports the existing coefficient coherence module;
it changes no declaration in that module or in the adopted source tree.

Added two strictly lower, underived geometry interfaces in separate modules:
`Sheaf.Paper.OrdinaryCompletedOpenClosedDetection` and
`Sheaf.Paper.OrdinaryCompletedCoverDetection`. Both are statements about ordinary
module morphisms on S alone. They have no derived category, arbitrary derived
morphism, ambient immersion r, or composite-arrow transport. Their docstrings
supply sources and proofs in words. The open-closed interface includes the finite
coefficient identification and independent-universe bridge to the ringed module
localization sequence. The covering interface includes chart/site identification
and conversion of the stated precoverage to cover-local sheaf detection.

The main proof supplies all passage to unbounded derived categories using the
already proved jointly-reflecting-family lemmas in
`WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`.
It proves the isomorphic-scheme clause using inverse restrictions, and transports
the open-closed and cover tests through explicit exact derived composition
comparisons. All six added imports of the item are private proof imports; its
public import and signature are unchanged. The item's DAG proof now follows this
route. No other existing module or node is changed.
Remote compilation checked all three new modules and the original theorem proof.
The main theorem compiled in 8.5 seconds; a profiling run of the coherence module
compiled in 12.2 seconds, with no slow declaration. Profiling options were removed
and the compiler's local-instance style suggestions were applied before delivery.

## Proved and sorry left

Closed the item's one original hole:
`WeilConjectures.IntegralOnSlice.qcqsOrdinaryLocalDetection`.
The item now contains zero `sorry` tokens.

Added and proved, with zero holes:
`WeilConjectures.IntegralOnSlice.ordinaryCompletedPullCoherence`
(node `lem-fix-ordinary-completed-pull-coherence`). Its private helpers for site,
finite-ring, completed-ring and module direct-image identity/composition are all
proved; no data definition contains `sorry`.

Added exactly two holes, each the whole proof of a public theorem:

- `WeilConjectures.IntegralOnSlice.ordinaryCompletedOpenClosedDetection`
  (node `lem-fix-ordinary-completed-open-closed-detection`).
- `WeilConjectures.IntegralOnSlice.ordinaryCompletedCoverDetection`
  (node `lem-fix-ordinary-completed-cover-detection`).

Thus this delivery is a decomposition: one original hole closed, two strictly
simpler holes added, net minus one hole closed before any closure accounting.
It does not claim an axiom-free proof of the original target. It also uses the
existing stated `qcqsOrdinaryRestrictionModels` for exactness; its hole is not
created or modified by this delivery.

Edge cases: the coherence construction is for all schemes, including empty ones.
The open-closed module lemma permits either piece, or S itself, to be empty; the
same short exact localization sequence applies. The covering lemma retains the
original nonempty-S hypothesis and permits empty chart members. Its index type
has its original independent universe. Detection on all integer cohomology
objects supplies the unbounded argument without a boundedness hypothesis.

## No longer needed

No original Lean import is removed: the original item's sole public import is
needed by its statement and stays. No existing module is withdrawn.

The direct proof dependency `lem-sfb-exact-open-closed-unbounded-calculus`
(`Sheaf.CategoryTheory.ExactOpenClosedUnboundedCalculus`) is unnecessary for this
item's revised route and has been removed from its node's proof dependencies.
Only the underived open-closed detection and exactness are needed; the existing
proved exact-functor reflection theorem supplies the derived conclusion.
The original proposed K-flat composition route is also unnecessary here: every
restriction used in the theorem is already exact by the stated restriction-model
theorem, so localization uniqueness suffices. No K-flat composition obligation is
introduced or imported for this proof.

The ringed open-closed theorem and cover-local sheaf criterion remain needed
beneath the two new underived interfaces; they are not claimed globally obsolete.
The existing cohomology comparison and derived isomorphism criterion remain
represented in the item's DAG dependencies. No UNIT statement or realized step
is bypassed; `sk-rem-sf-pf-done` has no realized node requirements at this level.

## Where the brief, the DAG or earlier work was wrong

No false statement was found, and no target or shared definition was changed.
The previous plan proposed more derived recollement and K-flat machinery than
this particular assertion needs. The actual missing geometry can be isolated at
the abelian module-sheaf level. The existing ringed open-closed declaration fixes
its module/coefficient universe to the site size plus one, whereas the assigned
statement has independent site and coefficient universes. The new lower
open-closed interface explicitly retains that necessary bridge rather than
silently specializing a universe or adding a hypothesis.

## New nodes

`lem-fix-ordinary-completed-pull-coherence` realizes the proved ordinary module
identity/composition theorem. Its proof records the finite-projection and
adjunction argument, rather than treating coherence as an assumed pseudofunctor.

`lem-fix-ordinary-completed-open-closed-detection` realizes ordinary module
isomorphism detection for a complementary open-closed pair. It is strictly below
the original derived theorem and includes neither derived lifting nor composition
with an ambient immersion.

`lem-fix-ordinary-completed-cover-detection` realizes ordinary module isomorphism
detection for the specified pro-etale cover. It is strictly below the original
derived theorem and includes neither cohomology descent nor ambient restriction.

All three nodes are in `sec-six-functors`, inherit the original unit and blueprint
provenance through the item, record the actual Mathlib searches, and attach their
new module and declaration. No change record is required: there is no existing
statement, definition, public import, attribute or instance change.

## Second reading by D7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
