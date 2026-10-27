## What changed

Replaced the proof of
`WeilConjectures.CanonicalOpenRestriction.canonicalOpenRestrictionModel` by an assembly
of the geometric restriction descent and the counit square on good complexes. The
existing theorem signature, its documentation, all definitions, and its three public
imports are unchanged. Added only private proof imports and two proved private helpers
in the item module.

The first helper proves that natural transformations out of the integral derived
category agree if their components agree on flat-term K-flat complexes: choose a
complex representing an arbitrary derived object, resolve it by the existing
independent-coefficient K-flat resolution theorem, convert categorical term flatness
using `siteSheafTensorRightIso`, and transport along the resulting isomorphism using
naturality and cancellation. The second helper applies injectivity of the inverse
system-adjunction Hom equivalence and Mathlib's `mateEquiv_counit` to identify the
comparison with the prescribed mate on those representatives, then uses the first
helper. Both helper proofs are complete. Their section respects transparency and keeps
`HasDerivedCategory.standard` locally irreducible, avoiding expansion of the
concrete derived-category model. The original options outside that section remain
as in the item source.

Added two statement modules, each with a source, a detailed proof in words, and its
own node. The new modules also prove four proved local exactness instances each
using the existing restriction exactness and `comp_preservesFiniteLimits` /
`comp_preservesFiniteColimits`. This keeps their signatures elaborating with
transparency respected and the large standard derived-category model folded;
Their declarations are public because statement elaboration cannot use private
instances, but their instance attributes are local to their modules. Their names
are prefixed by descent or counit to keep the modules compatible. The equivalence factors preserve all
limits and colimits by their actual adjunctions; the finite preservation lemmas
then prove the required composed instances explicitly.
`OpenRestrictionAugmentedDescent` constructs the restriction isomorphism and its
augmented strict chain models independently of r and hr; it does not assert
mate identification. `OpenRestrictionCounitOnGoodComplexes` assumes a natural
transformation with such models and the supplied extension normalization; it proves
only the counit equality on good complexes, without asserting existence or
invertibility of that transformation. Thus they separate the two mathematical steps
of the existing plan instead of renaming the original obligation. No arbitrary
witness is chosen in a definition, and no target or public definition changes.

Updated the item's node proof, proof dependencies and proof origin to the actual
assembly. There are no consumer adaptations or change records: no existing public
interface changed.

Validation: the full sandbox compiled in import order after the universe fix:
43.9 seconds for OpenRestrictionAugmentedDescent, 44.3 seconds for
OpenRestrictionCounitOnGoodComplexes, and 67.0 seconds for the original helper
elaboration settings in the item. After the local transparency/derived-model
folding improvement, the item compiled alone in 27.6 seconds with profiling.
The profile reports 5.5 seconds of elaboration and no unresolved goals or errors.
All diagnostic options have been removed for delivery. Original theorem signature,
new node signatures, line lengths and exact hole counts were also checked.

## Proved and sorry left

Original holes: 1. Closed in the item module:
`WeilConjectures.CanonicalOpenRestriction.canonicalOpenRestrictionModel`
(node `lem-sf-canonical-open-restriction-model`). The item now has zero textual holes.
This is a decomposition, not a complete proof without postponed dependencies:
one upper hole is replaced by two strictly smaller mathematical obligations.

Added holes, each the entire proof of one public named theorem:

- `WeilConjectures.CanonicalOpenRestriction.openRestrictionAugmentedDescent`
  (`Sheaf.Paper.OpenRestrictionAugmentedDescent`, node
  `lem-sf-open-restriction-augmented-descent`).
- `WeilConjectures.CanonicalOpenRestriction.openRestrictionCounitOnGoodComplexes`
  (`Sheaf.Paper.OpenRestrictionCounitOnGoodComplexes`, node
  `lem-sf-open-restriction-counit-on-good-complexes`).

The private `eq_of_good_complexes` and
`eq_mate_of_counit_on_good_complexes` have complete proofs, with no holes.
Total delivery holes: 2; closed 1, added 2, net -1. No claim of an axiom-free
proof of the original mathematical assertion is made.

## No longer needed

No existing import was removed and no existing module or node is claimed pruned.
The four original geometric proof dependencies are used in the plans of the two
new nodes rather than directly by the formal assembly in the item. They therefore
remain needed. The assembly directly needs the two new nodes, the existing K-flat
resolution, the site-tensor comparison, and the Mathlib mate identity.

No completeness or reconstruction module was added as a proof dependency. The
nearby OpenRoosRestrictionDescent and completion comparison statements do not supply
this ambient strict-system assertion, and importing them would also introduce a
cycle through IntegralOpenReductionComparison.

## Where the brief, the DAG or earlier work was wrong

The original two steps combine several distinct interfaces: constructing one strict
restriction model, descending it naturally, and identifying its transpose with the
supplied extension comparison. The recorded dependencies do not directly state
either the augmented restriction descent or its counit square for the fixed o, SU,
and SX. In particular `openSemilinearReductionDescent` is in the extension direction
and takes extra coherent-calculus records; `openSemilinearOrdinaryComparison` chooses
operations rather than accepting the fixed ones; and
`ordinaryReductionAugmentedComputation` also requires a supplied coherence record.
None is substituted with hypotheses omitted. The missing geometric steps are now
explicit statements, while the localization/naturality and mate-uniqueness glue is
proved here. No mathematical error or unit-route departure is asserted.

The edge cases of the new statements retain the empty and identity opens, zero
complexes, unbounded good complexes, and independent coefficient universes. The
restriction construction uses identities on pure tensors and no nonzero, finite
Tor-amplitude, boundedness, completeness, or quasi-compactness hypothesis. The
counit statement does not claim that evaluated derived morphisms detect equality:
the proof in words compares strict system maps before localization.

## New nodes

`lem-sf-open-restriction-augmented-descent`:
`lean/Sheaf/Paper/OpenRestrictionAugmentedDescent.lean`. This is the geometric
restriction construction and descent, without any r or hr. It is sourced in
Stacks 03DJ, 0E8I, 0G7E, 06YY, 0GL1 and 0941 and the original representative step.
LeanSearch, Loogle, local source searches and blueprint searches found no theorem
with the fixed-operation augmented assertion.

`lem-sf-open-restriction-counit-on-good-complexes`:
`lean/Sheaf/Paper/OpenRestrictionCounitOnGoodComplexes.lean`. This is one counit
square on good representatives, from given extension and restriction strict models;
it asserts neither existence nor invertibility. It is sourced in the original
extension-summand transpose calculation and Stacks 03DJ, 0E8I, 06YY, 0GL1 and 0941.
Searches found formal adjunction mate identities but no strict-system counit square.

Both nodes keep chapter `sec-six-functors`, unit `sk-thm-sf-compatibility`, and the
original blueprint ancestor `fix-prop-coherence`. No unit or chapter record changes.

## Second reading by U2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
