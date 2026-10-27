## What changed

Replaced the hole in `Sheaf.Paper.OpenRestrictionAugmentedDescent` by the actual
augmented-computation and localization argument. Its statement and existing public
import are unchanged. Added only proof imports and two proved private helpers.

The private `augmentedComputation` uses the existing ordinary quotient adjunction,
`fixedDerivedComparison`, and `ordinaryAugmentedPresentation`. It constructs natural
computation isomorphisms for the specified calculus, verifies both finite presentation
conditions, and retains the full strict scalar-unit augmentation. It does not require
a coherence record for that calculus: the existing helper calculations do not need one.

The main proof extends an ordinary strict quotient comparison degreewise, restricts
to good complexes, conjugates by those two augmented computations, and applies
`Localization.liftNatIso`. Its representative square is proved by the localization
component formula and cancellation of actual computation isomorphisms. The finite
formula is the ordinary comparison equation in each degree.

Added `OrdinaryOpenRestrictionQuotient` and `OpenRestrictionGoodComplex`, each with
one ordinary geometric theorem. These are strictly smaller steps: the first has no
complexes, derived functors, augmentations or localization; the second only preserves
the good-complex predicate and constructs no comparison. Their docstrings and nodes
state the remaining geometric arguments. No shared module, definition or interface
was changed. The blueprint unit route is retained.

Development compilation checked both new statements and the complete assembly with
`lcompile.py`; the latter completed in 30.0 seconds with profiling enabled. The final
files remove the profiling options. Naming the chosen witnesses directly avoids
repeated elimination through the large conclusion; explicit cancellation arguments
keep the representative-square proof within the standard heartbeat limit. The two
scalar-existence definitions are locally irreducible, as in the existing normalized
presentation code; no exported transparency setting or definition changes.

## Proved and sorry left

Closed the original body hole of
`WeilConjectures.CanonicalOpenRestriction.openRestrictionAugmentedDescent` from the
existing comparison/presentation calculations and two smaller geometric statements.
This is a decomposition, not a net hole reduction: one original hole closed, two
holes added, no original holes left in the item module.

The delivery leaves exactly these two new holes:

- `WeilConjectures.CanonicalOpenRestriction.ordinaryRestrictionQuotient`, node
  `lem-sf-open-restriction-ordinary-quotient`.
- `WeilConjectures.CanonicalOpenRestriction.restriction_preservesGood`, node
  `lem-sf-open-restriction-good-complex`.

No hole occurs in a definition, private helper or intermediate proof body.
The zero complex and empty open satisfy both remaining statements: tensor and
restriction are zero-compatible, and the acyclicity tests on an empty slice are
preserved by the coefficient equivalence. Neither statement assumes flat quotient
maps, completeness, boundedness or quasi-compactness.

## No longer needed

No original import or library module is removed, and no module is claimed pruned.
The original single public import remains. The node now records the dependencies of
the written proof. The generic ringed-topos tensor-pullback, semilinear sections,
open-tensor normalization and K-flat-resolution nodes are no longer directly invoked
by the derived assembly: the first three remain relevant to the two ordinary
geometric steps, and resolution/localization is supplied by the existing good-model
localization. Thus this delivery does not withdraw those dependencies from the library.
No extension comparison r, mate-identification theorem, completion comparison or
completeness theorem is imported by the new argument.

## Where the brief, the DAG or earlier work was wrong

The existing `ordinaryReductionAugmentedComputation` theorem asks for a coherence
record, but its proof never uses that record. The assigned theorem quantifies over
arbitrary specified calculi SU and SX without such records. Rather than changing
that shared interface, the private helper uses its already proved normalized
augmentation calculation and the fixed-calculus derived comparison directly.

The generic ringed-site restriction theorem proves preservation of K-flatness before
transport through `o.integral.inverse`; it does not itself establish the prescribed
transported good-complex predicate. The latter transport is explicitly retained as
one of the smaller remaining statements. Existing same-universe completed-open
models and completion comparisons do not supply this independent-universe restriction
statement with the specified operations. Existing extension-direction descent does
not state the needed restriction comparison or its finite unit/counit formula.

## New nodes

`lem-sf-open-restriction-ordinary-quotient` records the ordinary natural strict
quotient restriction isomorphism and its finite-adjunction word. Source: Stacks
Modules on Sites, Tags 03DJ and 0E8I, and the ordinary quotient-system construction
of Tag 0941. Its finite generator formula retains every transport unit and counit.

`lem-sf-open-restriction-good-complex` records preservation of flat-term K-flat
complexes under the actual normalized restriction. Source: Stacks Tag 0E8K and
flatness under restriction, followed by normalized ringed-site equivalence transport.
Both nodes record the searches actually run through msearch and the existing local
APIs checked. No change record is needed: no existing signature or definition changes.

## Second reading by B7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
