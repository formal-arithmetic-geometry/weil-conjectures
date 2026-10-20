## What changed

Repair of returned head `a726bb7749c`: the retained proof packet is rebased by the
delivery tool onto current `sheaf-dag`, with the proved item file explicitly present.
The complete item passed the server compile again (54.5 seconds). The return concerns
landing packet handling; all mathematical changes from the reviewed packet are retained.

Proved `AlgebraicGeometry.ProEtale.projectionComparison_etaleOrigin` with its existing
signature and docstring. The proof follows the fixed compactification's proper/open
route. It normalizes the specified compact-support comparison to the proper mate
followed by the canonical open comparison, pastes the existing proper and open tensor
squares, and cancels the comparison isomorphisms. Boundedness follows from the existing
Tor-amplitude pullback and tensor estimate, with no Tor hypothesis on M.

All additional proof declarations are proved private helpers. The six vocabulary declarations
from `ProjectionComparisonEtaleOriginEquation` move into the item module with their original
signatures and bodies verbatim. Their only direct Lean importer was this item. The old module
is withdrawn and its definition node now attaches to this module. Keeping the vocabulary and
proof together permits sharing of the generated instance proofs in the derived category data.
No source-library declaration, target signature, definition meaning or unit route changes.
Change record: `coord/changes/P4-projection-comparison-shared-vocabulary.md`.

## Proved and sorry left

Closed 1 of 1 holes: `AlgebraicGeometry.ProEtale.projectionComparison_etaleOrigin`.
Added 0 holes; split off 0 statements. No `sorry` remains in this delivery.
The axiom audit still lists the existing imported `sorryAx` dependency: it is already
present in `compact_projection_square`, before the final proof normalization
is used. Thus this closes the assigned hole from existing declarations, as stage 3
requires; it does not claim that the whole imported theory is axiom-closed.

## No longer needed

The following original direct proof imports were removed. Their interfaces are already
available through the retained statement and coherence imports where required; no source
library declaration or globally unused module is withdrawn:

- `Sheaf.AlgebraicGeometry.FixedComparisonDirectImageMate`
- `Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison`
- `Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZeroExact`
- `WeilConjectures.AlgebraicGeometry.ProperBasic`
- `Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence`
- `Sheaf.AlgebraicGeometry.TorAmplitudeKFlatResolution`
- `Sheaf.Paper.CompactSupportSiteCoherence`
- `Sheaf.Paper.ExchangeProjectionSuppliedDomains`
- `Sheaf.Paper.KunnethDerivedTensorTEst`
- `Sheaf.Paper.RingedExchangeTensorCoherence`
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`
- `Sheaf.SixFunctors.OpenTensorNormalization`
- `WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection`
- `WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekProjection`
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`

The explicit flat-model construction, a separate invocation of ringed-topos exchange
coherence, and a new restriction/full-faithfulness proof of the open square are unnecessary:
the proved source bound lemma, generic proper-mate square and open-tensor coherence
already supply them. The following obsolete direct tool-use approvals were deleted,
without reordering or adding approvals:

- `lem-kun-0f1m`
- `lem-weil-pbc-extension-by-zero-exact`
- `lem-weil-pbc-ringed-exchange-tensor-coherence`
- `lem-cbc-proetale-extension-zero-comparison`
- `lem-weil-extension-by-zero-exact`
- `lem-sf-open-tensor-normalization`
- `lem-pur-compact-support-site-coherence`

These dependency removals concern this node's direct proof route; their mathematics may
remain in the retained helpers' dependencies.

Withdrawn module: `Sheaf.AlgebraicGeometry.ProjectionComparisonEtaleOriginEquation`. Its six
declarations remain, unchanged, in the item module. The definition node and all direct Lean
consumers are adapted in this delivery. This removes a module boundary, not a mathematical node.
The canonical support comparison and coefficient-finiteness modules are now explicit public
imports because the moved definitions require them.

## Where the brief, the DAG or earlier work was wrong

No statement defect was found. The original plan described model-level and open-restriction
calculations that are already encapsulated by proved library coherence lemmas. The proof
uses their generic private helpers, not any specialized cohomological-smoothness conclusion.
For efficient checking, pullback composition is proved first as an equality of natural
transformations, and tensor transport first as an equality of complete isomorphisms.
Taking components only afterward avoids expanding sheaf-pullback constructions. The open
and compact-support squares use general categorical pasting helpers so that checking
associativity does not repeatedly unfold the derived functor constructions. The final
pasting application writes its morphisms directly: local data bindings caused costly
conversion checks even though the categorical equations were already proved.

The final inverse-square lemma takes its arrows directly from the goal. The proof normalizes
the bifunctor object expressions before using the four isomorphism inverse identities.

Definitions and theorem types store nested class proofs differently. Two local tactics
first elaborate the ordinary mathematical proof in an intermediate goal, then inline its
concrete private helpers and apply Lean's standard proof abstraction to class arguments.
Keeping the definitions in this module lets that transformation reuse their proof cache.
The original goal receives the resulting ordinary proof term for normal kernel checking.
No proof term is taken on trust, and no full term elaborator is retained in the tactics'
implementation. This also keeps the delivery's axiom audit inexpensive.
No file limit was raised and no proof was moved to another file.

Validation: the full module passes the combined compilation and axiom audit. Its
original public theorem signature and all six moved declaration blocks match verbatim.

## Second reading by P4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
