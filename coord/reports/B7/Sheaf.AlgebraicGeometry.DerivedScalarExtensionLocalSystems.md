## What changed

Proved `AlgebraicGeometry.Scheme.derivedScalarExtension_localSystems` in its existing module without changing its signature, public imports or definitions. The proof constructs both local systems from the canonical scalar left adjoints. It transports invertibility from source-scheme scalar mates across slice equivalences, proves restriction coherence by inverse-mate pasting, and proves the final comparison square by transposing and deriving the ordinary coefficient cube.

All additional imports serve private proofs. The added namespace/variable commands and notation scope trigger the static interface check; their exact command interfaces and all downstream users are documented in `coord/changes/derived-scalar-extension-local-systems-proof-scopes.md`. Existing public declarations and imports are unchanged, and no consumer adaptation is required. The existing scalar mate and global comparison invertibility declarations are used as the already stated dependencies intended by stage 3. The node proof and proof dependencies now record this route. No auxiliary public theorem or module is added.

## Proved and sorry left

Closed: `AlgebraicGeometry.Scheme.derivedScalarExtension_localSystems` (one original hole).

Added: zero holes. Remaining in the item: zero holes. No split statements.

The proof uses existing named theorems, including `AlgebraicGeometry.ProEtale.scalarPullbackReverse_isIso` and `AlgebraicGeometry.ProEtale.pbcComparisonReductionMap_isIso`; their proofs are outside this delivery.

## No longer needed

No original import was removed: the sole original public import supplies the statement. The node's direct dependency `lem-pur-site-restriction-module-adjunction-exact` is unused: exact source-site equivalences and their existing localization adjunctions supply the needed restriction interface. The general tensor-pullback node `lem-weil-pbc-ringed-topoi-derived-tensor-pullback` is used through the already stated scalar-mate specialization rather than reproved directly. Neither is claimed pruned from the entire targets import closure. No module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The planned chain-level K-flat argument is already encapsulated by the canonical scalar-adjoint and scalar-mate interfaces. The missing work here was their precise unit normalization and coherence. The delivered proof establishes those identities explicitly by adjunction and exact derived functor pasting; it makes no additional flatness, boundedness, nonzero-ring or nonempty-scheme assumption.

On this provider-error resumption, the dispatcher metadata reference clock changed from start `1792440004.5571177` to `1792499303.6551206` (2026-10-20 12:28:23 UTC). The worker did not change `.budget` and continued the original item and sandbox. No delivery had been attempted at that reset.

## Second reading by B7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
