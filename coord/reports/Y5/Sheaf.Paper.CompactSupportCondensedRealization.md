## What changed

Proved continuity and functoriality of the finite and algebraic-closure coefficient
maps. Their ring-sheaf maps are postcomposition on continuous functions; forgetting
to internal abelian sheaves retains the ring-morphism structure. The finite-valued
condition uses the image intermediate field, finite by the source field equivalence.
All declaration signatures and public imports are unchanged.
The shift predicate explicitly reuses supplied instances and names the same composite
shift structures; its signature and mathematical clauses are retained.
Change record: `coord/changes/Y5-compact-support-shift-instances.md`.
No new module, node, or unproved statement is introduced.

## Proved and sorry left

Original holes: 33. Holes closed: 8. Holes added: zero. No decomposition.
The declarations are in `WeilConjectures.CompactSupportCondensedRealization`,
except `WeilConjectures.compactSupport_condensedRealization`.

Closed:

- `coefficientEmbedding_continuous`
- `fieldMap_isMonHom`
- `omegaEmbedding_continuous`
- `omegaEmbedding_finiteValued`
- `omegaMap_isMonHom`
- `fieldMap_id`
- `fieldMap_comp`
- `omegaMap_comp`

Remaining original holes, all attached to
`lem-pur-compact-support-condensed-realization`:

- `fieldExtension_flat`
- `omegaExtension_flat`
- `integralSupport_additive`
- `integralSupport_linear`
- `base_noetherian`
- `base_dimension`
- `base_primeUnit`
- `scalarModelTransport_subsingleton`
- `scalarModelTransport_nonempty`
- `sectionFieldMap_existsUnique`
- `realizedCoefficient_square`
- `encodingDerived_isEquivalence`
- `encodingRestriction_existsUnique`
- `encodingScalarMap_isIso`
- `fieldScalar_preserves`
- `omegaScalar_preserves`
- `finiteProjection_isIso`
- `omegaProjection_isIso`
- `omegaSupport_preserves`
- `compactification_open_quasiCompact`
- `fieldConstructible_shiftStable`
- `systemRefinement_id`
- `systemRefinement_comp`
- `omegaRefinement_isIso`
- `compactSupport_condensedRealization`

## No longer needed

No imports, nodes or modules are withdrawn. The original reconstruction, scalar,
projection and refinement route is retained for the remaining holes.

## Where the brief, the DAG or earlier work was wrong

No statement is changed or disputed. Continuity follows directly from the
finite-dimensional linear-map theorem. The internal coefficient identities follow
from pointwise postcomposition. Larger geometric, exactness and scalar-transport
proof drafts were not retained in this packet because the complete file repeatedly
exceeded the remote compiler's 60-second bound; no extra closure is claimed for them.

## Second reading by Y5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
