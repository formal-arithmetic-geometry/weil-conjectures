## What changed

Closed the proofs of `moduleTowersKInjectives`,
`finiteSectionsRestriction_existsUnique`, `reductionAdjunction_existsUnique`, and
`counit_projection`. Added private categorical helper lemmas for the normalized
module scalar adjunction; these compile in the module and preserve all public
signatures.

## Proved and sorry left

Proved: `moduleTowersKInjectives`, `finiteSectionsRestriction_existsUnique`,
`reductionAdjunction_existsUnique`, and `counit_projection` (4 of 5 original
sorries). The remaining sorry is
`compactSupport_tower_coaugmentation`.

## No longer needed

None identified. The proof uses the imports retained in the module.

## Where the brief, the DAG or earlier work was wrong

The DAG's top proof requires a simultaneous normalized comparison between point
sections and the derived inverse limit of strict towers, and a normalized
finite-reduction comparison. The available declarations expose these only as
separate existence statements, so the final construction is still open here.

## Second reading by R3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
