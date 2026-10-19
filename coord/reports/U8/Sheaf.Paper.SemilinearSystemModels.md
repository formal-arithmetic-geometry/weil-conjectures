## What changed

Proved eight foundation and comparison theorems in
`Sheaf.Paper.SemilinearSystemModels`, without changing any existing signature or definition.
Added proof-only imports of `Mathlib.CategoryTheory.Comma.StructuredArrow.Small` and
`Mathlib.CategoryTheory.Sites.CoverPreserving`. Kept the existing smallness parameter of
`evaluation_continuous` for API compatibility; its proof does not need it, so only that
declaration disables the unused-section-variable linter.

Smallness uses the supplied witness, a product of small-model equivalences, and the induced
slice equivalence. Continuity uses cover preservation and an explicit factorization of
product-category arrows to preserve compatible families. Evaluation of the ring follows
from functor extensionality and preservation of identities. Scalar restriction is exact
because its composite with the exact conservative forgetful functor is the unchanged
abelian sheaf. Restriction composition uses the actual sectionwise scalar-restriction
isomorphisms and tower composition; its uniqueness is proved on sections. The ring-system
map is obtained from `NatTrans.ofOpSequence`, whiskering and uncurrying, and is uniquely
specified by its components. These arguments apply also to empty sites, zero coefficient
rings, equal indices, and arbitrary nonflat coefficient maps.

## Proved and sorry left

Closed eight of the original twelve holes, all in namespace
`WeilConjectures.SemilinearSections`:

- `siteSmall`
- `sequenceSmall`
- `sliceSmall`
- `evaluation_continuous`
- `evaluation_ring`
- `res_exact`
- `restrictionComposition_existsUnique`
- `systemMap_existsUnique`

Added zero holes; no decomposition or new nodes. Four existing holes remain, all attached
to `def-coef-semilinear-system-models`:

- `WeilConjectures.SemilinearSections.ringPresheaf_isSheaf`
- `WeilConjectures.SemilinearSections.evaluation_exact`
- `WeilConjectures.SemilinearSections.transition_exists`
- `WeilConjectures.SemilinearSections.restrictionEvaluation_existsUnique`

Their existing source citations and complete proof descriptions are retained.

## No longer needed

None. No existing imports, nodes, or modules are pruned. The existing node has no numbered
proof plan or proof dependencies; the proofs use the already imported module operations
and Mathlib. No additional project proof dependency is introduced.

## Where the brief, the DAG or earlier work was wrong

The shared checkout temporarily lacked the assigned source file during an update; it
subsequently appeared and was copied without modifying the repository. One remote compile
received no answer within 200 seconds; later retries returned compiler diagnostics.
The mathematical statements and the blueprint unit route are unchanged.

## Second reading by U8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
