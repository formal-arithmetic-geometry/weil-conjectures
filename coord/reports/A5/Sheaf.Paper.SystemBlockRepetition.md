## What changed

Filled the combinatorial, ring-identification, ordinary functoriality, scalar-restriction,
and open-slice exactness proofs in `Sheaf.Paper.SystemBlockRepetition`. The constructions and
public mathematical statements are unchanged. Private proved helpers establish reindexing of
coefficient functors, section-ring presheaves, pushforward exactness, and composition and
scalar-restriction identities. Exactness uses the actual vertical sequence topology:
restriction is continuous and cocontinuous, so the underlying abelian sheaf functor preserves
finite limits and colimits, and the module forgetful functors reflect them.

The first-endpoint, geometric-existence, derived-coherence and open-extension declarations
retain their original named holes. No intermediate statement or new hole is introduced.

## Proved and sorry left

Closed 11 of the original 19 holes (all names below are in
`WeilConjectures.SemilinearSections`):

- `systemBlockMap_endpoints`
- `SystemBlockMap.firstMonotone`
- `blockSite_continuous`
- `SystemBlockMap.comp_finite`
- `blockRepeatRing`
- `blockEndpointRing`
- `blockRepeat_comp`
- `blockRepeat_id`
- `blockRepeat_restrictScalars`
- `blockOpenRepeatRing`
- `blockOpenRepeat_exact`

Eight original holes remain, all attached to
`lem-pur-system-block-repetition`:

- `systemBlockRepetition`
- `blockDerivedComparison_normalization`
- `blockDerivedComparison_adjunction`
- `blockCoefficientComparison_naturality`
- `blockDerivedComparison_comp`
- `blockDerivedComparison_id`
- `systemBlockGeometry`
- `blockRepeat_extensionByZero`

Holes added: zero. Split-off statements: zero. This is a partial proof delivery, not a
claim that the whole block-repetition node is proved.

## No longer needed

Removed these private proof imports, which none of the completed proofs needs:

- `Sheaf.CategoryTheory.KInjectiveDerivedMapComputation`
- `Sheaf.CategoryTheory.ExactSquareDerivedCounit`
- `WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution`
- `Mathlib.CategoryTheory.Adjunction.Basic`

Their mathematical inputs remain in the plan for the original unfinished declarations.
No node or module is withdrawn. The proofs use the planned actual ringed sequence-site
constructions. The unproved portions retain their original mathematical dependencies;
no unfinished parent or blueprint-unit route is bypassed.

## Where the brief, the DAG or earlier work was wrong

The supplied generic exact-square counit statement requires strict equalities of the
ordinary functors, whereas `blockDerivedComparison_adjunction` supplies natural
isomorphisms. A future proof must explicitly transport the generic statement or use
mate calculus; it cannot directly apply that theorem as the docstring suggests.
The first-endpoint and geometric packages remain unchanged, rather than weakening their
section-normalization clauses.

## Second reading by A5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
