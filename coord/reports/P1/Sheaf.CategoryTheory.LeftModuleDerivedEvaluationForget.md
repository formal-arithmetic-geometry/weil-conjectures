## What changed

Proved both original theorems in
`Sheaf.CategoryTheory.LeftModuleDerivedEvaluationForget`, retaining every existing
signature, definition and public import.

`CategoryTheory.LeftModuleDerivedEvaluation.abelianInverseExact` reflects finite
limits through underlying-set sheaves and obtains colimits from the abelian
inverse-image adjunction. Preservation of binary products gives additivity.

`CategoryTheory.leftModuleDerivedEvaluationForget` now proves all five clauses.
The comparison is an isomorphism by the existing injective-module abelian
acyclicity theorem, the cohomology/right-derived sections identification, and the
right-acyclic base-change criterion. The injective-complex clause uses the
acyclic-complex unit criterion. Restriction compatibility follows from
right-derived uniqueness and the unit factorization. The global section maps
are constructed explicitly from maps out of the terminal constant sheaf:
product preservation and `abelian_addition` give additivity, and
`scalar_compatibility` gives linearity for arbitrary, possibly noncommutative,
rings. Their forgotten square commutes by `moduleSetIso_compatibility`.
The existing derived cube theorem and derived identity unit laws then give
global pullback compatibility. Applying homology gives the last clause.

Added proof imports
`WeilConjectures.CategoryTheory.Sites.InjectiveModuleAbelianAcyclic` and
`WeilConjectures.CategoryTheory.Sites.CohomologyRightDerivedSections`.
All new helpers are private and proved. No definitions were extracted into
another module. The node's proof, dependencies and proof origin follow this
completed proof. Existing public declarations and their signatures, definition
bodies, instances and public imports are unchanged. Preflight conservatively
classifies the added local proof commands as an interface change; they are
documented in `coord/changes/P1-left-module-evaluation-proof-context.md`, with
the direct importer census and the reason no consumer adaptation is needed.

## Proved and sorry left

Closed 2 of 2 original holes:

- `CategoryTheory.LeftModuleDerivedEvaluation.abelianInverseExact`.
- `CategoryTheory.leftModuleDerivedEvaluationForget`.

Both belong to `lem-pe-left-module-derived-evaluation-forget`.
Holes added: zero. Holes remaining in the delivery: zero. Split-offs: zero.
This is a proof from existing declared dependencies, not a decomposition.
The retained module compiled cleanly through `lcompile.py` in 24.3 seconds
against the current published library.

The normalized global maps use actual constructions, with no data selected
from an unproved existence theorem. The construction works for the zero ring
and noncommutative rings. The geometric clause assumes terminal objects;
it places no demand on sites without one. No injectivity after scalar
forgetting is asserted or used.

## No longer needed

Removed proof imports:

- `WeilConjectures.CategoryTheory.Abelian.RightDerived.LongExactSequence`.
- `Sheaf.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses`.
- `Sheaf.CategoryTheory.ModuleAbelianEvaluationComparison`.

Pruned direct proof dependencies
`lem-weil-pbc-dplus-injective-representative`,
`lem-weil-pbc-ring-sheaves-grothendieck`,
`lem-weil-pbc-ringed-site-module-abelian-evaluation-comparison`, and
`def-sp-injective-resolutions`. The general right-acyclic base-change and
acyclic-complex unit APIs perform the resolution argument; the already stated
injective-acyclic specialization and cohomology/right-derived identification
replace the objectwise comparison as direct tools. Removed the corresponding
three obsolete top-level `tool_uses` entries. The generic Leray acyclicity tool
remains needed through the acyclic-complex unit API, and the derived cube
remains needed for geometric global pullback. No unit statement or step is
bypassed.

The earlier proposed Setup extraction and global-only split were never
delivered. Their archived text in `scratchpad` is not part of the delivery;
there are no new modules or nodes.

## Where the brief, the DAG or earlier work was wrong

The retained report described an obsolete two-module decomposition, although
the sandbox's actual Lean file already contained a complete consolidated proof.
It has been replaced with this account of the compiled delivery. The original
plan's explicit injective representative and integer-ring Grothendieck steps
are unnecessary with the available right-derived APIs. The new direct tools
are the existing arbitrary-site injective-module acyclicity theorem and
cohomology/right-derived sections identification, not geometric comparison
theorems replacing the unit's route.

The initial required dry run queued behind other deliveries for worktree
capacity. No launcher or repository tools were modified or bypassed.

## Second reading by P1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
