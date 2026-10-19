## What changed

Closed both holes in `Sheaf.Paper.SfScalarExtensionComposition`, preserving every
public signature and definition. The normalized ordinary-to-completed comparison
restricts `scalarCompletion` to intrinsic integral objects; good K-flat resolutions
and naturality prove uniqueness. Generic fully faithful cancellation gives the
normalized integral composition and unit comparisons.

Proved the ordinary tensor unit laws and pentagon using inverse formulas on
sheafification generators. Transported these laws through the existing exact-functor
derived comparisons, conjugated by the normalized completion maps, and localized
the resulting integral equations. Explicit heterogeneous transport handles the
published rational scalar functors' specified object equalities.

Added private proved helpers and proof-only imports of
`IntegralOperationsScalarComparisons`, `TensorColimitsIndependentCoefficients`,
and `WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate`.
All are used. The complete item compiled without errors or warnings in 36.1 seconds
(`scratchpad/combined6.log`). Local irreducibility keeps chosen coefficient functors
from unfolding; generic derived-composition instances are confined to their section.
The command changes and unchanged consumers are recorded in
`coord/changes/A6-scalar-composition-proof-context.md`.

## Proved and sorry left

Closed:
- `WeilConjectures.sfIntegralOrdinaryComparison_existsUnique`.
- `WeilConjectures.sfRationalScalar_coherence`.

Two of the two current repository holes closed. Zero holes added or split off.
No `sorry` remains in the item. Existing dependency theorems, including
`scalarCompletion_existsUnique` and the ordinary associator/unit existence theorems,
remain the stated dependencies; their proofs are not part of this delivery.
The new DAG record attaches an already existing theorem and adds no Lean declaration.

## No longer needed

Removed the redundant proof imports `Sheaf.Paper.SfIntegralConstructibleTriangulated`
and `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`; their declarations
are already available transitively. Their simultaneous removal compiled successfully
(`scratchpad/pruned-imports.log`). The proof still uses intrinsic isomorphism stability
and K-flat resolutions, so these modules are not pruned from the targets’ import closure.
All existing public imports retain the published statement interface.

The direct DAG proof no longer invokes `lem-pur-derived-change-of-rings`,
`lem-weil-pbc-ringed-topoi-derived-tensor-pullback`, or
`def-pur-sheaf-tensor-product` to construct a fresh derived associator. The existing
ordinary tensor comparisons and the exact-functor derived-coherence API suffice.
These results remain below the retained legacy declarations; no claim is made that
they leave the targets' import closure. Removed the obsolete top-level
`tool_uses` approval for `lem-weil-pbc-ringed-topoi-derived-tensor-pullback`.
`lem-weil-finite-free-completed-scalar-comparison` remains needed below the normalized
completion dependency, instead of being a direct invocation here.

## Where the brief, the DAG or earlier work was wrong

The inherited K-flat resolution call had incorrect explicit universes; coefficient,
site object and site morphism universes are `{u+1, u+1, u}`. Uniqueness also needed
an explicit mapped isomorphism for cancellation and direct naturality equations.
Duplicate local irreducibility assignments were rejected by Lean and removed.
Derived-composition instances must be scoped to the generic coherence section to
avoid expensive inference through the chosen coefficient constructions.

The global normalized completion theorem was already declared as
`WeilConjectures.scalarCompletion_existsUnique` inside the broader
`lem-pur-integral-operations-scalar-extension` attachment. That larger node has this
composition node as a statement dependency because it also states operation tower
coherence. Citing the whole package here would create a false DAG cycle although the
selected Lean declaration is independent of composition. The new node records only
that existing normalization result, with its independent proof dependencies; no
result is restated or weakened. The owning node now follows the implemented proof.
The original unit route is retained.

The first dry run required a command-change record, now supplied. Later diagnostic
compiles intermittently exceeded 60 seconds, including the appended axiom scan; the
latest full delivery compile and probe passed. Preflight then required removing
`lean.file` from the new existing-declaration attachment, which delivers no Lean file.
That metadata error is corrected. The full dry run then passed at `6a9dbffcf6`
(`scratchpad/dryrun-metadata.log`). Nothing was pushed by these dry runs.

## New nodes

`lem-weil-normalized-scalar-completion` records the already stated unique global
ordinary-to-completed natural transformation, normalized on good representatives
and invertible on derived-complete inputs. Its Lean attachment is the existing
`WeilConjectures.scalarCompletion_existsUnique` in
`Sheaf.Paper.IntegralOperationsScalarComparisons`; no new module or hole is added.
Its source is Bhatt--Scholze Proposition 3.5.1 and Lemma 6.8.2(1), as expanded in the
blueprint composition proof. The command-change record is
`coord/changes/A6-scalar-composition-proof-context.md`.

## Second reading by A6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
