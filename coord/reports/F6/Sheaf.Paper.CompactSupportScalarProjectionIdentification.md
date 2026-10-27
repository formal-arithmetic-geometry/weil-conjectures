## What changed

Proved `WeilConjectures.PurScalarProjection.scalarCompletion_existsUnique`.
The fully proved `WeilConjectures.integralScalarCompletionUnitComparison` supplies
existence and the actual completion-unit equation. Its proof uses the existing
finite-free quotient/Roos exchange for the actual completed coefficient map.
The fully proved `WeilConjectures.principalIntegralCompletionComparison` identifies
each supplied principal quotient completion with `IntegralOnSlice.completion`,
preserving its unit on good K-flat representatives and then every derived object.
Conjugating the exchange gives the actual isomorphism and unit equation.
The actual completion-reflector Hom injection proves uniqueness.

The scalar normalization component is split into
`Sheaf.Paper.CompactSupportScalarCompletionNormalization`: the existing public
`scalarCompletion_existsUnique` and `scalarCompletion`, with their proved private
reflector and scalar naturality helpers. Every public signature and chosen-map
definition body is unchanged. The item publicly imports this component, preserving access to every original declaration.
Completed tensor balancing, its naturality and unit helpers, and the proper/open,
support and main comparison declarations remain in the item.

Only the item, its own DAG node, three new proved modules and their nodes, and
the module-split change record are changed. The DAG's Step 8 and Lean attachments
follow this organization. The parent gains only the structural statement dependency
on the moved definitions; no mathematical statement or target is changed.

The argument includes the identity coefficient extension, ramified extensions,
the zero complex and the empty scheme. It assumes neither completeness nor
constructibility of its input; no extra hypothesis was introduced.

## Proved and sorry left

Closed one of the five original holes:
`WeilConjectures.PurScalarProjection.scalarCompletion_existsUnique`.
It is now in the new normalization module with the same public name and type.

Four original holes remain unchanged in the item, all attached to
`lem-pur-compact-support-scalar-projection-identification`:

- `WeilConjectures.PurScalarProjection.openProjection_existsUnique`
- `WeilConjectures.PurScalarProjection.realization_existsUnique`
- `WeilConjectures.PurScalarProjection.native_scalar_identification`
- `WeilConjectures.PurScalarProjection.gamma_identification`

No holes were added or split off. Both new comparison theorems and all new
private helpers are proved. Profiling identified repeated unfolding of concrete
derived-functor choices during categorical rewriting. Abstract categorical helpers
supply those calculations, and the representative comparison, scalar existence
construction and existing scalar normalization component have separate modules.
The remaining item proofs use local irreducibility for the large completed
projection, tensor balancing and support-map definitions, consuming their stated
unit and naturality equations instead of repeatedly unfolding their construction.
These attributes are local to the file. The compile-time limit and all shared
definitions are unchanged.

## No longer needed

No existing module or node is withdrawn. The remaining holes retain the original
proper/open and strict-system route. The scalar proof's finite-free, quotient/Roos
and principal-completion imports are used in the new scalar-existence module;
those dependencies remain needed transitively. The normalization component uses
the existing general OpenRoos reflector proof. The original
`CompletedIntegralFiniteFree` proof import remains needed in the item for its
`integral_ramification` helper in `ordinaryCompletedSquare`.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement correction was needed. The live item source exists;
the historical rework quarantine entry was not interpreted as a withdrawal.
There are five starting holes in the live module. The existing finite-free
exchange applies to normalized principal quotient models, so its application
requires explicit unit-preserving transport to the specified actual completion;
identifying only their complete loci would not establish the required equation.

## New nodes

`lem-pur-integral-principal-completion-comparison`, in
`Sheaf.Paper.IntegralPrincipalCompletionComparison`, proves a unit-preserving
isomorphism from any supplied principal quotient completion to the actual integral
completion on each derived input. It is a one-coefficient representative argument.
Its source is the normalized quotient/Roos comparison already proved in
`CompletedIntegralPrincipalUnitCriterion`, with naturality and cancellation proved
here. Its local `letI` values fix canonical site and sheafification instances;
they add no assumptions.

`lem-pur-integral-scalar-completion-unit-comparison`, in
`Sheaf.Paper.IntegralScalarCompletionUnitComparison`, proves existence of the
scalar/completion isomorphism with the actual unit equation. It uses finite
freeness, the ramification equation, exact products, the existing quotient/Roos
exchange and the preceding representative comparison. Its local `letI` values
likewise fix canonical instances without adding assumptions.

`lem-pur-compact-support-scalar-completion-normalization`, in
`Sheaf.Paper.CompactSupportScalarCompletionNormalization`, houses the two moved
public scalar normalization declarations. It combines the preceding existence
result with the actual completion reflector to prove uniqueness and retains the
original chosen scalar comparison and scalar isomorphism-naturality proof. Its Lean attachments replace the moved entries in the parent.

All three modules are fully proved and add zero holes. The structural split is
documented in `coord/changes/F6-scalar-completion-module-split.md`. No other existing
module is changed; a direct-importer search found no current Lean importers of
the item. Its DAG parents and unit route are retained.

## Second reading by F6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
