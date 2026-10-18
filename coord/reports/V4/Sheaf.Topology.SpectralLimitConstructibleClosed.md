## What changed

Proved `Topology.isCompact_limit_constructibleClosed` in
`Sheaf.Topology.SpectralLimitConstructibleClosed`, with its signature unchanged.
The proof follows Stacks Topology Tag 0A2V and the closed-equalizer argument of
Tag 08ZV: the compatible families form a closed subset of the product of the
compact Hausdorff constructible spaces. Unique realization gives a continuous
surjection onto `X`, using its initial topology. The closed subset imposing all
coordinate conditions `Z i` has compact image equal to the requested subset.
The surjection also proves `CompactSpace X`.

Added the proof-only import
`WeilConjectures.Mathlib.Topology.Spectral.ConstructibleTopology` for the already
proved `constructibleTopology_le`; the two existing proof-only imports supply
Hausdorffness and continuity of spectral maps for the constructible topologies.
All eight existing DAG steps and their stated dependencies are used. No
statement, definition, visibility, unit route, or DAG dependency changed.

Validation: server single-file compilation through `lcompile.py`; the delivery
checks also compile and probe the declarations. The search used LeanFinder for
compact Hausdorff inverse limits, Loogle for `isClosed_eq`, the remote grep
service for `constructibleTopology|continuous_iInf_rng`, and local searches in
both library roots. There is no shorter existing theorem with this statement.
The existing topology comparison lemma supplies step 2 directly.

## Proved and sorry left

Closed 1 of 1 original holes:
`Topology.isCompact_limit_constructibleClosed`
(node `lem-weil-pbc-spectral-limit-constructible-closed-quasi-compact`).
Added 0 holes and split off 0 statements. No `sorry` remains in the delivered
module. This proof uses the existing stated theorem
`IsSpectralMap.continuous_constructibleTopology`, whose proof is still `sorry`
in its separate dependency module; that existing obligation is unchanged.

## No longer needed

None. No imports, declared dependencies, nodes, or modules were removed.
The proof uses all the mathematical ingredients of the existing DAG plan;
compactness of all compatible families is established once and then reused
for the closed coordinate constraints.

## Where the brief, the DAG or earlier work was wrong

No statement error or unusable dependency was found. The existing library
already proves the elementary topology comparison in DAG step 2, under the
name `constructibleTopology_le`.

The transition identity and composition laws, original projection continuity,
and compatibility of the subsets are redundant once the compatible-family
realization and initial-topology hypotheses are given. Their binders remain
unchanged; unused-variable linting is disabled only for this declaration. No directedness or nonemptiness
is used, so empty index sets and empty spaces are covered.

## Second reading by V4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
