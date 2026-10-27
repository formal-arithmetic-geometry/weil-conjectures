## What changed

Kept the statement of `AlgebraicGeometry.Scheme.FiniteCompactScalar.openScalar_transport`
unchanged. Factored its proof through the fixed-coefficient pro-etale site comparison
and the intrinsic realization comparison. The private scalar-transpose natural
transformation supplies the naturality needed to transport the input site isomorphism;
ordinary naturality then inserts the arbitrary output isomorphism `eGB`.

Added `Sheaf.Paper.FiniteOpenScalarSiteTransport`. Its proof identifies the prescribed
fixed open scalar transpose with `OpenScalarSite.scalarOpen`, using the ordinary open
unit normalization and exact localization. It identifies the two published etale open
scalar isomorphisms and uses the already proved unbounded `scalar_site_square_aux`.
Its public import is the transport-data module needed by the statement. The proof imports
the three modules containing these lemmas privately, with `import all`
where the existing proved helper is private. No shared interface changes.

Added `Sheaf.Paper.FiniteOpenScalarRealizationTransport` for the remaining intrinsic
realization face. Updated the item's node to describe the two faces and their assembly.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.FiniteCompactScalar.openScalar_transport` by a complete
assembly proof. Proved
`AlgebraicGeometry.Scheme.FiniteCompactScalar.fixedOpenScalar_site_transport`, including
the scalar-unit normalization and the identification of the etale scalar maps.

One new hole remains:
`AlgebraicGeometry.Scheme.FiniteCompactScalar.fixedOpenScalar_realization_transport`
(node `lem-finite-open-scalar-realization-transport`). Its proof is exactly `by sorry`.
It contains only the pro-etale coefficient realization square, with no change of site
and no arbitrary etale output isomorphism. This is a decomposition: one original hole
closed and one strictly smaller hole added. No definition contains `sorry`.
No hypotheses, coefficient maps, adjunctions, or comparison normalizations were changed.

Validation: the site face and the unchanged original theorem compiled through
`lcompile.py`; the final assembly check completed without warnings in 20.8 seconds.
Profiling found less than a second of elaboration for the remaining realization
statement and a few seconds for the site proof. Temporary profiler options were removed.
Delivery runs the required final compilation and preflight on the complete packet.

## No longer needed

No original imports were removed and no module is withdrawn. The original proof's
planned direct dependency on `lem-pur-etale-scalar-mate-projection` is unnecessary:
the site face follows from the stronger unbounded theorem already proved in
`Sheaf.Paper.OpenScalarSiteCoherence`. Likewise
`lem-sf-class-compact-support-comparison` is not a direct proof dependency of the
assembly. Both may remain in the transitive statement/import closure through the
unchanged public coordinate definitions; no claim is made to prune that closure.
The open/scalar compatibility is independent of the proper-map factor and of
bounded flat representatives. No blueprint unit statement or realized step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The original proof plan did not identify the already proved unbounded helper
`OpenScalarSite.scalar_site_square_aux`. The public wrapper requests a bounded flat
representative, but its proof helper establishes the needed square without those
hypotheses. The site part therefore needs no new unproved theorem. The normalization
between the two etale scalar isomorphisms is essential and is proved explicitly.

The remaining realization statement is a genuine face of the original argument,
rather than the original equation under a different name: all etale/pro-etale site
comparisons and `eGB` have been removed, and the fixed site face is proved separately.
The reasoning uses only functoriality, adjunction units and equivalence triangles;
zero rings, empty schemes and the zero complex require no exclusions.

The first preflight identified a DAG cycle through the aggregate
`lem-sp-open-scalar-site-coherence`: that node also owns flatness and scalar/open
composition laws, whose dependencies return through completed operations to the
compact-support theorem. The proof here uses its private unbounded helper, not
those additional public assertions. Its actual proof is a mate-cube assembly of
`restriction_coefficient_cube`, `derived_coefficient_cube`, `scalar_pullback_cube`
and `comparison_derived_extension_mate`. The new site's DAG now records the lower
coefficient/site adjunction units, open unit normalization, etale scalar comparison
data and exact derived pasting inputs of those helpers directly. The aggregate
node and all of its declarations, dependencies and imports remain untouched.
The Lean module remains a proof import; this is a precise dependency record,
not a withdrawal of the aggregate or its other clauses.

## New nodes

`lem-finite-open-scalar-site-transport` records the proved fixed-coefficient site face,
with the precise lower open-unit, coefficient/site and derived-square normalization
inputs of the existing unbounded helper as proof dependencies.
Its Lean module is `Sheaf.Paper.FiniteOpenScalarSiteTransport`.

`lem-finite-open-scalar-realization-transport` records the remaining realization face,
with its full conjugation/localization/mates argument in the docstring. Its Lean module
is `Sheaf.Paper.FiniteOpenScalarRealizationTransport`.

Change record: `coord/changes/finite-open-scalar-transport-local-elaboration.md`.
This documents the static heuristic's attribute warning: the two irreducibility
attributes are local to proof elaboration and have no consumer effect. Existing
signatures, definitions, exported attributes and public imports are unchanged.

## Second reading by Y3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
