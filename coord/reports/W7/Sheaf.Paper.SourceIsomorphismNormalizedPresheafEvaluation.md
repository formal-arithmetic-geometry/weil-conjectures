## What changed

Filled `sourceIsomorphism_normalized_presheaf_evaluation` without changing its statement
or `etaleIsomorphismNormalizationArrow`. Transport the specified presheaf map to slice
sites, reflect its generator equation through the etale localization equivalences, and
express that equation as equality of two actual maps to the mixed-coefficient Hom
presheaf. Sheafify and apply comparison inverse image. Naturality of Hom evaluation,
compatibility with the Isom-to-Hom projection, and coefficient-restriction evaluation
give the slice square. Canonical coefficient-mate pasting then transports the square
back to source sites.

Added four lower modules: `Sheaf.Paper.DerivedRestrictionHomPresheaf` constructs the
coefficient-restriction map and proves its naturality;
`Sheaf.Paper.DerivedHomRestrictionEvaluation` proves its evaluation compatibility.
`Sheaf.Paper.DerivedHomEvaluationFunctoriality` proves ordinary evaluation naturality
and compatibility with Isom-to-Hom;
`Sheaf.Paper.ProEtaleNormalizationSquareTransport` constructs the slice comparison
normalization arrow and proves transport of its squares to source schemes.
These constructions use the actual derived functors, localization comparisons, and
specified comparison adjunctions. No arbitrary normalization or comparison data is
chosen. No other existing Lean module or node is changed.

The private localization and ordinary evaluation calculations reuse the arguments in
`NormalizedDerivedIsomorphismTransport`, `DerivedMorphismWeaklyContractibleEvaluation`,
and `DerivedScalarExtensionLocalSystems`. Those higher modules already reach this item,
so importing them here would form an import cycle. The lower generic exact-functor
pasting lemmas are imported instead. All of the local calculations are proved here.
Private local instance caches reuse the
existing sheafification-existence proofs to avoid repeating expensive site-instance
searches; their scope ends before the public theorem. The command-scope advisory
from preflight refers to these private helper sections and local instance attributes;
no public instance, notation, signature, or import is added to the existing item interface.

Validation after extraction: all five Lean files compile without warnings through
`lcompile.py --all`. The item took 37.7 seconds, pro-etale transport 26.6 seconds,
and evaluation functoriality 8.9 seconds; every file is below 60 seconds.

The original theorem signature and normalization-arrow definition were compared with
the shared source and are unchanged.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.sourceIsomorphism_normalized_presheaf_evaluation`
(node `lem-weil-pbc-source-isomorphism-normalized-presheaf-evaluation`).

Also proved `CategoryTheory.derivedRestrictionHomPresheaf_natural` and
`AlgebraicGeometry.Scheme.derivedHomEvaluation_restrictScalars` and constructed
`CategoryTheory.derivedRestrictionHomPresheaf` and
`AlgebraicGeometry.Scheme.sliceComparisonNormalizationArrow`. Also proved
`AlgebraicGeometry.Scheme.derivedHomEvaluation_natural`,
`AlgebraicGeometry.Scheme.derivedIsoEvaluation_hom`, and
`AlgebraicGeometry.Scheme.sourceSliceNormalization_transport`. Added zero holes; no `sorry`
remains in any delivered module. This is a proof, not a decomposition into new obligations.

The assertions do not require finite coefficient rings, a universal normalization
arrow, or bounded/perfect/lisse objects. Identity coefficient maps, zero coefficient
rings, and empty weakly contractible objects are included: the argument uses functorial
composition, equivalences, and the existing unit bijections without excluding them.

## No longer needed

No original import or declared dependency is removed, and no module is withdrawn.
The general scalar-extension adjunctions, finite-coefficient reduction existence
results, and local-existence/cover arguments are not needed for this preservation
statement. They are not imported. The unit's own route is unchanged.

## Where the brief, the DAG or earlier work was wrong

The original three-step mathematical plan is sufficient. Its reference to a
mixed-coefficient Hom presheaf required making the actual coefficient-restriction map
and the canonical comparison square explicit. The delivery supplies and proves these
interfaces rather than introducing another version of the normalized Isom obligation.

A direct import of the existing transport or general evaluation module is impossible:
`import_direction.py may` reports that each already reaches the assigned item.
The private calculations below their finiteness-dependent APIs avoid that cycle.

The first complete proof compiled in 60 seconds with profiling, and in 44.8 seconds
after caching existing sheafification instances and removing diagnostics. Delivery
then measured 77 seconds and refused the file. After these optimizations, the already
proved evaluation and pro-etale transport calculations were extracted into separate
modules. This is a compilation-time split, with no new mathematical obligation.

## New nodes

`def-weil-pbc-restriction-hom-presheaf` records the explicitly constructed restriction
map on local derived Hom presheaves and its proved naturality. Its module is
`Sheaf.Paper.DerivedRestrictionHomPresheaf`.

`lem-weil-pbc-derived-hom-restriction-evaluation` records the proved compatibility of
that Hom map with weakly contractible evaluation, with the canonical comparison and
slice coefficient isomorphisms displayed in its statement. Its module is
`Sheaf.Paper.DerivedHomRestrictionEvaluation`. It has no normalized arrows, specified
Isom-presheaf map, or generator equation as hypotheses.

`def-weil-pbc-slice-comparison-normalization-arrow` records the concrete slice arrow,
and `lem-weil-pbc-proetale-normalization-square-transport` records its proved transport
property in `Sheaf.Paper.ProEtaleNormalizationSquareTransport`.

`lem-weil-pbc-derived-hom-evaluation-naturality` and
`lem-weil-pbc-derived-isomorphism-evaluation-hom` record the two proved functoriality
properties in `Sheaf.Paper.DerivedHomEvaluationFunctoriality`.

## Second reading by W7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
