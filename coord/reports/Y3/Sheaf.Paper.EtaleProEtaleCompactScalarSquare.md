## What changed

Implemented the scalar/site mate-pasting part of
`AlgebraicGeometry.ProEtale.CoefficientCompatibility.transportedCompactScalar_site_square`
in `Sheaf.Paper.EtaleProEtaleCompactScalarSquare`, with its statement unchanged.
The private helper `compactComparison_inv` identifies the prescribed compact-support
comparison with the proper ambient counit mate followed by the open comparison.
`fixedCompactScalar_site_square` pastes the existing proper scalar mate square with
the already proved unbounded open scalar/site square, using naturality on both sides.
It uses the exact-open boundedness lemmas and identifies the published etale open
scalar factor by `compactScalarOpen_eq`.

Isolated the original plan's Step 3 in the new module
`Sheaf.Paper.RecordedCompactScalarNormalization`. Its theorem identifies the genuine
transport of the recorded intrinsic map with the fixed-module proper/open composite,
as natural transformations on the entire pro-etale derived category. This is an
independent presentation-normalization problem: no etale-origin object, lower bound,
compact-support site comparison, or scalar/site square occurs in its conclusion.
The main theorem rewrites by this normalization and applies the implemented square.
All three existing public imports are retained. Added proof imports supply comparison
normalization, the included proper mate, the unbounded open square, the etale open
normalization and boundedness lemmas, the proper scalar mate, and the new normalization.
No existing external module or public interface was changed. A proved local instance
pins the pro-etale site's size; explicit functor equations normalize the D+ inclusion
factors without changing any shared definition or transparency setting.

Validation: both delivered Lean modules compile through `lcompile.py`, with no errors
or warnings. The final item compile took 13.6 seconds; the normalization module's
last compile took 54.0 seconds. The original theorem statement was compared verbatim
against the repository source. The two node records have existing dependencies and
their `proof_deps` equal the union of their proof steps' `uses`.

## Proved and sorry left

One original hole is closed:
`AlgebraicGeometry.ProEtale.CoefficientCompatibility.transportedCompactScalar_site_square`
(node `lem-sp-transported-compact-scalar-site-square`). Its combining proof and the
private helpers have no sorry.

One hole is added and remains:
`AlgebraicGeometry.ProEtale.CoefficientCompatibility.recordedCompactScalar_fixed_normalization`
(node `lem-sp-recorded-compact-scalar-fixed-normalization`). Its complete natural-language
normalization argument is in the declaration docstring and its node. This delivery is
a decomposition (one hole closed, one added), not a net hole reduction. The item has
zero textual holes after the change; the new module has one.

## No longer needed

No existing imports were removed and no module is withdrawn or claimed globally
unnecessary. The node's direct proof dependencies no longer repeat the lower-level
ingredients already encapsulated by the proved open-square and comparison APIs:
`lem-weil-pbc-extension-by-zero-exact`, `lem-coef-etale-open-comparison-data`,
`lem-weil-pbc-comparison-direct-image-canonical-mate`,
`lem-weil-pbc-exact-functor-bounded-below`,
`lem-sfb-etale-proetale-scalar-pullback-cube`,
`lem-sf-open-comparison-unit-normalization`, `lem-weil-pbc-mate-pasting`,
`lem-sf-comparison-pullback-exact`, and
`lem-cbc-proetale-extension-zero-comparison`.
These are not declared obsolete: the existing proved APIs can still depend on them.

The intrinsic realization dependencies
`def-sp-et-proet-coefficient-transport`, `def-sp-reduction-direct-image-comparison`,
`lem-sf-compact-support-restriction-of-scalars`, `lem-trf-open-square-exchange`,
`def-weil-proetale-inverse-image`, and `lem-weil-pbc-mate-pasting`
are retained in the new normalization node rather than repeated as direct dependencies
of the scalar/site pasting proof. The unit route and statement dependencies are preserved.

## Where the brief, the DAG or earlier work was wrong

The open scalar/site public theorem advertises a bounded flat representative, but
its already proved private helper `OpenScalarSite.scalar_site_square_aux` holds for
every unbounded input. Using it avoids adding an unwarranted finite Tor-amplitude
hypothesis or a replacement-resolution obligation. The existing `sp_comparison_hom`
and `compactSupportComparisonNormalization` also provide the inclusion-normalization
bridge needed by the plan. No mathematical statement was changed or disputed.

The realization lemmas `realizationScalar_directImage_mate` and
`fixedOpenScalar_realization_transport` were inspected. They normalize scalar
transposes using `realizationScalarIso` and the sectionwise intrinsic direct-image
model, whereas the recorded arrow here uses `scalarPresentation`,
`directImagePresentation`, and the tensor-coordinate geometric mate. They do not
immediately state the remaining equality of these prescribed presentations.

## New nodes

`lem-sp-recorded-compact-scalar-fixed-normalization`, in
`dag/nodes/sec-smooth-purity/lem-sp-recorded-compact-scalar-fixed-normalization.json`,
is precisely the original Step 3: normalization of the recorded intrinsic coefficient
arrow under realization, on the pro-etale category alone. Its source is the proper/open
factorization in Stacks Tag 0GL6 together with the original agent-written normalization
argument; it does not claim that the full normalization is stated in that tag.
Blueprint searches found no separate statement of the presentation normalization;
the new node retains the original item's Charts ancestor, `det-sp-reduction-exceptional`.
LeanFinder, LeanSearch, Loogle and Mathlib/project grep searches found generic mate
calculus and module scalar adjunctions, but no theorem for these particular presentation
maps. Zero rings, empty schemes, identity coefficients and unbounded inputs are included
by the same adjunction identities. No change record is required: existing signatures,
definitions, attributes and public imports are unchanged.

## Second reading by Y3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
