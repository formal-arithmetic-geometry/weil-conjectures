## What changed

The original signature and public import of `diagonalEtaleInverseDeformation` are
unchanged. Its proof now obtains a Cartesian-centre span for each restricted etale
map, applies the two Endpoints clauses and the NormalizedBase clause of
`SectionRestriction.coherence`, identifies the source and normal composites, and
cancels the common smooth-source delta. Uniqueness identifies the two existing
presentations of delta. The final argument performs the categorical cancellation
explicitly.

`DiagonalEtaleFactorization` constructs the actual two smooth section pairs and
their base square and proves `centreSpan_nonempty` by deleting off-diagonal sheets.
The maps of the span are geometric maps, and its only factorization field is an
equality of ambient scheme maps. No cohomological comparison is a field.
`DiagonalEtaleSourceEndpoint` identifies the source endpoint using ordinary
restriction composition and uniqueness of counit-normalized locality for arbitrary
N. `DiagonalEtaleNormalEndpoint` proves the normal exchange identity by identifying
restriction along a section-pair isomorphism with inverse smooth exchange. It then
pastes the actual normal squares, using Rees composition to identify their maps.
It has no delta, orientation, coefficient twist or dualizing comparison square.
All three are new modules. No other existing module or shared interface is changed.
The endpoint files compile cleanly in 13.5 s (source) and 17.1 s (normal); the
geometric factorization compiled in 7.4 s in its profiler check. All temporary
profiler options have been removed. The assembled theorem compiled in 16.0 s;
the two unused simp arguments reported in that run have been removed. The final
delivery command recompiles and checks the completed packet.

## Proved and sorry left

The single original hole is replaced by a proof of
`WeilConjectures.PurityFiniteSetting.diagonalEtaleInverseDeformation` from the
stated section coherence and endpoint declarations. New proved declarations are
`DiagonalEtaleComparison.centreSpan_nonempty` and
`DiagonalEtaleComparison.span_source_endpoint`, with private restriction and
normalized-locality helpers.

`DiagonalEtaleComparison.span_normal_endpoint` is also proved, including its
private `isoSquare_exchange` and `normal_span_map` helpers. One original hole is
closed, zero holes are added, and zero holes remain in all four delivered modules.
No split-off sorry statement remains. Existing section-coherence dependencies may
still contain their own holes, as permitted by this stage. No data construction or
private declaration has a hole.

## No longer needed

No existing Lean import or module is withdrawn. No source-library declaration is
removed or altered. The original item had only its statement's public import;
that import remains verbatim.

The original DAG listed direct normalization dependencies on
`FiniteEtaleDualizingNormalization`, `TensorMateEtalePrecomp`, or
`EtaleCompactSupportNormalization`. The source endpoint now handles those steps.
They remain transitively needed. The actual Rees construction in
`DiagonalEtaleSectionComparisons` remains needed by the normal endpoint.
No global pruning of those modules is claimed. The original DAG's direct proof
edges are replaced by the centre-span and endpoint edges and section coherence;
`thm-pur-dnc-invariance` remains directly used for uniqueness of delta.

## Where the brief, the DAG or earlier work was wrong

The planned geometric shrinking is essential: sourceLift itself does not have a
Cartesian centre square when the etale map has multiple sheets. The proof constructs
the open complement explicitly, rather than using sourceLift as an EtaleMap of
section pairs. The source restriction formula is functorial without a Cartesian
centre hypothesis, which permits cancellation through that span.

The earlier plan did not state the endpoint identification lemmas. The new source
lemma supplies its one-endpoint step, including compatibility with arbitrary N;
the proved normal lemma supplies only its zero-endpoint step. Neither is the
original delta naturality assertion renamed. The unit route is retained. Empty
schemes, empty opens and dimension zero require no excluded cases in these
arguments. No mathematical false statement was found.

## New nodes

`lem-pur-diagonal-etale-cartesian-centre-span` records the explicit geometric
factorization and its proved existence. Its module also names the actual diagonal
pair, base pair and base square. It follows diagonal-dualizing Step 1 and
orientation-charts Steps 1--3, using the existing chartGeometry construction.

`lem-pur-diagonal-etale-span-source-endpoint` records the source-only comparison.
The proof uses existing ordinary restriction functoriality, the normalized
adjunction comparison, and smooth section exchange, following the same source
steps. LeanFinder and LeanSearch found no exact comparison theorem; Loogle supplied
categorical cancellation, and Mathlib/project grep located the reused API.

`lem-pur-diagonal-etale-span-normal-endpoint` records the proved normal-only
exchange comparison, following the zero-fibre Rees calculation and smooth exchange
pasting in those steps. The isomorphism exchange identity is derived from the
existing restriction/base-change square and pullback unit naturality. Its docstring
gives the complete argument and explains
why the actual Rees map, rather than a chosen bundle isomorphism, is involved.
No change record is required: all additional modules and nodes are new, and no
existing definition or statement changes.

## Second reading by W5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
