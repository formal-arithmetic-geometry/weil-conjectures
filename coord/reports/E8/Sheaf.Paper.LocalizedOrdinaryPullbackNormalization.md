## What changed

Proved the actual coefficient coherence package in the new module
Sheaf.Paper.LocalizedOrdinaryCoefficientCoherence. Its Lean proof transports the
existing constant-sheaf composition and identity lemmas through the specified
finite coefficient comparisons, checks quotient transitions, proves completed
composition and identity by joint monicity, and evaluates the existing scalar
section formula. It never exchanges inverse image with an infinite limit.

The original theorem now assembles four individually normalized edges, their
composition comparison and their identity comparison. Those three independent
construction/coherence steps are isolated in their own modules, with exact
normalization predicates, sources, proof plans and DAG nodes. The original
signature, all fields and all functor definitions are unchanged.

Extracted the existing auxiliary declarations verbatim into
Sheaf.Paper.LocalizedOrdinaryPullbackData to avoid an import cycle between the
parent theorem and its new proof modules. The original module publicly imports
that data module, preserving every original declaration and public import.
Change record: coord/changes/E8-localized-ordinary-data-extraction.md.

Validation: all six packet modules compile together through lcompile.py, with no
compiler errors or warnings. The coefficient theorem uses normal transparency
settings; no new transparency override was introduced. The extracted data are
verbatim and the main theorem signature is unchanged (checked mechanically).
The data node records the structure signature before `where`, matching the
project parser. The change record lists all 296 transitive importers.
The sole direct importer, Sheaf.Paper.RationalScalarMixedUnitCancellation
(current holder E5), compiled unchanged against the packet's .lbuild outputs.
Its temporary source copy was removed, so no other existing module is delivered.

## Proved and sorry left

Original hole closed:
AlgebraicGeometry.Scheme.LocalizedOrdinary.localizedOrdinaryPullbackNormalization
(lem-per-localized-ordinary-pullback-normalization), proved from the three new
strictly smaller statements and the proved coefficient theorem.

Additionally proved:
AlgebraicGeometry.Scheme.LocalizedOrdinary.localizedOrdinaryCoefficientCoherence
(lem-per-localized-ordinary-coefficient-coherence), including its six private
supporting lemmas finite_comp, finite_id, projection, completed_comp,
completed_id and transitions.

Three holes added, each with proof exactly `by sorry` in its own public theorem:

- AlgebraicGeometry.Scheme.LocalizedOrdinary.localizedOrdinaryEdge_exists
  (lem-per-localized-ordinary-edge): one morphism, no compositor or identity square.
- AlgebraicGeometry.Scheme.LocalizedOrdinary.localizedOrdinaryComposition_exists
  (lem-per-localized-ordinary-composition): composition for already supplied edges,
  with coefficient coherence as input.
- AlgebraicGeometry.Scheme.LocalizedOrdinary.localizedOrdinaryIdentity_exists
  (lem-per-localized-ordinary-identity): identity for an already supplied edge,
  with the completed coefficient identity as input.

This is a decomposition of the original one-hole theorem, not a complete proof
of the normalization result: 1 original hole closed, 3 added, net minus 2.
There are zero holes in the item module or the data and coefficient modules.

The new single-edge statement allows arbitrary ϖ, since localization at a scalar
and its tensor comparisons do not require that scalar to generate the maximal
ideal. The parent's original uniformizer hypothesis is retained verbatim.
Checked the proposed statements on identity morphisms, empty schemes, zero
modules and complexes, arbitrary unbounded complexes, and scalar ϖ=0 (the
localized coefficient sheaf is the zero ring). No nonzero scalar or invertible
completed structural map is assumed. For arbitrary normalized edges, their
unit and generator formulas determine the ordinary maps, and the resolving
model equation determines the derived maps; hence composition and identity
apply to the supplied edges, rather than requiring simultaneous choices.

## No longer needed

None. No mathematical node, declaration or module is withdrawn or pruned.
The item's original eight public imports are now publicly re-exported through
LocalizedOrdinaryPullbackData. They are not counted as removed dependencies.
Its original generic proof dependencies remain needed in the three residual
steps. The parent proof_deps now point to the four actual proof modules.

The constant-sheaf composition and identity calculations need not be rewritten:
proved private lemmas in ProfiniteCoefficientInverseImage supply them directly
through a proof-only `import all`. Likewise the scalar formula reuses the proved
private pbcCompletedSection_directImage in PbcScalarExtension. No duplicate
statement or private holed helper was introduced.

## Where the brief, the DAG or earlier work was wrong

No statement error was found. The node's review already pointed out that
CompletedCoefficientRingedCoherence contains related coefficient calculations;
its public theorem uses a different completed coefficient presentation. For the
actual pbcAdicCompletion maps the existing constant-sheaf helpers give a shorter
route, which is the coefficient proof written here.

The abstract ringed-derived comparison system does not directly return Edge,
Composition or Identity for the specified actual ordinary scalar-extension
functors and their fixed computation counits. The pro-etale derived composition
interface assumes coefficient isomorphisms, whereas these statements retain
arbitrary structural maps. Identifying these presentations and proving their
normalized generator/model equations is the remaining work, isolated rather
than replaced by an unspecified comparison isomorphism.

The blueprint unit's realized nodes and route are unchanged. The extracted data
are existing definitions, not a second definition of any notion. Reusing the
proved constant-comparison and scalar-section helpers uses their owning
profinite coefficient and scalar-extension nodes as generic tools; the reader
can record any additional tool-use approval required for the new coefficient
node. No maintainer approval list was extended by this delivery.

## New nodes

- def-per-localized-ordinary-pullback-data records the existing auxiliary data in
  their extracted module, with all names and bodies preserved.
- lem-per-localized-ordinary-coefficient-coherence records the proved finite,
  completed, transition and scalar normalization package.
- lem-per-localized-ordinary-edge is original Steps 3–5: construct one specified
  localized edge by balanced flattening and resolving-class descent.
- lem-per-localized-ordinary-composition is original Steps 6–7 for composition:
  the rational compositor, mixed scalar calculation and derived delta square.
- lem-per-localized-ordinary-identity is original Steps 6–7 for identity:
  scalar multiplication and the ordinary and derived identity squares.

All new statements retain the original node's sources and unit. Each node has
its own complete proof in words. Search used leanfinder, loogle, leansearch and
Mathlib grep through msearch.py, followed by local source reading. Searches found
ordinary pullback comparisons, not these normalized actual-localization maps.

## Second reading by E8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
