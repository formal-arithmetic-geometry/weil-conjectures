## What changed

Replaced the hole in `geoCartierCanonicalClass_scalar` by a complete assembly proof
from two independent parts of the original argument. The first part is existence
of normalized source and line coefficient maps with their unbounded derived unit
properties. It does not assume a Cartier ideal or mention any Ext class. The second
part is the coefficient square for comparison images of arbitrary ordinary relative
boundary representatives. It assumes only the generator normalizations of the maps;
it does not assert their existence or their derived unit properties.

The main proof obtains the canonical ordinary boundary specifications, applies the
second part to the maps supplied by the first, and precomposes its equality with the
inverse R supported-source mate. Exact-functor compatibility with Yoneda products,
associativity, and cancellation of the source isomorphism identify the resulting
square with the actual canonical pro-etale classes. A proved private lemma performs
this cancellation over abstract abelian categories, so simplification does not
unfold the large concrete sheaf constructions. The existing theorem signature,
definitions, and public import are unchanged. Two private proof imports are added. The new units module imports only the
interface definitions its statement needs; source-comparison invertibility is
needed by the square module, not by this units statement.

Remote compilation passed for both new statements and for the complete assembly
proof. The assembly compiled in 28.8 seconds after extracting the abstract
cancellation helper. The delivery command performs the final packet checks.

## Proved and sorry left

This is a decomposition, not a complete proof of coefficient naturality and not a
net decrease in holes. The original hole closed is
`AlgebraicGeometry.ProEtale.geoCartierCanonicalClass_scalar`
(`lem-sfb-cartier-reduction-scalar`), proved from the two following new holes:

- `AlgebraicGeometry.ProEtale.geoCartier_normalized_scalar_units`
  (`lem-sfb-cartier-normalized-scalar-units`), in
  `Sheaf.AlgebraicGeometry.CartierNormalizedScalarUnits`.
- `AlgebraicGeometry.ProEtale.geoCartier_boundary_scalar_square`
  (`lem-sfb-cartier-boundary-scalar-square`), in
  `Sheaf.AlgebraicGeometry.CartierBoundaryScalarSquare`.

The item has zero remaining holes; two new modules have one each. Each postponed
proof is exactly `by sorry` and has its source, complete argument in words, and a
matching DAG node. The assembly proof has no internal holes. The two statements
separate construction/universality from boundary naturality and neither restates the
original compatibility predicate under another name. Empty support and the zero
ring produce zero supported objects; the identity map gives the usual unit. Positive
N and its invertibility retain the locally free roots-line argument, including N=1
(where the coefficient rings are zero). No flatness hypothesis is added.

## No longer needed

No existing import was removed, and no module or node is withdrawn or claimed
pruned. The original low-level dependencies are now recorded under the two new
steps, rather than cited as if the main assembly used their mismatching APIs
directly. In particular, `lem-geo-cartier-coeff-extension`,
`lem-asd-finite-etale-twist-line`, `lem-pur-derived-change-of-rings`,
`lem-sfb-successive-derived-quotient-normalization`,
`lem-pur-sheaf-ring-derived-coefficient-adjunction`,
`lem-asd-ordinary-supported-kummer`, and
`lem-weil-pbc-ringed-topoi-derived-tensor-pullback` remain needed below these steps.
`def-sfb-geo-cartier-canonical-class` remains a direct dependency. The canonical
ordinary-class specification and source-isomorphism node are explicitly cited in
the updated main proof. The unit's ordinary construction followed by comparison
inverse image is preserved.

## Where the brief, the DAG or earlier work was wrong

The existing `supported_kummer_boundary_scalar` theorem treats only the lifted
residue-ring map Z/N to A, rather than an arbitrary A to B. The coefficient
extension theorem treats supported constants and their derived comparisons, not
normalized roots maps or relative boundary naturality. The generic tensor and
adjunction theorems likewise do not directly supply the normalized pro-etale
interface. These missing specializations have been made explicit instead of
assuming they follow by applying a single existing declaration. The alternative
integral-generator/root-map route was checked too: the useful reduction-spec and
Kummer-comparison helpers are private in CartierReductionSiteComparison, which
already imports this item through GeoCartierCycleClass. Importing that module here
would create a cycle. The generic Ext-bijection lemmas alone do not supply those
normalized boundary equations.

The source of `Sheaf.SixFunctors.GeoCartierCoeffExtension` is currently quarantined
as recorded in `coord/rework.tsv`; its archived theorem and dependencies were read
and retained. No archive or Lean attachment was removed, and its temporary absence
was not treated as a withdrawal.

## New nodes

`lem-sfb-cartier-normalized-scalar-units` records just the construction, generator
formulas, and unbounded universal properties of the two coefficient units. Its proof
uses the existing supported-constant comparison, flat roots line, derived scalar
adjunction, and comparison tensor compatibility. It has no Cartier-ideal hypothesis
or boundary-class data.

`lem-sfb-cartier-boundary-scalar-square` records just the Ext square on exact
comparison images of arbitrary ordinary normalized boundaries, with the supported
source mates displayed. The proof uses transitivity of derived extension of the
pole boundary, ordinary relative-boundary uniqueness, and comparison naturality.
It neither produces coefficient maps nor asserts scalar-unit universal properties.
Both nodes follow the current blueprint's finite coefficient extension and opening
comparison paragraphs. LeanSearch, LeanFinder, Loogle, source grep, and blueprint
searches found no existing declaration with either full interface. No shared
interface changed and no change record or forced adaptation is required.

## Second reading by S4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
