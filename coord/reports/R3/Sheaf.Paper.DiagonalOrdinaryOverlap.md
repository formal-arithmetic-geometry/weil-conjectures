## What changed

`Sheaf.Paper.DiagonalOrdinaryOverlap` now proves the unchanged `overlap` statement
from a single restriction-naturality identity. The proof uses all affine subopens
of the target intersection, without supposing that the intersection is affine.
It proves injectivity of realization from bounded-below comparison, associativity
of the ordinary restriction compositors, compatibility with the common shift,
and the degree-zero equality test on the resulting jointly surjective cover.
The latter is proved directly using H0 and conservativity of sheaf inverse images.

The new proof-only import `Sheaf.Paper.DiagonalOrdinaryRealizeRestriction` supplies
one independent identity for the realization of an arbitrary ordinary local
isomorphism under one nested affine restriction. Its statement involves no
charts, chart agreement, family, shifted overlap or gluing conclusion. The other
new proof-only imports provide generic exact-functor compositor and shift
coherence and the existing sheaf conservativity theorem. Public imports,
existing definition bodies and all existing declaration signatures are unchanged.

The node copies describe this actual proof route. No unit route is bypassed:
the supplied DNC/vector-bundle charts and their prescribed theta realizations
remain the input orientations.

## Proved and sorry left

Closed in the item: `WeilConjectures.PurityFiniteSetting.OrdinaryDiagonal.overlap`
(node `lem-pur-diagonal-ordinary-overlap`), the only original hole. There are zero
sorries in the item module. Its private comparison, cover, compositor and shift
helpers are proved.

Added and still sorry:
`WeilConjectures.PurityFiniteSetting.OrdinaryDiagonal.realize_restriction`
(node `lem-pur-diagonal-ordinary-realize-restriction`), in
`Sheaf.Paper.DiagonalOrdinaryRealizeRestriction`.

This is a decomposition, not a net hole closure: one old hole closed, one new
hole added, net zero. The remaining task is a concrete identity between the
explicit ordinary/pro-etale comparison and finite Tate transports. Its docstring
spells out the source-composition, normalized roots/line, tensor-induction and
shift argument. The overlapping-open descent and bounded-below injectivity
arguments are supplied in Lean in this delivery.

Edge cases checked in the argument: equal nested opens, d=0, empty opens and
empty overlaps, zero coefficient ring, and a nonaffine intersection. None requires
a positive dimension, a nonempty cover or an affine-intersection hypothesis.

## No longer needed

No existing module is withdrawn and no public import is removed. No adopted
source-library declaration is removed or changed.

The item no longer uses `lem-pur-affine-target-diagonal-dnc` as a proof dependency:
the cover comes directly from the affine-open basis, and finite type on each
affine chart follows from local finite type of its structural map. That node
remains needed for construction of the input charts elsewhere.

The item does not apply `degreeZeroDerivedMapGluing`: it proves the required
equality-only test with H0 and the existing jointly-surjective sheaf
conservativity theorem. Its module remains publicly imported for `openComp`,
which is part of the unchanged `onSmallerIso` definition, so its node remains a
definitional proof dependency and no whole module is claimed as pruned.

`det-prop-sfb-cartesian-coefficients-twists` is no longer a direct proof dependency
of the item: the finite Tate composition calculation belongs to the new
restriction-naturality obligation. It remains in that obligation's proof plan;
this delivery does not claim to prune it globally.

## Where the brief, the DAG or earlier work was wrong

The original plan correctly identifies the needed mathematical steps. Its
phrase about transporting realization equations concealed a specific missing
identity for the actual normalized maps, rather than an immediate application
of an existing theorem. The library's general comparison coherence and its
section-only `orderedTateSectionPullback` do not directly state this identity;
the latter requires a retraction, which a nested open need not possess.

The new identity is strictly one part of that plan, with weaker geometric
hypotheses and no chart-agreement or descent assertion. The proof uses its two
nested instances, comparison Hom injectivity, the derived restriction/shift
coherence, and a jointly-surjective equality argument to obtain `overlap`.

Generic tool used from another unit:
`lem-etale-sheaf-jointly-surjective-conservative`, via its existing proved source
library declaration. It supplies only detection of isomorphisms of ordinary
sheaves; exactness then gives joint faithfulness. It replaces no geometric or
purity unit step. The maintainer may record this tool use if required.

The new restriction identity also lists
`lem-weil-pbc-comparison-pullback` and
`lem-weil-pbc-proetale-derived-pullback-composition` as generic coherence tools
for its remaining calculation. They concern the existing site comparison and
inverse-image functors, rather than a different purity route.

## New nodes

`lem-pur-diagonal-ordinary-realize-restriction` is the single new node. Its module
contains one theorem with one sorry, its full source/proof docstring, and no new
definitions. It isolates restriction naturality of the fixed realization
coordinates. LeanSearch, Loogle and grep searches were run before introducing
it; generic pullback coherence exists, but the prescribed combined identity was
not found. Blueprint search found no duplicate. There are no definition or
statement change records, since all existing interfaces are preserved.

For the remaining calculation, `Dnc.pullComparison` in `PurityDncInvariance` is
the explicit pro-etale/ordinary derived comparison. The module
`ComparisonPullbackCoherence` proves `comparison_pullback_coherent`, including
its composition component. `MapDerivedCategoryMate` supplies the generic
exact-functor derivation compositor, associativity and whiskering identities.
`OrdinaryFiniteTwistTransportUniqueness` proves uniqueness from the normalized
roots inclusion and pure coefficient/root generators, using `lineHomEquiv`.
The actual ordered Tate transport is the recursion
`vectorIntegrationBaseCoefficientPullback` in `VectorBundleIntegrationCharts`.
These APIs support the source square and the target tensor induction described
in the new theorem's docstring; no unsupported arbitrary Tate identification
is introduced.

## Second reading by R3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
