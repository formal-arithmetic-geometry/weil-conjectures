## What changed

Filled both proof obligations in `Sheaf.AlgebraicGeometry.AlgebraicSpaceSchemeRestriction`.
`schemeOpensArrow_isEtale` uses the existing scheme-morphism test and `isEtale_comp`.
`schemeOpens_isContinuous` uses Mathlib's cover/compatibility criterion: a proved private
helper factors comparison maps through the open intersection, and the covering proof
uses the pointwise Zariski covering condition to produce a jointly surjective etale cover.
Added private proof imports of `AlgebraicSpaceRepresentableEtaleSchemeTests` and
`Mathlib.CategoryTheory.Sites.CoverPreserving`; retained both existing public imports.
Updated the existing definition node's proof, dependencies and proof origin to match.
All public signatures, definitions and their data constructions are unchanged.

## Proved and sorry left

Closed 2 of 2 original holes:
- `AlgebraicGeometry.AlgebraicSpace.schemeOpensArrow_isEtale`.
- `AlgebraicGeometry.AlgebraicSpace.schemeOpens_isContinuous`.

No holes remain in the delivered module. No holes added; no split-off modules.
The proof uses the already stated (still holed) `representable_etale_scheme_tests`
and `isEtale_comp`, as intended by stage 3; their holes are not claimed closed.
The private `schemeOpens_compatiblePreserving` helper is fully proved.

## No longer needed

None. No existing import, module, declaration, node or unit step is removed.
The node originally had no proof dependencies; the recorded dependencies now match
its proof. The generic continuity criterion and open-fibre-product nodes are Mathlib
leaves. No new mathematical result is left for another worker.

## Where the brief, the DAG or earlier work was wrong

The definition node had no proof steps despite the two named construction obligations.
It now records their actual proofs. No statement error or interface repair was needed.
Read Stacks `definition-etale-site`, `definition-structure-sheaf`, and
`remark-change-topologies-ringed-sites`; the construction is exactly restriction to opens.
The proof allows empty opens and empty test schemes: the covering point condition is
vacuous there, and the pullback/compatibility argument needs no nonemptiness assumption.
It imposes no separation, affineness or finite-cover assumption. The existing unit route
is retained. The current blueprint unit text is newer than its unit JSON record, but
this delivery changes neither the unit nor any target.

## Second reading by R9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
