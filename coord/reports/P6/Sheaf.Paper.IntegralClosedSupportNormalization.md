## What changed

Restored the quarantined item from its preserved archive. Its published dependency now
resolves. Replaced the whole proof of
`WeilConjectures.IntegralSupportNormalization.closedSupportNormalization` with an assembly
from ordinary recollement and the specified coefficient-system model. All existing public
signatures, structures, definitions and public imports are preserved.

The proof obtains finite limits and colimits from the two existing adjunctions, proves
`closedAlpha` invertible from the actual reconstruction unit, defines `di` as its inverse,
uses the existing completed-image completeness proof, obtains the actual finite reduction
isomorphisms from `C.push_reduction`, preserves the same reduction interval by exact finite
closed direct image and its homology comparison, transports shifts and triangulatedness
through the fully faithful inclusion, and transports `R.disjoint` to the actual functors.

Private proved helpers perform the shift-square and full-subcategory calculations with
abstract functors before specializing to coefficient operations. This avoids unfolding
chosen total-limit objects just to compare the two presentations of an underlying object.
No shared definition is altered.

Two new modules isolate the remaining geometric normalization work. They assert properties
of the prescribed reduction square and alpha map, rather than another existence theorem
for ClosedSupport. The assembly, including exactness, completeness, intervals, inversion,
restricted shifts and vanishing, is implemented in the item.

Validation: all three modules compiled in import order with `lcompile.py --all`.
The cleaned item was then checked again and compiled in 5.7 seconds with no errors or
warnings. The existing structure and theorem signatures were compared verbatim with
the preserved archive. All three DAG dependency lists match their proof steps, and
every named dependency exists.

## Proved and sorry left

Original holes: one, `WeilConjectures.IntegralSupportNormalization.closedSupportNormalization`
(node `lem-sf-closed-support-normalization`). Its proof is now complete from the named
prerequisites; no sorry remains in the item. This is a decomposition, not a complete proof
of the original obligation: zero holes closed without decomposition, one decomposed,
two holes added, net minus one in these delivered sources.

The two remaining holes, each the whole proof of a public named theorem in its own module:

- `WeilConjectures.IntegralSupportNormalization.closedReduction_isIso`
  (`lem-sf-closed-reduction-comparison`, IntegralClosedReductionComparison).
- `WeilConjectures.IntegralSupportNormalization.closedAlpha_normalization`
  (`lem-sf-closed-alpha-normalization`, IntegralClosedAlphaNormalization).

Each new theorem has its source, a full natural-language argument, a DAG node and an
unchanged actual-map formulation. No data definition contains sorry. Existing imported
holes are reused as the stage requires and are not copied or claimed as proved.

## No longer needed

No original import is removed: the original sole public import of
IntegralSupportNormalizationData remains. No module is withdrawn or claimed globally
unreachable.

The item no longer directly needs the etale-origin/site-comparison route:
`lem-sf-proetale-constructible-origin`, `prop-weil-pbc-site-comparison-finite-level`,
`prop-weil-pbc-comparison-direct-image`, or `lem-fin-closed-immersion`. Its interval proof
uses exactness of the actual finite pro-etale closed direct image directly.

`prop-weil-pbc-koszul-reconstruction`, `prop-weil-pbc-direct-image-limits`,
`lem-weil-strict-roos-comparison` and `def-weil-exact-derived-adjunction` are no longer
separate direct proof dependencies of the parent. Reconstruction and comparison machinery
remain inside the reused system model, existing completeness proof and the new comparison
nodes; these are not claimed as globally pruned. The ringed open/closed result remains
needed through `lem-sfb-proetale-identified-open-closed`.

## Where the brief, the DAG or earlier work was wrong

The recorded quarantine failure was a bad import of IntegralSupportNormalizationData.
The current published dependency allows the restored source to compile; restoration alone
was not treated as completion. The archive's one original sorry was opened and reduced.

The old plan's etale-origin comparisons are unnecessary for preserving intervals once
exactness of the canonical finite closed direct image is available. The unit route is
unchanged: the localization triangle still uses exact closed direct image and the original
open/closed operations. The new lemmas retain the normalized actual maps and never infer
an equality of derived system morphisms merely from equality of their evaluations.

Edge cases checked in the mathematical reading: zero input, empty closed or open part,
identity closed immersion, arbitrary shifts, and empty intervals a > b. The interval proof
uses only preservation of zero homology and does not assume a <= b. The reduction-square
lemma has arbitrary ambient input; the alpha formula is on the original full constructible
category. Its data are not chosen from a new existential theorem.

## New nodes

`lem-sf-closed-reduction-comparison`: invertibility of `closedReduction` for a supplied
ordinary normalized closed-immersion comparison. This is the reduction-square part of old
steps 1--2; it asserts none of the other ClosedSupport fields.

`lem-sf-closed-alpha-normalization`: the projection and signed-shift identities for the
canonical `closedAlpha`, assuming the strict reduction square invertible. This is the map
normalization part of old steps 2 and 4; it asserts no restricted functor, completeness,
interval, adjunction, triangulatedness or support vanishing.

Change record: `coord/changes/P6-integral-closed-comparison-decomposition.md`.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.IntegralClosedAlphaNormalization": "2c4786251b452a9d8fc15a8dafa41dd615c4cbe2", "Sheaf.Paper.IntegralClosedReductionComparison": "6aa063eb838301593a8aaaba6651dc9547b991e5", "Sheaf.Paper.IntegralClosedSupportNormalization": "6edd8cbf1e1b1d61f0eac149bb6ec224435e90cd"}, "results": {"Sheaf.Paper.IntegralSupportFunctorNormalization": {"hash": "fb1f160aeee91fa0adc2ea96d83edb1460a363a9", "status": "OK"}}, "seconds": 49, "time": "2026-10-28T01:37:46+0800", "transitive": 0, "version": 1}
```

## Second reading by P6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
