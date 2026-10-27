## What changed

Replaced the sorry in `integralPullEvaluation_quotientSquare` by an explicit
localization-pasting proof. Its statement and public imports are unchanged.
The proof checks equality of natural transformations after localization,
cancels the evaluation/pullback/restriction factorization isomorphisms, and
uses naturality and the defining evaluation and transition normalizations.
A proved private lemma performs the pasting for abstract indexed abelian
categories; the final theorem instantiates it with the actual functors. This
avoids repeatedly unfolding the sheaf constructions during rewriting.

Added `IntegralScalarPullbackMateNormalization`, proving the exact localization
formula for the inverse scalar pullback mate. Its private categorical proof
uses the derived-adjunction unit formula and the existing
`compactSupportScalarDirectNormalization`. The equality transport quantifies
over the restriction functors and their instances, so it preserves their
additivity/exactness proofs and does not assume restriction preserves
K-injectives. Added `IntegralPullEvaluationCochainSquare`, with the actual
constructed cochain comparison and the remaining ordinary geometric square.
Updated the item's proof dependencies and added nodes for the two parts.

Validation: the final three-module packet compiled in import order without
warnings or errors. The item compiled in 49.8 seconds; the scalar mate module
has a checked proof and no holes. The item signature was compared verbatim
with the original and is unchanged.

## Proved and sorry left

Closed the original hole:
`WeilConjectures.IntegralSystemRealization.integralPullEvaluation_quotientSquare`
(node `lem-sf-integral-pull-evaluation-quotient-square`).

Proved without a new hole:
`WeilConjectures.IntegralSystemRealization.integralScalarPullback_mateNormalization`
(node `lem-sf-integral-scalar-pullback-mate-normalization`), including its private
unit, transpose, inverse-mate and equality-transport lemmas.

One new hole remains:
`WeilConjectures.IntegralSystemRealization.integralPullEvaluation_cochainSquare`
(node `lem-sf-integral-pull-evaluation-cochain-square`). Its docstring gives the
sectionwise argument. It is strictly the ordinary cochain part: it contains
no localization, derived direct image, K-injective comparison, or derived
adjunction. The proof combining this with the scalar normalization and passing
to arbitrary derived systems is complete. Thus this is a decomposition: one
original hole closed and one lower hole added, net zero, rather than a claimed
unconditional proof of the original result. There are no holes in definitions.

## No longer needed

No original import is removed, and no module is withdrawn. The planned direct
proof dependencies `lem-coef-semilinear-derived-sections`
(`Sheaf.Paper.SemilinearDerivedSections`) and
`lem-sf-compact-support-restriction-of-scalars`
(`Sheaf.SecSmoothPurity.IntrinsicCompactSupportRestriction`) are not used in
this proof.
Their broad calculus or compact-support comparison is replaced by the ordinary
cochain identity and the all-complex normalization of the fixed scalar direct
comparison. This does not claim either module is absent from the transitive
library import closure. The unit's coefficient-compatibility route is retained.

## Where the brief, the DAG or earlier work was wrong

The old plan names the general semilinear calculus, but does not provide the
ordinary square in the fixed sequence-site evaluation coordinates. The new
cochain node states precisely that missing sectionwise step. The scalar mate
identification requires the all-complex right-derived-unit equation; mere
invertibility or an assumption that scalar restriction preserves K-injectivity
would not identify the published comparison. The delivery proves that
identification from the existing normalization theorem instead.

The stale local quarantine/build record was checked against the current queue
and source records. The current item has one proof hole; its original source
compiled before proof work. No quarantine archive or source declaration is
removed.

## New nodes

`lem-sf-integral-pull-evaluation-cochain-square` is the ordinary cochain square
from proof step 1, with the comparison explicitly constructed from the existing
inverse-image/evaluation and finite intrinsic comparisons. The zero complex
and n = 0 require the same formula; no flatness or normalization is added.

`lem-sf-integral-scalar-pullback-mate-normalization` is the now-proved derived
mate normalization from proof step 2. It concerns a single finite module
complex and contains no system evaluation or system transition. Its abstract
proof is by injectivity of the derived adjunction transpose and the canonical
unit equations. No existing shared definition or signature was changed, so no
change record or forced adaptation is required.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.SixFunctors.IntegralPullEvaluationCochainSquare": "51a8e5ffbfe9b723c9a2f758f76af3d8fd761a3b", "Sheaf.SixFunctors.IntegralPullEvaluationQuotientSquare": "019c4f7bea36448db411c4c6e8684381d22b4e7b", "Sheaf.SixFunctors.IntegralScalarPullbackMateNormalization": "f53e748011e006b6ca08a4fe9e37be6cae3098fd"}, "results": {"Sheaf.SixFunctors.IntegralSystemDirectEvaluation": {"hash": "eee5082cebdacaa7df2167b6c36afd231ecfbf5d", "status": "OK"}}, "seconds": 22, "time": "2026-10-28T02:32:31+0800", "transitive": 0, "version": 1}
```

## Second reading by H4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
