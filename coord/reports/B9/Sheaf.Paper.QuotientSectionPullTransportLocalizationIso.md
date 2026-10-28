## What changed

Replaced the sole caller's use of the transport helper by a complete proof directly in
`Sheaf.Paper.QuotientSectionPullTransportLocalization`. The two composites are natural
transformations on complexes. Apply naturality to the actual flat-term K-flat resolution
augmentation, substitute the assumed equation and cancel its invertible derived source
map. The caller's statement and all target statements are unchanged.

Withdrew `Sheaf.Paper.QuotientSectionPullTransportLocalizationIso` through `deleted.txt`,
removed its sole import/call, set its node's Lean attachment to `null`, and updated its
parent's proof record. Change record:
`coord/changes/B9-quotient-section-pull-direct-localization.md`.

## Proved and sorry left

The item initially had one sorry in
`AlgebraicGeometry.ProEtale.QuotientSectionTensor.section_pull_normalized_localization_transport_iso`.
That declaration and its hole are pruned, not claimed as a proof of the original
arbitrary-derived-isomorphism statement. Thus 0 of its 1 original statements are proved
in place; 1 hole is removed by pruning; 0 holes are added; 0 are split off; 0 remain in
the delivered Lean modules.

`AlgebraicGeometry.ProEtale.QuotientSectionTensor.section_pull_normalized_localization_descent`
has a complete new proof of its unchanged statement, with no remaining sorry or use of
the retired helper. Its old proof depended on the retired hole. This is not a decomposition.

## No longer needed

Pruned module `Sheaf.Paper.QuotientSectionPullTransportLocalizationIso`, its declaration
`section_pull_normalized_localization_transport_iso`, and node
`new-sfb-quotient-section-pull-transport-localization-iso` from its sole parent's proof
dependencies. Removed the parent's private import of the module. The retired module's
public import of `QuotientSectionPullTransportKFlat` is unnecessary there; the parent
still imports the K-flat module directly for its existing interfaces.

No other import or dependency is pruned. The existing proved generic K-flat resolution
node `lem-sfb-abstract-kflat-resolution` supplies the actual augmentation; the unit's
resolution/localization route is preserved. DAG and Lean searches found no other parent,
caller or unit realization of the retired helper.

## Where the brief, the DAG or earlier work was wrong

The previous split discarded the resolution's actual cochain map and retained only an
isomorphism of derived objects. Its proposed naturality proof treated the ordinary
scalar-extension target as though it descended to the derived category, which is not
part of the model's hypotheses. The direct cochain-level proof avoids that unsupported
step and requires no additional mathematics or new statement. No claim about the truth
of the retired stronger statement is needed for this replacement.

The current server queue lists an ordinary stage-3 proof item, with no rework row,
build-error file or open B9 return for it. The parent's current server claim is absent.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.QuotientSectionPullTransportLocalization": "504829d35defc8103909798350751975850a036b", "Sheaf.Paper.QuotientSectionPullTransportLocalizationIso": "fdd6fd89e33daef28207b2d920705ea5b4231ed8"}, "results": {"Sheaf.Paper.QuotientSectionPullTransportExtension": {"hash": "3e53cea4a261930ca9e16d8af3e71d959cb32f83", "status": "OK"}}, "seconds": 71, "time": "2026-10-28T10:18:59+0800", "transitive": 0, "version": 1}
```

## Second reading by B9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
