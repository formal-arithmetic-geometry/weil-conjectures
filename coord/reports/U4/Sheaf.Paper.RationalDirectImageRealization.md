## What changed

In `Sheaf.Paper.RationalDirectImageRealization`, proved
`AlgebraicGeometry.Scheme.ContinuousRational.DirectImage.modulePush_additive`.
The sectionwise pushforward and scalar restriction preserve addition definitionally,
so its `Functor.Additive` field is proved by reflexivity. No new helper is needed.
All signatures, definitions, attributes and imports are unchanged.

The complete item compiled through `lcompile.py` in 16.5 seconds with no diagnostics.
`#print axioms` of the proved instance reports exactly `propext`,
`Classical.choice`, and `Quot.sound` (diagnostic compile: 16.9 seconds).
The diagnostic command was removed afterwards.
The current queue row is stage 3 proof work. The saved global-build error records
bad imports of `ContinuousRationalDerivedRealization` and `SfCommonStageDirectImage`;
these imports succeeded in the current single-file compilation.

## Proved and sorry left

Closed one of the two original holes:
`AlgebraicGeometry.Scheme.ContinuousRational.DirectImage.modulePush_additive`
(node `lem-a1-rational-direct-image-realization`).

One original hole remains, unchanged:
`AlgebraicGeometry.Scheme.ContinuousRational.DirectImage.rational_direct_image_realization`
(node `lem-a1-rational-direct-image-realization`). Its existing docstring contains
the complete fifteen-step proof plan and source. This partial delivery does not
claim the localization projection or the normalized adjunction and coefficient
coherence package. No holes were added or split off.

## No longer needed

None. No imports, modules or nodes were removed. The main theorem remains open,
so its planned dependencies and the unit route are retained. The additivity proof
itself needs no additional import or node.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement defect found. The two saved bad-import diagnostics
were not reproduced by the successful current compile. The existing additivity
hole needs only the definition of pushforward, rather than an auxiliary lemma.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.RationalDirectImageRealization": "80bc5a3025e2ea4f9a3591da82c5a62f90a41bbd"}, "results": {}, "time": "2026-10-28T11:57:49+0800", "transitive": 0, "version": 1}
```

## Second reading by U4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
