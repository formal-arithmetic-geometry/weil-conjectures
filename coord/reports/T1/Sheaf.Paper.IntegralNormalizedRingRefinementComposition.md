## What changed

The composition theorem is now proved from a strictly lower-level objectwise
composition statement after applying the integral coefficient inclusion.  The
main proof identifies the two natural isomorphisms by `Iso.ext` and
`NatTrans.ext`, then cancels the faithful inclusion on each component.  The
objectwise theorem is recorded in the new module
`Sheaf.Paper.IntegralNormalizedRingRefinementCompositionAfterInclusion` and is
the remaining stage-3 obligation for the binary normalized pasting argument.

The sandbox files compile with `lcompile.py --all`.

## Proved and sorry left

The declaration
`integral_normalized_ring_refinement_composition` is proved, closing one
existing `sorry`.

The new declaration
`integral_normalized_ring_refinement_composition_after_inclusion` remains as
one named `sorry`, recording the objectwise normalized integral pasting step.

## No longer needed

The original proof plan's direct imports are not needed by the composition
module itself: its proof uses only the new after-inclusion module.  The five
large pasting and realization nodes remain dependencies of the new lower-level
statement, where the actual geometric work belongs.

## Where the brief, the DAG or earlier work was wrong

The original item exposes only the abstract construction record `N`; it does
not expose the auxiliary normalized integral pasting data required to apply
`integralNormalizedRefinementPasting` directly.  The DAG plan therefore needs
the objectwise after-inclusion statement as an explicit intermediate node.
The original target statement and all its hypotheses are unchanged.

## New nodes

`lem-sf-integral-normalized-ring-refinement-composition-after-inclusion` is
implemented by
`Sheaf.Paper.IntegralNormalizedRingRefinementCompositionAfterInclusion`.
It states the binary composition equality after the faithful integral
coefficient inclusion, which is strictly simpler than equality of the original
refinement isomorphisms.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.IntegralNormalizedRingRefinementComposition": "f243dcd49bce24548270634ef3acca664ab17a9b", "Sheaf.Paper.IntegralNormalizedRingRefinementCompositionAfterInclusion": "0540fed22855e0f93b5b38d8b9e8ffd3faef8341"}, "results": {}, "time": "2026-10-28T05:13:32+0800", "transitive": 0, "version": 1}
```

## Second reading by T1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
