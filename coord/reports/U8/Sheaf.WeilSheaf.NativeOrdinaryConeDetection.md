## What changed

Proved `WeilConjectures.NativeExceptionalForgetful.native_ordinary_cone_detection`
by combining a split-mono witness and a split-epi witness and applying
`isIso_of_mono_of_isSplitEpi`. Added two strictly smaller intermediate theorem
modules: `NativeOrdinaryConeRetraction` and `NativeOrdinaryConeSection`. The
previous combined split-data module was withdrawn because the two halves are
independent proof obligations. Added the corresponding DAG node copies.

The sandbox compiles all three modules in import order.

## Proved and sorry left

Closed the sole `sorry` in `NativeOrdinaryConeDetection`.

Added two `sorry`s, one each in:

- `native_ordinary_cone_retraction`, asserting a `SplitMono` witness;
- `native_ordinary_cone_section`, asserting a `SplitEpi` witness.

No definitions contain `sorry`.

## No longer needed

The withdrawn `NativeOrdinaryConeSplitData` module is no longer needed; its
single combined obligation was replaced by the two strictly smaller halves.
No existing dependency import was pruned.

## Where the brief, the DAG or earlier work was wrong

The original proof plan bundled two logically distinct geometric conclusions:
the rotated-cone argument yields a retraction, while finite-dimensional
constructible stalks yield a section. Splitting them makes each remaining
statement strictly simpler and leaves a real categorical proof of the parent.
The target statement and its hypotheses were unchanged.

## New nodes

- `lem-sf-native-ordinary-cone-retraction`
- `lem-sf-native-ordinary-cone-section`

The withdrawn combined node/module is listed in `deleted.txt`.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.WeilSheaf.NativeOrdinaryConeDetection": "143898757516bebd711dd8f3ebd2d26e9930640e", "Sheaf.WeilSheaf.NativeOrdinaryConeRetraction": "313d3d43a6c0db4c0354a270cb3a7db906255522", "Sheaf.WeilSheaf.NativeOrdinaryConeSection": "e387096687f28b8f7f5460b016fbd41c50a47940"}, "results": {}, "time": "2026-10-28T12:16:10+0800", "transitive": 0, "version": 1}
```

## Second reading by U8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
