## What changed

Filled `sfQbarLocalizationFiniteCoherence` by assembling two strictly smaller finite-stage packages. Added `SfQbarLocalizationFiniteBase` and `sfQbarLocalizationFiniteBase_exists` for the finite operations and their prescribed stage comparisons, and `SfQbarLocalizationFiniteTail` and `sfQbarLocalizationFiniteTail_exists` for exact, shift, adjunction, mate, unit, and counit coherence. The target imports these proof-only modules and constructs the original `SfQbarLocalizationFiniteData` field by field. The target statement is unchanged.

## Proved and sorry left

The target declaration `sfQbarLocalizationFiniteCoherence` is proved with no `sorry`. The two strictly smaller intermediate existence declarations remain `sorry`, each with a complete source and proof plan in its docstring and DAG node:

- `sfQbarLocalizationFiniteBase_exists` (`lem-sf-qbar-localization-finite-base-existence`);
- `sfQbarLocalizationFiniteTail_exists` (`lem-sf-qbar-localization-finite-tail-existence`).

This is a decomposition: the base contains only the operation and comparison fields, while the tail takes a fixed base and contains only the remaining coherence fields.

## No longer needed

The target proof keeps only the finite-data public import and the tail proof import; the direct base import is redundant because the tail imports it. The target proof no longer directly uses the nine original proof dependencies (`lem-sf-rational-localization-triangle-orthogonality`, `lem-weil-compact-support-finite-field-independence`, `lem-sf-rational-direct-image-coefficient-compatibility`, `lem-fix-operation-reduction`, `lem-weil-pbc-ringed-scalar-pullback-shift-normalization`, `lem-pur-compact-support-scalar-shift-normalization`, `lem-pur-scalar-shift-line-tower-transport`, `lem-weil-scalar-extension-exact-triangulated`, and `lem-weil-scalar-extension-composition`); they remain recorded as dependencies of the two split-off nodes where their planned arguments belong. No existing module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The previous landing was quarantined because its global build saw a stale bad import; the current source import graph compiles. The original proof plan asks one theorem to construct a large record with all finite operations and coherence fields at once, so the proof has been split into the two genuine subpackages above. No target statement or definition was changed.

## New nodes

`lem-sf-qbar-localization-finite-base-existence` records existence of the finite operation package and is implemented by `Sheaf.Paper.SfQbarLocalizationFiniteBase`. `lem-sf-qbar-localization-finite-tail-existence` records existence of the remaining coherence package for a fixed base and is implemented by `Sheaf.Paper.SfQbarLocalizationFiniteTail`.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.SfQbarLocalizationFiniteBase": "11455ba0bb11a0544db0074ad72900b09923b663", "Sheaf.Paper.SfQbarLocalizationFiniteCoherence": "8b72a9dc8747b0080ae444a1a816ec3514800c90", "Sheaf.Paper.SfQbarLocalizationFiniteTail": "b1c225329f09a66ef9f94b55b62f96a43ea4e795"}, "results": {}, "time": "2026-10-28T00:50:04+0800", "transitive": 0, "version": 1}
```

## Second reading by G6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
