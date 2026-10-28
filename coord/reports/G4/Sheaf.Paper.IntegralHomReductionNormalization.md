## What changed

The main module now constructs `ReductionPresentation` from two strictly smaller
statement modules. `IntegralHomReductionComparisonExists` states existence of the
fixed-target derived tensor comparison isomorphism, and
`IntegralHomReductionNormalizationData` states existence of the flat representative
maps, pure-tensor normalization, and derived counit square. The main proof obtains
those witnesses and packages them with the fixed target. The main theorem has zero
`sorry`s.

## Proved and sorry left

Closed `WeilConjectures.IntegralHom.reduction_normalization_exists` (one hole).
Added the strictly smaller split statements
`WeilConjectures.IntegralHom.reduction_comparison_exists` and
`WeilConjectures.IntegralHom.reduction_normalization_data_exists`, each with one
`sorry`, respectively in the nodes
`lem-sf-integral-hom-reduction-comparison-exists` and
`lem-sf-integral-hom-reduction-normalization-data`.

## No longer needed

Removed the unused proof import `Sheaf.Paper.IntegralHomReductionComponents` from
the item module. The original three proof dependencies are retained only as the
stated dependencies of the two split-off lemmas; the item proof itself uses the two
new declarations.

## Where the brief, the DAG or earlier work was wrong

The original node bundled the derived comparison construction and all representative
normalization equations into one theorem, which was not tractable as a direct Lean
proof. No statement was weakened or changed. The route was decomposed into the
comparison and normalization components, then assembled by the actual structure
constructor.

## New nodes

`lem-sf-integral-hom-reduction-comparison-exists` is stated in
`lean/Sheaf/Paper/IntegralHomReductionComparisonExists.lean` and records the fixed
finite-target derived tensor comparison. Its proof is the scalar-extension,
balanced-associativity and derived-universal-property argument from the blueprint.

`lem-sf-integral-hom-reduction-normalization-data` is stated in
`lean/Sheaf/Paper/IntegralHomReductionNormalizationData.lean` and records the
strictly smaller representative normalization and counit-square fields. Its proof
is the sectionwise scalar-unit and derived transport argument from the blueprint.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.IntegralHomReductionComparisonExists": "1d9171d50236db8484caa907a555a22b95355620", "Sheaf.Paper.IntegralHomReductionNormalization": "eaf89bc43be9a1979aded47e5b25bf27ec691d65", "Sheaf.Paper.IntegralHomReductionNormalizationData": "16489e89a79fe6da8fbc611715ee174962ad6d55"}, "results": {"Sheaf.Paper.IntegralHomReductionPresentation": {"hash": "0e5216560a3b2842e8613af3378b2363613c69c3", "status": "OK"}}, "seconds": 10, "time": "2026-10-28T10:58:31+0800", "transitive": 0, "version": 1}
```

## Second reading by G4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
