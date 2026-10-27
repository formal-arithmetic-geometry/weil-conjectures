## What changed

Restored the quarantined module and proved `native_compact_support_finite_scalar_coherence` by
unpacking the common-stage object, constructing a finite-Tor integral representative with
`integral_residue_tor`, and applying the fixed-stage generator transition theorem. Added the
proof-only import of `Sheaf.Paper.NativeCompactSupportFiniteScalarCoherenceGenerator` and
`Sheaf.Paper.IntegralResidueTor`. Added the strictly smaller generator theorem module and its
DAG node; its proof remains explicitly split as a named theorem.

## Proved and sorry left

Closed one original sorry: `native_compact_support_finite_scalar_coherence`.

Left one split sorry: `native_compact_support_finite_scalar_coherence_generator`, in
`Sheaf.Paper.NativeCompactSupportFiniteScalarCoherenceGenerator`, recorded by node
`lem-sf-native-compact-support-finite-scalar-coherence-generator`. It is strictly smaller:
it fixes the stage index and raw stage object, leaving only the coefficient-mate calculation.

## No longer needed

The target proof no longer directly needs the former direct proof dependencies
`def-sf-locally-finite-adic-compact-support-data`,
`def-sf-constructible-exceptional-coefficient-construction-data`,
`def-sf-locally-finite-adic-realization-data`,
`lem-sf-constructible-exceptional-coefficient-coherence`,
`lem-sfb-pasted-mates-counit-normalization`,
`lem-weil-finite-free-completed-scalar-comparison`, and
`lem-weil-pbc-condensed-flat-coefficient-calculus`; those belong to the generator's recorded
calculation. No existing module is pruned.

## Where the brief, the DAG or earlier work was wrong

The item was quarantined by the red-build rework after an unrelated dependency failure. The
restored reduction follows the already reviewed D6 repair route. No statement or target
signature was changed. The prior hollow public generator data definition remains removed;
only the named generator theorem is retained as the split-off obligation.

## New nodes

`lem-sf-native-compact-support-finite-scalar-coherence-generator` records the fixed-stage
generator calculation and is stated in
`lean/Sheaf/Paper/NativeCompactSupportFiniteScalarCoherenceGenerator.lean`.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.NativeCompactSupportFiniteScalarCoherence": "16ce0cc44566cdb0cb6712aa32de91f4ca5b86ba", "Sheaf.Paper.NativeCompactSupportFiniteScalarCoherenceGenerator": "10cf8f20a565c62191616bb1df660ce573e288dd"}, "results": {}, "time": "2026-10-28T06:27:28+0800", "transitive": 0, "version": 1}
```

## Second reading by V4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
