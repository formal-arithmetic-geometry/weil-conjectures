## What changed

The generator theorem now reduces an arbitrary common-stage object to the
rationalization of a finite-Tor integral representative. The residue-Tor
comparison constructs that representative, and the new integral-generator
theorem supplies the remaining fixed-numerator calculation. The original
target signature is unchanged.

## Proved and sorry left

Closed `native_compact_support_finite_scalar_coherence_generator` by a complete
Lean reduction to the integral finite-Tor theorem and
`integral_residue_tor`. Added one strictly smaller named split theorem,
`native_compact_support_finite_scalar_coherence_generator_integral`, whose proof
remains `by sorry` and records the actual coefficient-mate calculation.

## No longer needed

The assigned generator module no longer directly uses the five former
calculation dependencies (`lem-sf-constructible-exceptional-coefficient-coherence`,
`lem-sf-native-integral-scalar-morphism`,
`lem-sfb-pasted-mates-counit-normalization`,
`lem-weil-finite-free-completed-scalar-comparison`, and
`lem-weil-pbc-condensed-flat-coefficient-calculus`). They remain dependencies of
the new integral-generator node, where the unresolved calculation is isolated.
No existing module is pruned.

## Where the brief, the DAG or earlier work was wrong

The parent reduction had already isolated the finite-Tor numerator calculation,
but the generator statement still quantified over an arbitrary stage object.
The direct declarations in the dependency list do not state the coefficient
mate calculation needed to prove that numerator case. I made the missing
strictly smaller numerator theorem explicit and kept the original statement
unchanged. No target statement or upstream declaration was changed.

## New nodes

`lem-sf-native-compact-support-finite-scalar-coherence-generator-integral` records
the fixed finite-Tor numerator calculation and is stated in
`lean/Sheaf/Paper/NativeCompactSupportFiniteScalarCoherenceGeneratorIntegral.lean`.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.NativeCompactSupportFiniteScalarCoherenceGenerator": "1bea54cd64d56929477f189fa8a3ccb213dcd741", "Sheaf.Paper.NativeCompactSupportFiniteScalarCoherenceGeneratorIntegral": "312c6a903ef60d2d67095a96b460dfed1f18039e"}, "results": {"Sheaf.Paper.NativeCompactSupportFiniteScalarCoherence": {"hash": "16ce0cc44566cdb0cb6712aa32de91f4ca5b86ba", "status": "OK"}}, "seconds": 113, "time": "2026-10-28T08:05:51+0800", "transitive": 0, "version": 1}
```

## Second reading by J9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
