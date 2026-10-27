## What changed

Completed `WeilConjectures.CompactSupportFiniteProjection.binary_square_on_triangle`
in `Sheaf.Paper.FiniteProjectionBinaryTriangleSquare`. Added the private proof import
`import all Sheaf.Paper.FiniteProjectionBinaryIterationTrianglePasting`; preserved the existing
public imports, definitions and theorem signatures.

The proof uses `binary_composition_realization` for the two projection-free boundary
normalizations, `binary_iteration_triangle_pasting` for the iterated projection edge,
and `compositionProjectionMate` for the ordinary triangle equation and invertibility
of its comparison. Private proved helpers normalize the total factor projection,
including its equality transport, cancel the source/target conjugations, paste the
square, and reflect it through the faithful constructible inclusion. The coefficient
law is applied at every positive level using the existing `hn`, with no added
hypothesis or invertibility assumption on a projection.

The total-factor argument reuses the already proved private
`fixed_factor_projection_refl` in `FiniteProjectionBinaryIterationTrianglePasting`.
It first generalizes and eliminates the equality indexing the compactification;
the pullback transport is then the identity. Its identity calculation is proved
at arbitrary categories and functors before specialization. The DAG records this
route. No other existing module was changed and no new module or node was added.

Searches: LeanFinder for faithful reflection and isomorphism transport of a square;
Loogle for `CategoryTheory.Functor.map_injective`; launcher grep and local `rg` for
`paste_realized_square`, `binary_composition_realization`, and `factor_projection`.
The project-specific boundary normalizations have no Mathlib replacement; generic
faithfulness, functoriality, associativity and cancellation suffice for the glue.

Validation: the clean full module compiled through `lcompile.py` in 17.6 seconds,
with no errors or warnings. The existing public definition and theorem signature
were checked verbatim against the shared source.

## Proved and sorry left

Closed 1 of the item's 1 holes:
`WeilConjectures.CompactSupportFiniteProjection.binary_square_on_triangle`
(node `lem-sf-finite-projection-binary-triangle-square`).

Added 0 holes; split off 0 statements. No `sorry` remains in the delivered module.
This is a proof from the existing declared dependencies, including
`binary_composition_realization`; it does not claim those dependencies are all
independently sorry-free.

## No longer needed

No imports or modules were removed; no node is withdrawn. The separate direct
proof dependency on `lem-sf-finite-projection-iteration-realization` is redundant
because the proof uses `binary_iteration_triangle_pasting`. That iteration node
remains needed transitively through the pasting and composition-realization modules.

## Where the brief, the DAG or earlier work was wrong

The original one-step proof dependency list omitted the projection-free composition
normalization and the ordinary raw triangle law that its proof text called for.
The updated node makes those dependencies and the elementary endpoint/pasting
calculation explicit. The theorem statement itself required no repair.

A direct calculation with the equality transport exceeded the kernel checking
limit. Eliminating the factorization equality first avoids that conversion and
reduces the calculation to the already proved factor identity. No timeout or
heartbeat setting is raised.

The current server queue was checked: it lists an ordinary stage-3 proof item
with one hole. Its old build-error file reports unavailable dependency imports;
the proof compiles against the currently published dependency artifacts.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.FiniteProjectionBinaryTriangleSquare": "56df9dad5b014e1fa5552a1992dcdbc3255d6063"}, "results": {"Sheaf.Paper.FiniteProjectionBinarySquare": {"hash": "6c3902bd17672dafe7eeed3a47aa806dbb6ee6bf", "status": "OK"}}, "seconds": 59, "time": "2026-10-28T03:10:34+0800", "transitive": 0, "version": 1}
```

## Second reading by E4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
