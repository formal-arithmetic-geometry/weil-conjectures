## What changed

Added `Sheaf.Paper.FiniteQuotientLayerLocalComplexCore`, a chartwise intermediate
statement for the finite coefficient-layer calculation. The assigned theorem now
pulls back the residue-model sieve and applies this chartwise result on every
refinement. The assigned theorem's signature is unchanged.

## Proved and sorry left

The original `AlgebraicGeometry.Scheme.finiteQuotient_layer_local_complexes` hole
is reduced to the strictly simpler chartwise theorem
`AlgebraicGeometry.Scheme.finiteQuotient_layer_local_complex_core`.
The new theorem has exactly one `sorry`, with its proof supplied in its docstring
and node. No sorry occurs in a definition.

## No longer needed

The original direct proof dependencies concerning derived restriction and constant
module exactness are not imported into the assigned module; the outer proof only
needs the new chartwise core. No existing module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The original DAG proof combined the layer tensor calculation, finite-term
construction, homology comparison, and sieve transport in one step. The Lean
interface has no single theorem for that combination, so the chartwise calculation
is split into a strictly smaller intermediate statement. The unit route and the
assigned statement are unchanged.

## New nodes

`lem-weil-pbc-finite-quotient-layer-local-complex-core` is added for the chartwise
finite complex and homology comparison; its Lean declaration is in
`Sheaf.Paper.FiniteQuotientLayerLocalComplexCore`.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.FiniteQuotientLayerLocalComplexCore": "affe3d9689b5254c2cb0c0db6dffa0e977759eca", "Sheaf.Paper.FiniteQuotientLayerLocalComplexes": "0b316b6b56e37055b5263dd937475ea306f520d3"}, "results": {}, "time": "2026-10-28T00:34:07+0800", "transitive": 0, "version": 1}
```

## Second reading by W2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
