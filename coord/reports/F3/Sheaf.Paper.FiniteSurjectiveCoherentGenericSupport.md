## What changed

Replaced the sorry in `AlgebraicGeometry.Scheme.exists_coherent_pushforward_support_eq_range` with a
construction from the reduced induced closed subscheme of the closure of a lift of the generic point.
The proof uses coherence of finite pushforwards, finite type support closedness, sectionwise pushforward,
and stalk germ calculations. Removed proof-only imports of `ClosedPushforwardStalks`, `TensorPullback`,
and `ReducedSourceFactors`.

## Proved and sorry left

The declaration `exists_coherent_pushforward_support_eq_range` is proved with no sorry left.

## No longer needed

Removed imports and corresponding DAG proof dependencies for
`lem-weil-pbc-closed-pushforward-stalks`, `lem-weil-pbc-tensor-pullback`, and
`lem-weil-pbc-reduced-source-factors-through-closed-subscheme`; the direct sectionwise support and
factorization arguments make them unnecessary.

## Where the brief, the DAG or earlier work was wrong

The planned affine integral-extension calculation is unnecessary. The stalk nonvanishing follows by
using the unit section and the stalk germ equality, while maximal-ideal annihilation follows directly
from the defining vanishing ideal and residue evaluation.

## Second reading by F3

1. I compared the delivered module with the repository version. The theorem signature and all
existing declarations are unchanged; only the proof and proof-only imports differ. Verdict: pass.
2. I compiled the module with `lcompile.py`; it is error-free and contains no `sorry`, `axiom`,
`unsafe`, `opaque`, `extern`, or `implemented_by`. The construction is explicit and no definition
uses postponed data. Verdict: pass.
3. The proof uses the reduced vanishing subscheme, coherence of finite pushforward, sectionwise
pushforward, and stalk germ calculations. The support and maximal-ideal arguments are direct and
the resulting statement has the original strength. No new statement was split off. Verdict: pass.
4. The direct proof is shorter than the planned affine route. The removed proof-only imports and
their DAG dependencies are no longer needed; the unit route's construction of the reduced closure,
coherent pushforward, generic stalk, annihilation, and support remains represented. Verdict: pass.
5. The node's proof dependencies and origin were updated to match the actual proof, with the
factorization and closed-pushforward-stalk dependencies pruned. Verdict: pass.

I changed the proof-only imports, replaced the theorem proof, pruned the two unused DAG dependencies,
and recorded this second reading.
