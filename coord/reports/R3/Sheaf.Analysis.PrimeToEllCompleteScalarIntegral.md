## What changed

Filled `WeilConjectures.primeToEll_completeScalar_integral` without changing its
statement, definitions, public imports, or existing docstrings. The proof imports
`Sheaf.Analysis.FiniteQuotientContractiveAverage`,
`Sheaf.Topology.OpenNormalQuotientFunctionsDense`, and
`Sheaf.Topology.CompactParameterFunctional` privately. It equips B locally with
the normed Padic-algebra structure induced by the given isometric ring map,
extends the finite-quotient average by `LinearMap.extendOfNorm`, and proves
translation invariance by equality of continuous functions on the dense
subspace. Quotient finiteness identifies the dependency's finite sum with the
statement's topological sum. The compact-parameter theorem gives all remaining
clauses, specializing its finite-sum identity to `Fin n`.

This realizes all four existing DAG steps; the dense-range equalizer is the
uniqueness argument in step 3. Updated the item node's proof and proof origin to
record the precise interface bridges and the continuous equalizer argument.
Searches with LeanFinder, Loogle and Mathlib/source-tree grep confirmed the existing dense
extension API; the semantic integration hits concern real Haar integration and
do not replace the stated nonarchimedean inputs.

## Proved and sorry left

Closed 1 of 1 holes: `WeilConjectures.primeToEll_completeScalar_integral`
(`lem-sfb-prime-to-ell-complete-scalar-integral`). Added 0 holes; no sorry remains
in the delivered module. The three existing auxiliary declarations are used as
stated, with their own existing proof obligations unchanged. This is a proof
from the assigned dependencies, not a new decomposition. The server single-file
compile passed with no errors or warnings in 4.5 seconds.

## No longer needed

Removed the private import `Mathlib.Topology.Separation.DisjointCover`: finite
approximation is encapsulated by the existing quotient-function density theorem.
No declared dependency, DAG node, or Sheaf module is pruned. All four planned
analytic inputs remain used, and the unit route is preserved.

## Where the brief, the DAG or earlier work was wrong

No mathematical discrepancy found. The finite-average dependency uses a
`NormedAlgebra (Padic ell) B` instance rather than the item's explicit isometric
ring embedding; the local induced algebra and its norm proof bridge these
interfaces without changing either statement. Its finite sums and the item's
`tsum` agree because every open-normal quotient is finite.

## Second reading by R3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
