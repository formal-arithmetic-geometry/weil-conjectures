## What changed

Proved `RationalPolynomialBar.coface_retraction_identities` in the assigned module,
with all fourteen clauses and its original signature unchanged. Added proved
private helpers for coface substitutions, finite-sum cancellation, ordered
coordinate products, weighted homogeneity, the coefficient formula for projection,
and its behavior under block permutations. Added private Mathlib proof imports
for finite sums, variable renaming, and permutation signs.

The projection argument uses an involution on injective coordinate tuples. A
merge is invariant under exchanging the two merged blocks. Such an exchange
preserves the relevant coefficient and subset, and negates the sorting sign by
Mathlib's antisymmetric-product permutation formula. This proves each inner
coface has zero projection; omitted blocks handle the outer cofaces.

Updated the item's DAG proof and proof origin to describe these calculations.
All definitions, public imports, and public declaration signatures are preserved.
No other existing module or node was changed.

## Proved and sorry left

Closed the one original hole:
`RationalPolynomialBar.coface_retraction_identities`
(node `lem-sfb-polynomial-bar-coface-retraction-identities`).

There are zero remaining holes in the item and zero holes added by this delivery.
No statements were split off. The proof uses the concrete constructions from
`RationalPolynomialBarContraction`, without its `contraction` or
`differential_squared` theorems. The latter's existing hole remains in that other
module and was not counted as closed.

Validation: the complete module is compiled through `lcompile.py`; the delivery
preflight independently checks the complete proof and its declaration axioms.

## No longer needed

None. No original import, declared dependency, node, or module was pruned.
`def-weil-pbc-mv-polynomial-ring` remains the construction dependency.
The proof replaces the planned quadratic-block case analysis with the shorter
permutation-sign pairing, so that case analysis needs no additional split nodes.

## Where the brief, the DAG or earlier work was wrong

No statement correction was needed. The DAG's elementary projection-cancellation
argument can be shortened by pairing tuples using invariance under a block swap.
This works over every commutative ring, including the zero ring, without division.
The theorem retains its prescribed rational-algebra assumption.

## Second reading by A5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
