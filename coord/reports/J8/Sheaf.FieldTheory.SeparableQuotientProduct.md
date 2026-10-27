## What changed

Filled `Polynomial.exists_eval_quotient_algEquiv_pi_of_separable` without changing its
statement. Mathlib's `Polynomial.exists_finset_of_splits` factors the mapped polynomial
into a finite set of distinct linear factors. Evaluation identifies this finite set with
the root subtype; taking degrees proves its cardinality is `n`. The existing proved
`Polynomial.quotient_prod_X_sub_C_algEquiv_pi` supplies the evaluation equivalence, which
is transported along the factorization and reindexed by the root subtype.

## Proved and sorry left

Closed 1 of 1 holes:
`Polynomial.exists_eval_quotient_algEquiv_pi_of_separable`
(node `lem-pc-separable-polynomial-alg-closed-quotient-product`).
Added 0 holes; no sorry remains in the delivered module. No decomposition.

## No longer needed

None. Both declared proof dependencies are used: the Mathlib distinct-root
factorization leaf and `Sheaf.RingTheory.PolynomialDistinctLinearCRT`.
No module or DAG node is withdrawn. The existing unit route is retained.

## Where the brief, the DAG or earlier work was wrong

No mathematical or interface defect was found. The finite-set factorization avoids
separate manipulation of the roots multiset. The proof includes degree zero: the root
set is empty, and the existing CRT theorem handles the empty product. No positivity
hypothesis or restriction on characteristic is introduced.

Searches: Lean Finder found linear-factor quotient equivalences but no complete theorem;
Loogle found `Polynomial.exists_finset_of_splits`; the launcher grep and local source
searches confirmed the existing factorization, degree, CRT, quotient transport and
product reindexing APIs. The existing node's three-step proof and proof dependencies
already describe the completed argument, so they need no update.

## Second reading by J8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
