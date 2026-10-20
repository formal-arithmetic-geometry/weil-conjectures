## What changed

Proved `Ideal.quasiRegular_prefix_quotient` in
`Sheaf.RingTheory.QuasiRegularPrefixQuotient`. Both definitions and the public theorem
statement are unchanged. Added only private, proved helpers and a proof-only import of
`Mathlib.RingTheory.MvPolynomial.Homogeneous`.

The proof uses homogeneous coefficient relations to implement Stacks 061R's
one-generator argument, then inducts on the prefix length. Its coefficient calculations
generalize the private proofs in `RegularSequenceGradedPolynomial` to the tail subtype;
they use the existing associated graded product/scalar formulas directly. No import of
that regular-sequence theorem is needed. The canonical coefficient-ring identification
is Mathlib's third isomorphism theorem, with its formula on representatives.

Updated the node's proof plan to match this coefficient formulation. All four declared
proof dependencies are retained and used; the unit route is unchanged.

Validation: the complete module compiled through `lcompile.py` with no warnings or
remaining `sorry`. Degree zero, an empty original sequence, an empty tail, and zero
coefficient rings are covered by the proof without nontriviality assumptions.

## Proved and sorry left

Closed 1 of 1 original holes: `Ideal.quasiRegular_prefix_quotient`
(node `lem-pur-quasi-regular-prefix-quotient`). Added 0 holes; split off 0.
There are no remaining `sorry` declarations in this delivery.

## No longer needed

No original imports, declared dependency nodes, or modules were pruned.
The formal proof avoids constructing a separate associated graded quotient homomorphism
and instead compares coefficients of homogeneous lifted relations. The initially tried
explicit proof-only import of `Mathlib.Algebra.MvPolynomial.Rename` was removed because
it is already supplied by the homogeneous-polynomial import.

## Where the brief, the DAG or earlier work was wrong

No statement defect found. The original node's eight-step proof is mathematically valid;
the revised plan records the coefficient version actually formalized. The existing
`RegularSequenceGradedPolynomial` coefficient helpers are private and specialized to
`Fin c`, so they cannot directly serve the subtype-indexed tail. Their elementary
arguments are generalized privately here rather than changing another module's API.

## Second reading by K2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
