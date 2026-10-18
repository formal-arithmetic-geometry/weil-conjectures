## What changed

Proved `CategoryTheory.Functor.leftDerivedFunctorFromTotalTensorIsoMapDerivedCategory_hom_fac`
by unfolding the existing canonical comparison and simplifying with Mathlib's
`leftDerivedNatTrans_fac` and the identity-composition law. This is the same
factorization argument used by the source library's analogous
`leftDerivedFunctorIsoMapDerivedCategory_hom_fac`, without importing that stronger
K-flat interface. The server compiled the module cleanly in 2.1 seconds.
No signatures, definitions, imports, or DAG proof routes changed.

## Proved and sorry left

Closed the sole hole:
`CategoryTheory.Functor.leftDerivedFunctorFromTotalTensorIsoMapDerivedCategory_hom_fac`
(node `def-sfb-left-derived-exact`). Proved 1 of 1 sorries; added 0 holes;
0 sorries remain in the delivered module. The existing upstream dependencies on
the total-tensor preservation theorem and derived universal property remain as
recorded by the node; this delivery does not claim to prove them.

## No longer needed

None. All three existing public imports are needed by the statements or the
canonical comparison definition. Both recorded dependency nodes,
`def-sfb-preserves-kflat-quasi-iso` and `def-sfb-left-derived-functor`, remain used.
The proof uses no additional modules or nodes.

## Where the brief, the DAG or earlier work was wrong

No correction needed. The outstanding counit equation is already the generic
Mathlib factorization law for the uniqueness isomorphism. The source library
contains the analogous simplification proof, but its stronger graded-tensor
hypotheses make direct reuse of that declaration inappropriate here.

## Second reading by N4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
