## What changed

Implemented the flat scalar evaluation model from the recorded ordinary and derived
scalar adjunctions, natural tensor comparisons, strict coefficient maps and
scalar-Hom comparison tower. The chain evaluations and unit map are actual
constructions with proofs of their generator formulas.

Separated the tensor-only exact representative identity from postcomposition with
Hom evaluation. Its assertion concerns one K-flat right factor, an arbitrary first
complex, and the scalar unit; it has no Hom or K-injective input.

## Proved and sorry left

Closed the one original hole, `CategoryTheory.FlatScalarEvaluation.model_exists`.
There are zero remaining `sorry` occurrences in the item and zero added holes.
The five new theorem modules are completely proved: ordinary construction,
ordinary coefficient squares, ordinary resolution compatibility, the exact tensor
representative, and arbitrary-derived coefficient coherence. No unfinished result
is split off. The complete model and all five new modules compile on the project server.
The unchanged consumer also exceeds the compile limit against the original library;
its check is reported separately and no consumer proof is replaced by a hole.

## No longer needed

The proof does not use `Sheaf.Algebra.Homology.PrincipalKoszulQuotientTowers` or
`Sheaf.CategoryTheory.ExactFunctorDerivedFunctor`; both proof imports were removed.

The three exact-functor nodes
`lem-weil-pbc-exact-functor-complex-cohomology`,
`lem-weil-pbc-exact-functor-derived-factorization` and
`lem-weil-pbc-exact-functor-derived-functor` are unnecessary here. The K-flat
normalization of the already recorded universal counit, its naturality and exact
preservation of quasi-isomorphisms prove the comparison directly.

The separate node `lem-sfb-scalar-hom-chain-coefficient-coherence` is unnecessary
here: the proved generic coefficient compatibility in `StrictScalarHomChain`
applies directly to the canonical strict data. No upstream declaration is removed.

The proof also does not need `lem-sfb-hom-kflat-chain-transpose`: the natural
comparison from `lem-sfb-ringed-tensor-comparison-extension` supplies the
representative isomorphism and its two required equations directly.

## Where the brief, the DAG or earlier work was wrong

The planned exact-functor factorization is longer than needed. The scalar tensor
normalization can be extended to an arbitrary first factor directly by naturality
and a resolution; no resolution of the restriction of its extension is needed.
The tensor-only derived calculation is then the ordinary scalar adjunct of the
normalized chain tensor comparison.

## New nodes

`lem-sfb-scalar-tensor-exact-representative`, in
`Sheaf.Algebra.Homology.ScalarTensorExactRepresentative`, records the tensor-only
identity before postcomposition with evaluation. Its proof is strictly a part of
the model construction. It has no Hom or K-injective input and uses a single
K-flat right factor, with no termwise-flatness premise.

`lem-sfb-ordinary-scalar-evaluation-model`, in `ScalarOrdinaryEvaluationModel`,
constructs the ordinary chain evaluation and unit tensor maps independently of
any derived-category choices. All maps satisfy the original generator formulas.

`lem-sfb-ordinary-scalar-evaluation-square`, in
`ScalarOrdinaryEvaluationCoefficientSquare`, proves compatibility with each strict
coefficient square by the two identical generator evaluations. Its private
composite lemma identifies the chain expression used in derived evaluation.

`lem-sfb-ordinary-scalar-evaluation-resolution`, in
`ScalarOrdinaryEvaluationResolution`, proves preservation of all four resolution
maps and naturality of scalar evaluation. It requires neither K-flatness of the
resolved first complex nor K-injectivity of the evaluation target.

`lem-sfb-scalar-hom-derived-square-coherence`, in
`ScalarHomDerivedSquareCoherence`, proves arbitrary-derived naturality, tower,
identity and square coherence independently of chain representatives.

The original item definitions, record layouts, normalization conditions, theorem
signature and public imports are preserved. No definition repair, source-library
change or target change is delivered.

## Second reading by R2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
