## What changed

Repaired `WeilConjectures.completedPullbackTensor_evaluation_cube_model` to use
`finitePullbackTensorConstructionIso`, the canonical finite comparison already
specified by its mathematical node. Removed its unconstrained `ν` binder. The
sole parent, `Sheaf.Paper.CompletedPullbackTensorEvaluationRepresentatives`,
already supplied this canonical comparison; its proof drops that extra argument.
Every parent signature, visibility, attribute and public import is unchanged.
No target or adopted source-library declaration changes.

Proved the canonical cube by a unit calculation, total pure-generator
extensionality, the ordinary cochain square, its functorial quotient image,
exact-functor factorization naturality, and tensor-model cube pasting. The new
modules isolate these proved steps and the finite-model transport face. Local
transparency choices and explicit types for factor isomorphisms avoid repeated
inference across large coefficient-module structures. No shared definition or
instance is changed. A proved private `cochain_comp3_section` lemma computes
composition with its complexes abstract, avoiding a concrete `rfl` which unfolded
the total tensor's module structures repeatedly. The unit route is retained.

Validation: `lcompile.py --all` compiled all fourteen delivered Lean files, one
at a time in import order, with no errors or warnings and each under 60 seconds.
The slowest file was the raw diagonal at 58.0 s; the cube took 37.5 s and its
adapted parent 15.5 s. Static checks find zero holes, no forbidden declarations,
no profiling options, and exact agreement between every node signature and Lean.
The current server claim still assigns the cube to Q1 and leaves the parent
unclaimed; the assigned queue reason remains the disputed route.

## Proved and sorry left

The item began with one `sorry`, in
`WeilConjectures.completedPullbackTensor_evaluation_cube_model`. After correcting
its false arbitrary-comparison signature to the canonical statement of its node,
that statement has a complete proof. This does not claim to prove the former
arbitrary-`ν` statement. The item has zero remaining holes; the delivery adds zero
holes. Every new public theorem and every private helper is proved.

New proved declarations:

- `WeilConjectures.completedPullbackTensor_evaluation_unit`
- `WeilConjectures.completedPullbackTensor_evaluation_inverse_unit`
- `WeilConjectures.completedPullbackTensor_evaluation_generators`
- `WeilConjectures.finitePullbackTensor_unit_ext`
- `WeilConjectures.completedPullbackTensor_evaluation_ext`
- `WeilConjectures.completedPullbackTensor_evaluation_cochain`
- `WeilConjectures.completedPullbackTensor_evaluation_quotient`
- `WeilConjectures.completedPullbackTensor_evaluation_factors`
- `WeilConjectures.completedPullbackTensor_evaluation_diagonal`
- `WeilConjectures.completedPullbackTensor_evaluation_model_diagonal`
- `WeilConjectures.completedPullbackTensor_evaluation_model_transport`
- `WeilConjectures.completedPullbackTensor_evaluation_pasting`

There are no split-off unfinished obligations. Existing dependency proofs are
used with their recorded statements; their holes, if any, are unchanged.

## No longer needed

No existing module, node, public import or declaration is withdrawn. The three
original public imports of the item remain. The false arbitrary-comparison route
is replaced by the canonical ordinary generator argument, not by pruning the
unit or bypassing any parent. No unused adopted-source declaration is removed.
Temporary profiling and scratch modules are excluded from the delivery.

## Where the brief, the DAG or earlier work was wrong

STATEMENT-DISPUTED (former signature): the Lean theorem allowed an arbitrary
finite tensor natural isomorphism `ν`, with no normalization hypothesis. The
node's mathematical statement instead specifies the canonical finite comparison.
The old proof step incorrectly claimed that the other faces alone identified
an arbitrary `ν`. Multiplying the canonical comparison by minus one on a nonzero
tensor over an odd-characteristic quotient changes the conclusion while fixing
all hypotheses. For example take the identity morphism and two degree-zero
constant rank-one modules at a level with odd residue characteristic.

The corrected signature follows the existing mathematical statement. Its proof
uses the actual canonical finite normalization and checks the ordinary square
on all total pure generators, in arbitrary unbounded complexes. No boundedness,
constructibility or termwise-flatness condition is added. The ordinary cochain
and unit-extensionality steps do not need the invertibility assumptions used by
the derived construction.

The ordinary evaluation mate's section formula was not available as a declared
unit lemma. It is now proved from the mate equation and section transports,
rather than assumed. The quotient lemma applies an arbitrary functor; the
specialization to the derived quotient is used in the diagonal face.

## New nodes

`lem-pur-completed-pullback-tensor-evaluation-unit`: proves the ordinary mate's
formula on actual adjunction-unit sections, with a proved degreewise helper.

`lem-pur-completed-pullback-tensor-evaluation-generators`: computes the composite
of evaluated sequence tensor comparison, evaluation tensor comparison and the
tensor of the ordinary mates on unit pure tensors.

`lem-pur-finite-pullback-tensor-unit-ext`: proves that units of total pure tensors
determine maps out of intrinsic finite pulled-back total complexes of evaluated
sequence inputs; section surjectivity justifies testing the evaluated generators.

`lem-pur-completed-pullback-tensor-evaluation-cochain`: proves the complete
ordinary cochain square by transposition and the preceding generator formulas.
It is strictly an ordinary step, with no derived or K-flat hypotheses.

`lem-pur-completed-pullback-tensor-evaluation-quotient`: maps that ordinary equality
through a functor and expands composition. The diagonal uses the derived quotient.

`lem-pur-completed-pullback-tensor-evaluation-factors`: combines two consecutive
quotient maps in the prescribed factorization equation using functoriality.

`lem-pur-completed-pullback-tensor-evaluation-diagonal`: pastes the quotient square
with the two exact-functor naturality squares and the supplied factorization.

`lem-pur-completed-pullback-tensor-evaluation-model-transport`: proves evaluation
normalization after arbitrary isomorphisms of the two finite K-flat factors,
using naturality of the finite tensor-model comparison.

`lem-pur-completed-pullback-tensor-evaluation-pasting`: proves the derived cube
conditionally on its normalized finite and total diagonal faces. It constructs
the four tensor-model corners and pastes the seven faces. The item independently
obtains the finite normalization and proves the total diagonal before invoking it.

`lem-pur-completed-pullback-tensor-evaluation-inverse-unit`: computes the source
unit after the inverse tensor-evaluation and inverse mate maps. This pointwise
formula precedes either tensor comparison and has no finite-comparison k.

`lem-pur-completed-pullback-tensor-evaluation-ext`: proves a criterion for an
ordinary square with arbitrary target H and arbitrary maps a,k. This isolates
source transposition from the concrete tensor target; the cochain theorem then
supplies precisely the two generator normalizations.

`lem-pur-completed-pullback-tensor-evaluation-model-diagonal`: expresses the proved
total diagonal using composite model isomorphisms, with typed cochain functors
and tensors so that the cube consumes the face without repeating normalization.

All twelve new nodes are proved, not new `sorry` items. The change record is
`coord/changes/completed-pullback-tensor-evaluation-canonical.md`.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.CompletedPullbackTensorEvaluationCochain": "1e53c355b1052576d04c110a32589594597b9e89", "Sheaf.Paper.CompletedPullbackTensorEvaluationCube": "6e44a799bd5c04761069c1dd23c2ef7ee4e8360e", "Sheaf.Paper.CompletedPullbackTensorEvaluationDiagonal": "a71d133be2acf582815a782fe140801344e0b9c2", "Sheaf.Paper.CompletedPullbackTensorEvaluationExt": "7157b51cbef59047a8042fd6c96d8c5e5aaca613", "Sheaf.Paper.CompletedPullbackTensorEvaluationFactors": "ca808336b145547c8545fa94f8b8d7b8bbb3c8c7", "Sheaf.Paper.CompletedPullbackTensorEvaluationGenerators": "5055504fd156abcd938945adcc388c96a810b6bb", "Sheaf.Paper.CompletedPullbackTensorEvaluationInverseUnit": "50fa324a2a1016c9b4f745abe97921c6d2865352", "Sheaf.Paper.CompletedPullbackTensorEvaluationModelDiagonal": "a5b6d4732cd65b67e83799f67363e8f814931fd6", "Sheaf.Paper.CompletedPullbackTensorEvaluationModelTransport": "efe6fbe293a01f4f4d54cfea08cb8fafea4e8991", "Sheaf.Paper.CompletedPullbackTensorEvaluationPasting": "cd1c24a1e20ff07898225cb854f90297f4dcb50b", "Sheaf.Paper.CompletedPullbackTensorEvaluationQuotient": "ef3995d751ea1f45e21175f1c84aa26581c6d2d8", "Sheaf.Paper.CompletedPullbackTensorEvaluationRepresentatives": "ab38c4c1dcd91a38e8635b3eaf60b11cd1a3de1e", "Sheaf.Paper.CompletedPullbackTensorEvaluationUnit": "12ff789eeb1b86ed27d1a01315400b7799dea83b", "Sheaf.Paper.FinitePullbackTensorUnitExt": "4910337d5a58abde6ab71e4695fe89722d3f6c10"}, "results": {}, "time": "2026-10-28T04:23:47+0800", "transitive": 0, "version": 1}
```

## Second reading by Q1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
