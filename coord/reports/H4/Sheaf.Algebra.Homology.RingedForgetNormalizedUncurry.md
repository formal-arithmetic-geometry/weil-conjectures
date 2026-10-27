## What changed

Replaced the proof hole in
`CategoryTheory.RingedForgetTensorTransposition.ringed_forget_normalized_uncurry`.
The original public statement and public import stay unchanged. Private proof imports
reuse the existing generic evaluation-on-models, evaluation-transport and transposition
lemmas from `RingedSliceRepresentativeEvaluation`, `RingedSliceEvaluationCoherence`
and `RingedSliceEvaluationTranspose`, and the explicit chain adjunction from
`RingedDerivedTensorHomAdjunction`.

The proof first extends the two-injective Hom representative square to arbitrary
source complexes by naturality and cancellation along a K-injective resolution.
For a K-flat P and K-injective I it resolves Hom(P,I) by a flat-term K-flat complex,
compares the two ordinary evaluations, and applies the given tensor and Hom
representative squares. Naturality transports evaluation compatibility to all
derived objects. The final adjunction calculation gives the required uncurry equation.

Added `Sheaf.Algebra.Homology.RingedForgetChainUncurry`, proving the actual chain-map
comparison from the tensor summand, Hom projection and underived evaluation equations.
Its proof checks tensor summands and canonical sheaf pure tensors. It assumes only
additivity of U, with no exactness, flatness, K-injectivity or derived-category data.
All auxiliary definitions are
explicit constructions; existential resolution choices occur only in theorem proofs.
The naturality extension of the Hom representative square is in the new
module `Sheaf.Algebra.Homology.RingedForgetHomRepresentative`, to keep each compile
within the per-file limit. Pure comparison-data construction is also performed
in general categories before specializing to sheaves. The representative evaluation calculation is likewise
in `Sheaf.Algebra.Homology.RingedForgetRepresentativeEvaluation`; the assigned module
only transports that equation and applies transposition. No existing module other
than the assigned item is changed.

## Proved and sorry left

Closed the original single hole:
`CategoryTheory.RingedForgetTensorTransposition.ringed_forget_normalized_uncurry`
(node `lem-sf-ringed-forget-normalized-uncurry`).

The new theorem
`CategoryTheory.RingedForgetTensorTransposition.ringed_forget_chain_uncurry`
(node `lem-sf-ringed-forget-chain-uncurry`) is proved, with no split-off hole.
The new theorem
`CategoryTheory.RingedForgetTensorTransposition.ringed_forget_hom_representative`
(node `lem-sf-ringed-forget-hom-representative`) is also proved. No `sorry` remains
in the delivered modules, and no hole is added elsewhere. The representative theorem
`CategoryTheory.RingedForgetTensorTransposition.ringed_forget_representative_evaluation`
(node `lem-sf-ringed-forget-representative-evaluation`) is fully proved as well.
The statements used from existing modules may retain their existing dependencies;
this packet does not claim to close those other items.

Compiler verification: all four delivered modules compiled through `lcompile.py`,
with the enforced 60-second Lean limit. The chain and Hom helpers passed the combined
check; after generalizing comparison-data construction, the representative-evaluation
module and assigned module passed together. The original theorem signature was
compared textually against the shared repository and is unchanged. No profiler
settings remain. The shorter proof does not use the original product-preservation
binder. The private evaluation helper omits it; the original public theorem keeps
it, with its unused-section-variable lint disabled locally and an explanatory
comment. This preserves the original public signature.

## No longer needed

The evaluation-first argument does not directly use
`lem-coef-hom-kflat-into-kinjective-independent-coefficients`
(`Sheaf.Algebra.Homology.KInjectiveHomComplexOfUniverses`) to establish K-injectivity
of Hom(P,I), or `lem-sc-kinjective-quasi-iso-comparison` to lift the arbitrary
arrow f. Their direct proof-dependency entries are removed from this node.
`def-pur-hom-complex` remains a statement dependency and is used inside the new
chain calculation, rather than as an additional direct step of the derived proof.
The old direct entries `lem-sf-ringed-forget-two-injective-hom`,
`lem-weil-pbc-exact-functor-derived-factorization` and
`lem-sf-ringed-forget-tensor-descent` are now represented through the new proved
helper nodes. They remain needed transitively; moving them is not closure pruning.

No original import is removed and no module is withdrawn. In particular,
`KInjectiveHomComplexOfUniverses` is still privately imported by the new chain
module to access its existing independent-universe sheaf tensor-Hom equivalence;
no claim is made that this module has left the targets' import closure.
No declarations in the adopted source tree are removed.

## Where the brief, the DAG or earlier work was wrong

The original plan is mathematically adequate but asks for more representation
work than is necessary. Comparing the evaluation counits suffices by the existing
adjunction naturality calculation, so no lift of an arbitrary derived f into
Hom(P,I), no comparison between two fixed target resolutions and no localization
injectivity step are needed. The node proof and proof dependencies now describe
this shorter route. The unit statement and its realized route are preserved.
The original theorem docstring records the earlier plan; the updated node and
this report record the implementation.

## New nodes

`lem-sf-ringed-forget-chain-uncurry`, in
`dag/nodes/sec-six-functors/lem-sf-ringed-forget-chain-uncurry.json`, realizes
`Sheaf.Algebra.Homology.RingedForgetChainUncurry`. It isolates the ordinary chain
calculation from step 2 of the parent's argument and is fully proved here.
The statement is valid for arbitrary unbounded complexes: the proof tests maps
after the inverse tensor isomorphism, where target summands detect equality, so
it does not assume U preserves coproducts. Zero complexes and zero maps require
no exclusions; the proof uses only naturality, the stated curry equations and
cancellation of specified isomorphisms. No change record is required: no existing
public statement or definition is changed.

`lem-sf-ringed-forget-hom-representative`, in
`dag/nodes/sec-six-functors/lem-sf-ringed-forget-hom-representative.json`, realizes
`Sheaf.Algebra.Homology.RingedForgetHomRepresentative`. It extends the supplied
representative square from K-injective sources to arbitrary sources by naturality
and cancellation along a localized K-injective resolution, then composes with
an arbitrary chain map q into Hom(K,I) and the inverse representative models.
The target I remains K-injective. The categorical calculation is proved privately
for general abelian categories, avoiding repeated unfolding of the sheaf constructions.
This is a strictly smaller step of the argument, contains no tensor
comparison or uncurrying assertion, and has no proof hole.

`lem-sf-ringed-forget-representative-evaluation`, in
`dag/nodes/sec-six-functors/lem-sf-ringed-forget-representative-evaluation.json`,
realizes `Sheaf.Algebra.Homology.RingedForgetRepresentativeEvaluation`. It proves
evaluation compatibility for flat-term K-flat P and K-injective I. The assigned
module supplies the nontrivial additional steps: transportation to arbitrary
derived K,L and the adjunction argument for every M,f. This extra module keeps
the model calculation separate from those steps for the per-file compile limit;
it adds no hole.

## Second reading by H4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
