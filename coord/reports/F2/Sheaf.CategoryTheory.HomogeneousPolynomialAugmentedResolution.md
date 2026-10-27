## What changed

The original theorem
`Profinite.CondensedAction.HomogeneousPolynomial.homogeneous_polynomial_augmented_resolution`
is proved from two separate construction steps. Its signature is unchanged. The seven
supporting data declarations are moved verbatim to
`Sheaf.CategoryTheory.HomogeneousPolynomialResolutionData` and publicly reexported by the
item. The original public imports stay. This avoids cycles between the specifications,
new construction statements, and the theorem that combines them.

`HomogeneousPolynomialModelExistence.model_nonempty` states the existence of the pinned
equivariant complex, faces and augmentation. `HomogeneousPolynomialContractionExistence.
contraction_nonempty` states the inserted-zero contraction of every pinned model. Both are
valid for any normed coefficient field over Q_ell, including the two fields of the target
and rank zero. Neither includes the quasi-isomorphism conclusion.

The item proves `exact_of_contraction` and `augmentation_quasiIso` as private helpers.
The first sandwiches the contraction identity between a kernel inclusion and cokernel
projection. The second reflects underlying exactness with
`CondensedDerivedRestriction.forgetExact`, proves the degree-zero augmentation monic using
its split underlying retraction, and applies the short-complex quasi-isomorphism criterion.
Negative degrees use the specified zero objects. Derived localization then supplies the
last clause of Assertion. The finite field and algebraic closure cases use the same proof.
No equivariance of the contraction and no completeness of the coefficient field is assumed.

Change record: `coord/changes/F2-homogeneous-polynomial-resolution-data.md`.
There are no current direct Lean importers of the item, confirmed by exact import search
and `tools/downstream.py`; its pending DAG parent is preserved. A scratch consumer checks
that the original import still exports the complete interface.

Validation: `lcompile.py --all` compiled the shared data (15.7 s), contraction
statement (5.3 s), model statement (5.6 s), original item (16.2 s) and scratch
public-interface consumer (5.6 s), without warnings. All files are below 60 seconds.
The consumer checked all seven data names and the unchanged theorem signature through
only the original public import. Its axiom print contains the three standard axioms and
`sorryAx`, as expected from the two construction holes and pre-existing postponed
infrastructure. The scratch consumer was removed before delivery. A byte comparison
confirmed the moved declaration block is verbatim; all Lean lines meet the width limit.

## Proved and sorry left

Original holes closed: 1, in
`Profinite.CondensedAction.HomogeneousPolynomial.homogeneous_polynomial_augmented_resolution`
(node `lem-sfb-homogeneous-polynomial-augmented-resolution`). The item's module has zero
remaining holes. Its homological deduction and both private helpers are complete proofs.

Holes added: 2, each the entire proof of a public named theorem:

- `Profinite.CondensedAction.HomogeneousPolynomial.model_nonempty`, node
  `lem-sfb-homogeneous-polynomial-model-existence`, in
  `Sheaf.CategoryTheory.HomogeneousPolynomialModelExistence`.
- `Profinite.CondensedAction.HomogeneousPolynomial.contraction_nonempty`, node
  `lem-sfb-homogeneous-polynomial-contraction-existence`, in
  `Sheaf.CategoryTheory.HomogeneousPolynomialContractionExistence`.

This is a decomposition, with a net increase of one textual hole, not a claim that the
resolution is proved without postponed dependencies. The two remaining statements cover
separate steps of the original plan (1-3 and 4-5); neither is the original theorem under a
new name. Each has a source, full natural-language proof, matching DAG node and exact
`:= by sorry` proof. The shared data module has zero holes.

## No longer needed

The item's old private imports of
`Mathlib.CategoryTheory.Sites.Coherent.SheafComparison` and
`Sheaf.CategoryTheory.SheafTensor` are removed from the homological assembly. Their
construction role remains in the model-existence node's proof dependencies. No node or
module is withdrawn, and no whole-target-closure pruning is claimed.

The original proof dependency `lem-sfb-condensed-derived-restriction-calculus` is not used
by the new homological deduction: its actual required theorem belongs to
`def-sfb-condensed-derived-invariants`. The original public restriction-calculus import is
retained to preserve the existing public interface. Construction dependencies formerly
listed directly on the parent now sit on the corresponding split construction nodes.
The unit's statement and route are retained.

## Where the brief, the DAG or earlier work was wrong

The original plan attributed exactness reflection to
`lem-sfb-condensed-derived-restriction-calculus`, whose declarations concern restriction
and cup-product comparisons. The available exactness-reflection declaration is instead
`CategoryTheory.CondensedDerivedRestriction.forgetExact` in
`Sheaf.CategoryTheory.CondensedDerivedInvariants`. The node is updated to match this proof.

The latest blueprint paragraph (3) is a high-level proper/open direct-image argument;
the detailed polynomial argument is inherited agent-written material in the item's node,
with an exact literature reference still WANTED. The new nodes identify that provenance,
without presenting it as a quoted proof from the paragraph. No mathematical statement is
weakened, and no unit or chapter route is bypassed.

## New nodes

`def-sfb-homogeneous-polynomial-resolution-data` owns the seven existing definitions moved
verbatim to the shared module. It contains specifications, not an existence assertion,
and no chosen unproved witness.

`lem-sfb-homogeneous-polynomial-model-existence` carries original construction steps 1-3:
finite-support coefficientwise polynomial sheaves, internal monomial coproducts, diagonal
translation, alternating deletion and the constant augmentation.

`lem-sfb-homogeneous-polynomial-contraction-existence` carries original steps 4-5:
coproduct extension of zero evaluation/insertion, then degree-zero and positive-degree
finite cancellation identities. It requires an already given Model and concludes no
quasi-isomorphism.

All nodes inherit the item's chapter and unit. The inherited blueprint ancestor is null,
confirmed by `tools/blueprint_refs.py ancestor`; no artificial ancestor is introduced.

## Second reading by F2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
