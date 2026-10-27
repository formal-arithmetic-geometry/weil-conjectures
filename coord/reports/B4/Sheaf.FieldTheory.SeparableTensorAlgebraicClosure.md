## What changed

Proved `Algebra.separable_tensor_algebraicallyClosed_equiv_pi` in
`Sheaf.FieldTheory.SeparableTensorAlgebraicClosure`, keeping its signature unchanged.
A proved private helper converts the separably generated definition of separability
into `Algebra.IsSeparable` for a finite extension. Its argument follows the existing
private helper in `Sheaf.AlgebraicGeometry.FieldCurveCompletionInsep`, generalized
to independent universes without importing that geometric module.

The primitive-element power basis presents K as AdjoinRoot of its minimal polynomial.
Mathlib's AdjoinRoot base-change equivalence, followed by its coefficient-change
isomorphism along the tensor unit, gives the polynomial quotient over Omega.
The existing declared CRT theorem gives its product decomposition. PowerBasis.liftEquiv
identifies the roots with embeddings; AlgHom.card supplies the embedding count.
Validation: the item compiled cleanly through lcompile.py (6.1 seconds).

Added private proof imports of PrimitiveElement, AlgebraicIndependent.Transcendental,
and Algebra.Algebra.Pi. Updated the item's DAG proof to record these APIs.

## Proved and sorry left

Closed 1 of 1 original holes:
`Algebra.separable_tensor_algebraicallyClosed_equiv_pi`
(node `lem-pc-separable-tensor-algebraic-closure`).
No holes remain in the item; no holes or new theorem statements were added elsewhere.
The proof uses the already stated
`Polynomial.exists_eval_quotient_algEquiv_pi_of_separable`
(node `lem-pc-separable-polynomial-alg-closed-quotient-product`), whose existing
sorry remains unchanged in `Sheaf.FieldTheory.SeparableQuotientProduct`.

## No longer needed

No existing imports were removed. The declared CRT dependency remains needed.
The separate planned nodes `lem-weil-pbc-polynomial-scalar-extension` and
`lem-weil-pbc-tensor-quotient-base-change` are unnecessary for this proof:
`AdjoinRoot.tensorAlgEquiv` already packages polynomial quotient base change.
The planned use of `lem-pc-finrank-field-base-change` is also unnecessary:
`AlgHom.card` directly counts embeddings of the finite separable extension.
Their modules are not imported; the item's proof_deps and proof-step uses omit them.
These nodes may still be needed elsewhere in the project; no withdrawal is proposed.
All other original dependencies remain used, and the unit route is preserved.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement needed correction. The plan's quotient and scalar-extension
steps have a shorter packaged Mathlib implementation. A proof-local algebra instance selects the standard
left-factor algebra when constructing the intermediate tensor product Omega tensor_k k;
the existing attribute command and importer-visible interface are unchanged.
The degree-one case gives one factor; for a nontrivial finite separable extension,
the primitive-element minimal polynomial is monic and nonzero. The construction and
embedding count work in arbitrary characteristic and independent universes.

## Second reading by B4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
