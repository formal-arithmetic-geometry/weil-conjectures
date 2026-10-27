## What changed

Filled `AlgebraicGeometry.ProEtale.CondensedRing.integral_constructible_reduction_limit`
in `Sheaf.Paper.IntegralConstructibleReductionLimit`, keeping its signature unchanged.
The proof uses the existing finite-model completeness theorem `complete_sheaf`
from `QcqsIntegralFiniteModelCompleteness` (via a proof-only `import all`), and
`AdicCompletion.roos_isDerivedLimit`. The existing principal tensor/scalar-extension
comparison preserves the actual quotient transitions. Its componentwise product
isomorphism conjugates the Roos endomorphisms, and a triangle isomorphism transfers
the distinguished triangle to the displayed tensor reductions and original sheaf.
Exact countable products and `derivedCategory_hasCountableProducts` supply the
product witnesses. All added imports are proof-only; existing public imports stay.
The initial successful remote compile took 23.8 seconds; the final revision also
retains the characteristic inequality as a local proof, preserving its binder.
Updated the assigned node's proof, proof dependencies and proof origin accordingly.
No existing module other than the assigned module is changed.

## Proved and sorry left

Closed the single original hole in
`AlgebraicGeometry.ProEtale.CondensedRing.integral_constructible_reduction_limit`
(node `lem-sf-integral-constructible-reduction-limit`). There are zero remaining
holes in the item and zero holes added or split off by this delivery.
The completeness and coefficient comparison inputs are existing proved lemmas;
this delivery adds no statement or definition.

## No longer needed

No existing public imports are removed, and no library module is withdrawn.
The following original direct proof dependencies are not needed by this proof:

- `sk-lem-int-integral-heart` / `Sheaf.Paper.IntegralConstructibleHeart`:
  the qcqs finite-model proof gives completeness directly for a constructible sheaf.
- `sk-lem-integral-models` / `Sheaf.Paper.IntegralModels`:
  no embedding into a fixed algebraic closure or integral-model equivalence is needed.
- `lem-weil-pbc-completed-constant-sheaf-reduction` /
  `Sheaf.Paper.CompletedConstantSheafReduction`: the existing principal
  tensor/scalar-extension comparison directly identifies the actual tensor levels.
- `det-pe-products-derived` / `Sheaf.AlgebraicGeometry.ProEtaleProductsDerived`:
  internal-module exact countable products and the general derived-product theorem
  supply the required product without changing coefficient encodings.

These nodes are pruned only from this item's direct proof plan; no global withdrawal
or claim that other consumers no longer need them is made. The unit's reconstruction
step by derived completeness is preserved. No unused proof imports are retained.

## Where the brief, the DAG or earlier work was wrong

The original plan's coefficient-field embedding and integral-model criterion are
unnecessary here: the existing qcqs finite-model completeness argument applies to
the exact coefficients and sheaf in this statement. The comparison required in
step 2 was already available as `principal_tensor_scalar_extension`, including its
transition equation. The proof uses these existing declarations and introduces
no further split. The original theorem and its mathematical meaning are unchanged.

The qcqs completeness and principal tensor comparison nodes are used as general
tools; they preserve the unit's derived-completeness route and do not replace it.

## Second reading by A9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
