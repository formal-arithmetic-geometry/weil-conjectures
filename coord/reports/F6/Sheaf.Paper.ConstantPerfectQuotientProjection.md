## What changed

Filled `AlgebraicGeometry.Scheme.OrderedExchange.quotientProjection_isIso` without
changing its statement or any existing definition. The existing bounded constant
resolution supplies its actual augmentation and finite-free retractions. The proof
uses `SignedProjectionResolution.normalization` for the signed-total inverse, then
proves a general private adjunction transport identity and cancels natural
isomorphisms to recover the specified original quotient mate.

Added `Sheaf.Paper.ConstantQuotientTensorComparison`, the tensor interpretation of
evaluated reduction together with its pullback square. It isolates the first step
of the existing plan, and assumes only a flat K-flat augmented quotient resolution;
it does not assume finite support, projectivity, a coefficient object K, or any
projection map or inverse. Its witnesses are eliminated inside the theorem proof;
no definition chooses arbitrary data from its unproved existence statement.

## Proved and sorry left

Original hole closed by a decomposition:
`AlgebraicGeometry.Scheme.OrderedExchange.quotientProjection_isIso`
(node `lem-sp-constant-perfect-quotient-projection`). Its assembly proof is complete.

One hole added and remaining:
`AlgebraicGeometry.Scheme.OrderedExchange.constantQuotientTensorComparison`
(node `lem-sp-constant-quotient-tensor-comparison`).

Thus 1 original hole becomes 1 strictly smaller comparison obligation: net holes
closed 0. This is a decomposition, not a sorry-free proof. The existing private
resolution helpers remain proved. No other holes are added or modified.

The remaining comparison includes the zero quotient and empty-site cases. Its
construction tensors q only against K-flat first factors, so it does not require
the quotient itself to be flat. The final inverse argument imposes no bound on K.

## No longer needed

None: no module is withdrawn and no existing import is removed. The K-flat
resolution and tensor-descent nodes formerly listed directly by the parent now
belong to the new comparison lemma's proof dependencies. The generic pre-derived
adjunction node is no longer used directly in the parent: the existing signed
projection normalization supplies the derived representative calculation. These
are dependency reorganizations, not claims that the underlying modules are
unused by the library.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement was changed. The parent plan correctly identified the
constant realization and signed-total projection argument, but did not provide a
Lean declaration identifying evaluated universal reduction with tensor, compatibly
with its specified pullback square. This missing comparison is the only new hole.
The signed-total inverse and its derived normalization already exist as proved
library declarations, so that part of the plan need not be split or proved again.
The unit route is preserved.

## New nodes

`lem-sp-constant-quotient-tensor-comparison` in
`dag/nodes/sec-smooth-purity/lem-sp-constant-quotient-tensor-comparison.json`:
first step of the original plan, stated in the derived category, with its full
pullback square, source, proof in words, and Mathlib searches. It omits the
finite-projective and K-injective projection-formula argument handled by the
parent. No change record is needed: existing public signatures and definitions
are unchanged, and the only new public statement is in its own new module.

## Second reading by F6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
