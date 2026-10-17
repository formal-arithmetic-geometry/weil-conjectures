## What changed

Proved `integralResidue_tensorPullCounit_model` by expanding the tensor-pull
isomorphism and applying a strict intermediate factorization of the middle
coefficient-adjusted tensor model composite. The final step is a real
precomposition with the X tensor-presentation map and cancellation by
`Iso.hom_inv_id_assoc`.

Added the proof-only module
`Sheaf.Paper.IntegralResidueTensorPullCounitCore`, which states the middle
factorization used by the target proof. The target module now imports this
module and no longer directly imports `IntegralResidueTensorModel` or
`IntegralResidueTensorPresentation`; those declarations remain available
through the retained public imports and the core module.

## Proved and sorry left

Closed the original hole
`AlgebraicGeometry.ProEtale.CondensedRing.integralResidue_tensorPullCounit_model`.
Added one strictly intermediate open theorem,
`AlgebraicGeometry.ProEtale.CondensedRing.integralResidue_tensorPullCounit_core`,
with node `new-integral-residue-tensor-pull-counit-core`.

## No longer needed

Removed the target module's direct proof imports of
`Sheaf.Paper.IntegralResidueTensorModel` and
`Sheaf.Paper.IntegralResidueTensorPresentation`; the proof uses the new core
module, while the needed declarations remain reachable through its imports.
No DAG node or module is otherwise pruned: the core factorization uses the
existing tensor-presentation, tensor-model, scalar-counit, pull-presentation,
and integral-reduction declarations.

## Where the brief, the DAG or earlier work was wrong

The brief's direct calculation is valid but too large to expose within the
single-file elaboration budget. The middle factorization is therefore recorded
as a named strict intermediate theorem; the target proof combines it with the
presentation isomorphism and proves that combination explicitly. No target
statement or existing signature was changed.

## New nodes

`new-integral-residue-tensor-pull-counit-core` records the coefficient-adjusted
middle-composite factorization. Its proof remains open as the next item; the
source, proof steps, dependencies, and complete proof outline are in its node
and docstring.

## Second reading by B4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
