## What changed

Proved `AlgebraicGeometry.normal_stalks_perfectClosure_iff` in
`Sheaf.AlgebraicGeometry.NormalityPerfectClosureTest`, with its original signature
and docstring unchanged. The proof follows all six steps of the existing node:
a common extension field, perfect-field separating bases, separable scalar ascent,
field-extension descent, and affine-chart stalk comparisons. Private, fully proved
helpers implement preservation under ring equivalences and open immersions,
the spectrum-stalk criterion, and the scalar-extension argument.

Used Mathlib `Localization.localRingEquiv`, `Spec.stalkIso`, `pullbackSpecIso`,
`Scheme.Pullback.openCoverOfLeft`, and tensor-product commutation and
`cancelBaseChange` isomorphisms. Replaced the proof import
`Mathlib.RingTheory.TensorProduct.Basic` with
`Mathlib.RingTheory.TensorProduct.Maps` for these isomorphisms.
No public declaration, definition, target, or dependency interface was changed.

## Proved and sorry left

Closed 1 of 1 holes:
`AlgebraicGeometry.normal_stalks_perfectClosure_iff`
(node `lem-weil-pbc-normality-perfect-closure-test`).
Added 0 holes; no `sorry` remains in the delivered module. This is a proof from
existing declared dependencies, not a decomposition. It still uses the existing
`Algebra.isNormal_tensorProduct_of_separableExtension` and
`Algebra.normal_ring_of_normal_tensor_field` declarations, whose proofs are
separate stage-3 items. All six new private helper theorems are proved.

A single-file server compile succeeded. The final delivery preflight also compiles
and probes every declaration for axioms and direct holes.

## No longer needed

Removed the proof import `Mathlib.AlgebraicGeometry.FunctionField`: only the
spectrum-stalk localization clause is needed, and `Spec.stalkIso`, already available
from the retained scheme imports, supplies it. The function-field clause of
`lem-weil-pbc-spec-domain-stalks-function-field` is unused; its localization clause
remains used. No declared dependency node or Sheaf/WeilConjectures module is
pruned: the proof uses every declared mathematical dependency, so the existing
DAG proof route and dependency list remain accurate.

## Where the brief, the DAG or earlier work was wrong

No defect in the statement or declared dependencies was found. The proof does not
need the purely inseparable power hypothesis: normality over any perfect overfield
implies the asserted geometric normality by the same common-overfield argument.
The original `hpower` binder is retained exactly; a scoped linter option allows
this deliberately unused hypothesis without changing the signature.
No finite-type, integrality, connectedness, or nonemptiness assumption is introduced;
the affine-cover argument also applies to the empty scheme and disconnected schemes.

## Second reading by Y9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
