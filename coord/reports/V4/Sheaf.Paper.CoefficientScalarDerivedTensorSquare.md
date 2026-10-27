## What changed

Proved `AlgebraicGeometry.ProEtale.CondensedRing.coefficientScalarDerivedTensorSquare`
from `Functor.map_leftDerivedTensorComparison_comp_eq_of_iso`, with its existing signature
and docstring unchanged. The proof installs the specified ordinary monoidal structures,
identifies the scalar and geometric comparisons, expands the tensor of the two path maps,
and cancels the inverse path comparison using the proved private categorical helper
`tensor_square_from_inv`.

The private proposition `TensorSquare` and its proved constructor lemma
`canonical_tensor_square` retain the generic composition equation while matching the
monoidal data, before taking components. Explicit types for the four comparison aliases
prevent repeated reduction of concrete tensor constructions. This is a normalization of
the proof context; no existing definition, statement, public import, instance or exported
attribute changes. The existing section parameters are retained. Local transparency and
diagnostic settings are recorded in
`coord/changes/V4-coefficient-scalar-derived-tensor-proof-context.md`.

The private proof import
`Sheaf.UpstreamExtra.WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal`
provides the existing geometric-comparison identification after the source sync.
The node copy records these elementary normalizations and the same two-step proof route.
No other module requires adaptation.

Validation: the clean item and an unchanged copy of its direct consumer,
`Sheaf.Paper.CoefficientScalarTensorRealization`, both compiled successfully through
`lcompile.py` and were accepted by the single-file time gate. The temporary consumer
copy and all diagnostic files were removed; only the assigned module is delivered.

## Proved and sorry left

Closed the sole hole:
`AlgebraicGeometry.ProEtale.CondensedRing.coefficientScalarDerivedTensorSquare`
(node `lem-sfb-coefficient-scalar-derived-tensor-square`).

Both private lemmas `canonical_tensor_square` and `tensor_square_from_inv` are proved.
A witness of the private proposition `TensorSquare` is constructed from the existing generic theorem.
One hole closed, zero holes added, zero split off, zero holes remain in the delivered module.
Existing dependencies are used as provided; their transitive proof obligations remain
assigned to their own modules.

## No longer needed

None. No import, node or module is removed, and no new public obligation is introduced.
All declared proof dependencies remain relevant:

- `def-sfb-internal-scalar-tensor-comparison`: scalar comparison and its prerequisites.
- `def-pd-proetale-section-module-functors`: internal pullback prerequisites.
- `def-sfb-module-object-projection-map`: the specified geometric tensor comparison.

## Where the brief, the DAG or earlier work was wrong

No mathematical error found. The planned geometric-comparison identification lives in
`Sheaf.UpstreamExtra` after the source sync, so the proof needs that explicit private import.
Direct conversion of the concrete generic square exceeded the compile-time limit.
The private proposition and typed comparison aliases preserve the stated constructions
while avoiding that conversion cost; they introduce no additional assumption or proof hole.

## Second reading by V4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
