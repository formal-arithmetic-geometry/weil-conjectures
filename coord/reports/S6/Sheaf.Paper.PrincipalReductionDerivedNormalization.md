## What changed

Reduced `AlgebraicGeometry.ProEtale.PrincipalNormalization.derived_principal_normalization`
to two natural comparisons through the existing derived right tensor functor. The
original declaration and its hypotheses, universes and conclusion are unchanged.
The composite comparison is explicit. Its shift is transported by
`Functor.CommShift.ofIso`; additivity and triangulatedness follow by transport.
The transition and unit equations follow by composition, and the signed equation
uses the tensor comparison, shift compatibility of the transported isomorphism,
and its naturality at the localization shift map.

Added `Sheaf.Paper.PrincipalConeTensorNormalization` and
`Sheaf.Paper.PrincipalTensorScalarExtension`, imported privately by the item.
The first concerns the exact principal resolution and signed tensor-cone
interchange; the second concerns the balanced coefficient extension and its
normalized adjunction maps. Neither statement is the item under another name:
the first mentions no derived extension/restriction, and the second mentions
no scalar cone, uniformizer endomorphism, or cone-shift normalization.

## Proved and sorry left

Closed the original single hole in
`AlgebraicGeometry.ProEtale.PrincipalNormalization.derived_principal_normalization`
by a complete Lean composition of the two comparisons. This is a decomposition,
not a claim of a net reduction in holes: one hole closed, two added (net -1).

Added two holes, each the complete proof of one public theorem in its own module:

- `AlgebraicGeometry.ProEtale.PrincipalNormalization.principal_cone_tensor_normalization`
  (`lem-pe-principal-cone-tensor-normalization`).
- `AlgebraicGeometry.ProEtale.PrincipalNormalization.principal_tensor_scalar_extension`
  (`lem-pe-principal-tensor-scalar-extension`).

There are no holes in definitions and none left in the item's theorem body.

## No longer needed

No existing public import is removed and no existing module is withdrawn.
The assembly no longer directly needs these former planned proof dependencies:
`det-pe-derived-nakayama-resolution`,
`lem-weil-pbc-independent-bounded-flat-kflat`, `lem-pc-kflat-resolution`,
`lem-weil-pbc-site-derived-tensor-descent`, `def-pc-tensor-complex-sheaves`,
`sk-def-pe-derived-completion`, and `def-weil-abstract-derived-category`.
Its statement dependencies stay unchanged. The mathematics of the principal
resolution and scalar-extension comparison remains in the two new nodes; this
list is not a claim that their theory or source declarations can be deleted.
`def-weil-triangulated-category` is retained for coherent shifts and exactness.
No unit statement or proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

No false statement was found. Existing `TensorMappingCone` has the natural
`reductionIso`, its unit equation, and its change-of-scalar equation, but does
not state the required signed shift equation. Existing
`InternalKFlatScalarTowerRealization` proves the normalized scalar extension
comparison on a K-flat representative, rather than the natural comparison
between the two actual derived functors. These are the precise remaining
normalization tasks. The supplied plan is retained through these substeps.
The zero complex, level zero (exponent one), arbitrary integer shifts and the
empty scheme introduce no additional hypotheses.

## New nodes

`lem-pe-principal-cone-tensor-normalization`, module
`Sheaf.Paper.PrincipalConeTensorNormalization`, isolates the principal free
resolution comparison with derived tensor, its quotient and inclusion maps,
and its standard signed shift. It uses the existing scalar-cone total-tensor
model, with the exact coefficient sequence from the resolution node.

`lem-pe-principal-tensor-scalar-extension`, module
`Sheaf.Paper.PrincipalTensorScalarExtension`, isolates the natural balanced
coefficient-extension comparison and its two actual adjunction normalizations.
The native K-flat scalar-tower realization supplies the representative formulas;
localization and derived tensor supply their natural extension.

No existing statement or definition changes, so no change record is required.

## Second reading by S6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
