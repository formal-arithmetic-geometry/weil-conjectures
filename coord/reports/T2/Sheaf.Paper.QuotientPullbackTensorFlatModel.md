## What changed

Restored the assigned module from its quarantine archive, preserving the complete
theorem signature and its existing public import. Replaced its proof hole by
normalization of the two paths, the proved ordinary signed-total square, and
cancellation of the actual invertible target computation.

Added `Sheaf.Paper.QuotientTensorFlatModelMaps`, containing explicit ordinary and
derived computation maps, the proof of `ordinary_square`, and proofs of
`targetCompute_isIso` and `targetLocalization_isIso`. The latter uses the given
`TensorNormalized` equation to prove invertibility; it assumes no exactness of
extension by the quotient. The ordinary square reuses the proved private
`CondensedRing.scalarPull_monoidal` calculation, whose signature precedes the
exact scalar-extension assumptions in its source module, and the existing
`mapHomologicalComplexδNatTrans_naturality` and composition equations. A private
abstract-functor helper performs the composition calculation before specializing
to internal modules. `totalPull` selects the canonical geometric oplax
structure explicitly so that specialization does not unfold the composite
monoidal construction.

Added two computation statements in separate modules. The left statement assumes
only the scalar tensor normalization at X; the right statement assumes only the
one at Y. Each computes a single derived path as an explicitly constructed
ordinary complex map, and neither asserts equality of the two paths. The item
combines these strictly smaller steps by the independently proved ordinary
square and invertibility argument. Updated its DAG proof to this argument.

No existing definition, instance, attribute, public import or declaration
signature was changed. No consumer requires adaptation. All four sandbox modules compile together in
import order through `lcompile.py --all`; the item also passed a single-file
compile against those support modules without errors or warnings.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.ProEtale.IntegralQuotient.quotient_pullback_tensor_flat_model`
(node `lem-sfb-quotient-pullback-tensor-flat-model`). The item has zero remaining
holes. This is a decomposition, not a net proof closure: one original hole is
replaced by the following two strictly smaller holes.

- `AlgebraicGeometry.ProEtale.QuotientTensorFlatModel.left_flat_computation`,
  node `lem-sfb-quotient-tensor-left-flat-computation`.
- `AlgebraicGeometry.ProEtale.QuotientTensorFlatModel.right_flat_computation`,
  node `lem-sfb-quotient-tensor-right-flat-computation`.

Each new hole has a source and complete proof in words in its docstring and
node. No definition or private declaration contains a hole. The explicit model
maps, `ordinary_square`, `targetCompute_isIso`, and `targetLocalization_isIso`
are proved, as are the private scalar and geometric counit invertibility helpers.

The mathematical edge-case review covered identity scalar and geometric maps,
zero complexes and zero target rings, empty schemes, the nonflat residue
quotient n = 0, and complexes unbounded in both directions. Their formulas use
the inverse of a tensor localization only under its explicit IsIso hypothesis;
the main proof supplies that hypothesis from the given normalization. None of
these edge cases requires an extra hypothesis or a choice of an object.

## No longer needed

No module is withdrawn, and no existing public import is removed. The original
public normalization import remains necessary for the statement's definitions.

The top proof no longer needs the section realization conclusion of
`quotient_section_tensor_normalization`, its scalar section data, or a fresh
section-generator calculation from
`def-weil-pbc-ringed-tensor-section-calculus`. The ordinary calculation is already
proved internally by monoidal conjugation and its signed cochain prolongation.
The actual coefficient-square identity is already contained in `pullIso`;
specializing the generic construction at `reduction l E n` needs no separate
coefficient-square proof in this module.

The route no longer needs `lem-pur-kflat-total-tensor-model`,
`lem-weil-pbc-ringed-pullback-preserves-kflat`,
`lem-weil-pbc-ringed-topoi-derived-tensor-pullback`, or
`def-weil-pbc-ringed-tensor-section-calculus` as proof dependencies. It uses the
native internal pullback comparison/counit identification of
`new-proetale-derived-module-pullback-monoidal` and the existing private internal
K-flat pullback calculation instead. The right computation only uses the given
normalizations, naturality and the tensor/counit equation; the left also uses
preservation of K-flatness and flat terms for its application of hbX. No separate
flat-term tensor-total theorem is needed by either computation. These older
modules are not claimed as globally pruned. No blueprint unit step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The current source is quarantined, not withdrawn. It was restored from the path
recorded in `coord/rework.tsv`; its Lean attachment and statement dependencies
are preserved. No quarantine archive or source-library declaration is deleted.

The existing exact-functor derived composition square cannot be applied to the
nonflat quotient extension. Only its independently proved ordinary monoidality
calculation is reused. The localization computations remain separate obligations.

The originally proposed section-category detour is unnecessary for the ordinary
square and target cancellation. The source construction already supplies the
ordinary internal monoidality and K-flat counit invertibility needed for those
parts. There is no statement dispute or target change.

## New nodes

`lem-sfb-quotient-tensor-flat-model-maps` records the actual model maps, proved
ordinary signed square and invertible computation maps in
`Sheaf.Paper.QuotientTensorFlatModelMaps`.

`lem-sfb-quotient-tensor-left-flat-computation` records computation of the left
path, using only the scalar tensor normalization at X and PullNormalized.

`lem-sfb-quotient-tensor-right-flat-computation` records computation of the right
path, using only the scalar tensor normalization at Y and PullNormalized.

All three inherit the item's chapter and unit and refer to paragraph (3) of the
integral proper-base-change blueprint proof. No existing interface change needs
a change record.

## Second reading by T2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
