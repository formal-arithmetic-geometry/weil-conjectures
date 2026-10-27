## What changed

Proved `AlgebraicGeometry.ProEtaleWeilSheaf.nativeGeometricForget_tensorComparison`
in `Sheaf.Paper.NativeGeometricTensorComparison`, preserving its complete signature
and all three public imports. The proof uses the specified
`nativeDerivedClosedComparison`, so its Frobenius-forgetting comparison applies to
the actual chosen `nativeDerivedTensor`.

The shorter route identifies its ordinary tensor with the canonical derived tensor
using `native_ordinary_closed_tensor_models`. New proved private helpers compose
the two transposition bijections for a common internal Hom. They construct inverse
maps from identities and prove simultaneous naturality using
`CoefficientClosedStructure.evaluation_naturality` and adjunction naturality.
This avoids choosing an unrelated isomorphism for each fixed tensor parameter.
The private inverse-currying proofs follow the existing
`DerivedNativeTensorProof` helpers in `DerivedWeilTensorOperations`; the assembly
into `TensorComparisonProof.closedTensorIso` proves simultaneous naturality here.

Scalar forgetting is equipped with the already proved monoidal structure from
`nativeScalarForgetting_monoidal`, then composed with coefficient-ring-isomorphism
restriction. The existing exact monoidal derived comparison
`Functor.mapDerivedCategoryTensorComparison` and its `IsIso` instance give the
required coefficient comparison, natural in both variables. Whiskering and
associators compose it with the native Frobenius-forgetting comparison. The
condensed tensor is the existing `CondensedRing.derivedTensor`, with input order
unchanged. No boundedness, constructibility or site-perfectness assumption enters.
The coefficient-restriction nodes are generic tools: the native unit supplies
no alternative construction of restriction along its specified ring isomorphism.

Added only private proof imports for ordinary closed models, monoidal scalar
forgetting, scalar-forgetting equivalence, monoidal coefficient restriction and
exact derived monoidal comparison. Updated this item's DAG proof, proof_deps and
proof_origin to describe that route. No shared definition, public signature,
public import, other existing module, or target changed.

Validation: `lcompile.py` compiled the final module cleanly in 13.2 seconds
(exit 0). The delivery tool runs the required server preflight. The generic private proof applies to arbitrary objects and morphisms, so the
zero object, empty scheme and unbounded complexes need no additional hypothesis.
The unit `sk-prop-sf-biduality-general` has empty `realized` statement and step lists;
its route is preserved.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.ProEtaleWeilSheaf.nativeGeometricForget_tensorComparison`
(node `lem-sf-native-geometric-tensor-comparison`).

The item has zero remaining holes. Added zero holes and zero split-off statements.
All private helpers are completely proved. Existing dependencies retain their
current proofs and hole status; this is a proof from existing declarations.

## No longer needed

No original import was removed: the three public imports support the unchanged
statement. No module is withdrawn or claimed globally unnecessary.

The item no longer directly needs
`lem-pc-sites-sheaf-tensor-bilinear-universal`
(`WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorBilinearUniversal`),
`lem-sf-locally-finite-coefficient-ring-realization`
(`Sheaf.Paper.LocallyFiniteCoefficientRingRealization`), or
`def-sfb-preserves-kflat-quasi-iso` as separate proof steps. Balanced tensor
comparisons, K-flat transport and coefficient realization are already encapsulated
in the existing monoidal scalar-forgetting theorem, normalized coefficient
isomorphism and exact derived monoidal comparison. These nodes may remain needed
by those dependencies or other consumers; no declaration or dependency module is
deleted. The top-level proof_deps now records the declarations actually used.

The fixed-parameter theorem `nativeCoefficient_tensorComparison` is not imported:
it does not assert naturality in that parameter. Its underlying monoidal
construction is reused through `nativeScalarForgetting_monoidal` and the generic
bifunctor comparison instead. There are no new proof obligations below the item.

## Where the brief, the DAG or earlier work was wrong

The earlier plan predates the available ordinary closed-model and monoidal
scalar-forgetting theorems. Reconstructing the balanced tensor and K-flat
localization here would duplicate their work. The new proof supplies the missing
common-internal-Hom bifunctor uniqueness argument and uses these existing results.

The rework row preserves a quarantined copy and mentions the historical
`SfP1ProjectionTraceFalseTail` import. The current item is present in the shared
Lean tree and has no such import; its original statement and dependencies have
been preserved, and no quarantined file was deleted or withdrawn.

## Second reading by H5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
