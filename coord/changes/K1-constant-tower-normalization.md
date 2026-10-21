# K1 constant tower normalization

## Reason

Fill the three assigned proof holes in
`Sheaf.Paper.ConstantTowerDirectImageNormalization`, using the coefficient
adjunction and resolving-class localization that already specify the comparisons.
Avoid repeated expansion of sheafification, scalar-adjunction Hom equivalences,
and the K-flat tensor predicate during elaboration.

## Old

The assigned module had three proof holes: `ordinaryReductionPull_existsUnique`,
`reductionPull_existsUnique`, and `constantTowerDirectImageNormalization`.
Its private `levelUnitMap` repeated the sheafified presheaf construction of the
normalized scalar-adjunction unit. Quotient transitions used three private
sheafification transport helpers. Tensor-generator extensionality expanded the
sheafification adjunction's Hom equivalence. The public `augmentation` definition
used an inlined `haveI` proof of its left-derived universal property.

## New

All three proof holes have complete proofs. The DAG proof and proof dependencies
now follow the actual adjunction/localization argument.

The private `levelUnitMap` is the existing tensor-normalized scalar-adjunction
unit. Its unchanged section formula is proved from that adjunction's normalization.
It is the same map, determined by its values on all sections. Quotient transitions
use the adjunction Hom equivalence; the private `scalarExtensionPresheafMap`,
`scalarExtensionMap`, and `scalarExtensionMap_tmul` are unnecessary and removed.

Tensor-generator extensionality uses the direct sheafification universal property.
Private, proved `scalar_obj`, `scalar_tensor`, and `scalar_quasiIso` equations expose
the chosen scalar-extension functor's construction and resolving property without
repeatedly unfolding the full existence witness.
Proved private generic lemmas express injectivity and transposition through an
adjunction's unit. Local reducibility attributes keep the constant-sheaf functor,
the K-flat predicate, the scalar-extension witness, and the derived-functor models
folded while their existing APIs are applied. These attributes do not change exported attributes or data.
Proof-only imports are updated as listed in the report.

The public `augmentation` definition changes its proof binding from `haveI` to
`have`; the rest of its body is verbatim. The bound class
`Functor.IsLeftDerivedFunctor` is a proposition. Proof irrelevance identifies the
two instance proofs, so the constructed universal lift is unchanged. Keeping the
proof as a local binding avoids repeatedly expanding the chosen universal model.

All additional helpers are private and proved. Every existing public declaration
header and public import is preserved, and every other public definition is
verbatim. No target, source-library declaration, or consumer signature changes.
No new DAG node or axiom is added.

## Users

Only the assigned K1 Lean module changes. The changed or removed private helpers
have no users outside it. No other group's module is adapted.

The sole direct importer is
`Sheaf.AlgebraicGeometry.VaryingRingProperOpenArrows` (unclaimed when checked).
Its original source compiles unchanged against the completed sandbox module
(6.3 seconds, final main module 54.4 seconds).
No consumer adaptation is needed; all public constructions and statements retain
their meaning. After the private elaboration cleanup, the complete proof with the
delivery axiom scan compiles in 45.3 seconds with no source warnings.

The indirect consumer `Sheaf.Paper.ProEtaleConstantReductionTower` (held by T1)
also mentions
`AlgebraicGeometry.ProEtale.StrictTower.ConstantNormalization.augmentation`.
Its original source compiles unchanged against the optimized definition in 49.0
seconds, together with the direct consumer. The binding change affects only a proof of a proposition; no
change of meaning or consumer adaptation is required.

## Status

landed 20261021T013817-L-2339046 2026-10-21 (merge of deliver/K1/Sheaf.Paper.ConstantTowerDirectImageNormalization)
