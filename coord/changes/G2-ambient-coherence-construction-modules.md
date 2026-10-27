# AmbientPullbackTensor declaration locations and public imports

## Reason

The remaining ambient coherence proof uses three independent components. They
must import the concrete ambient constructions, while the item imports their
proofs. Move those constructions, with the same names, signatures and bodies,
into AmbientPullbackSiteData and AmbientPullbackTensorData. The item publicly
reexports the latter, which publicly reexports the former. This breaks the
potential proof-import cycle without a second definition of any notion.

The first extracted monolithic module compiled over the 60-second limit. The
profiler showed costs in elaborating the selected functor and tensor comparison
types. The coefficient equation is proved with an abstract adjunction helper;
its concrete specialization is isolated in AmbientCoefficientComposition. The
site and tensor constructions are separate modules. No global irreducibility or
instance/attribute change is made. The two construction modules retain their
existing local elaboration controls. Every original public import remains
publicly reachable, and every original public declaration is defined exactly
once. No adopted source-library file is changed.

Reviewer correction (stage-3 review, 2026-10-27): the item's statement now names
declarations recorded by lem-sf-ambient-pullback-site-constructions (Site, comp,
pushComp, generator, scalar, ...) and lem-sf-ambient-tensor-data-exists-unique
(Tensor, TensorModels, tensorData, CompositionLaws, ...). Both nodes are added to
stmt_deps of lem-sf-ambient-pullback-tensor-coherence; the site-constructions node
is also added to its proof_deps (compositor_generator uses pushComp_existsUnique).
The statement text and Lean signature are unchanged.

No mathematical definition or target meaning changes. This is a relocation of
existing declarations and proof decomposition, rather than a statement repair.

## Old

The item's public imports were:

```lean
public import Sheaf.Paper.SemilinearDerivedSections
public import Sheaf.Paper.BundledTensorComparison
public import Sheaf.Paper.OrdinaryTensorPullbackData
public import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
public import Sheaf.AlgebraicGeometry.ProEtaleCoefficientPullbackUniverses
public import Sheaf.CategoryTheory.LocalizedModuleExactForSystems
public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryCocycle
```

The item itself defined Site through CompositionLaws, including the proved
existence and uniqueness results. These declarations are listed verbatim in the
new construction nodes' lean.declarations fields.

## New

```lean
public import Sheaf.Paper.AmbientPullbackTensorData
```

AmbientPullbackTensorData publicly imports AmbientPullbackSiteData. SiteData
retains all the original public imports above. Site through scalar and their
original proofs are defined in SiteData. Tensor through CompositionLaws and the
original tensor bundle construction proof are defined in TensorData. None of
these declaration signatures or definition bodies is changed; only module and
blueprint attachments move. The extra coefficient-composition result and the
three split-off statements are proof-only imports of the item.

## Users

The original direct-importer search found five consumers, all checked against
the delivered modules. Three were unchanged; IntegralComparisonSequenceSystems has
the separately recorded private-proof extraction, and
QuotientExpressionStrictKFlatTowers has the separately recorded coefficient-data
split, for their compilation limits. The current repair checks two additional
consumers: StrictScalarPullbackComparison unchanged, and
StrictPullbackEvaluationConstructor with the forced proof import adaptation in
G2-strict-pullback-evaluation-imports.md. Unchanged check copies are not delivered.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.AmbientPullbackTensorCoherence | G2 | Same public API by reexport; final theorem decomposed. |
| Sheaf.SixFunctors.SystemPullbackCompositorIdentification | unclaimed | Public reexport keeps all constructions visible. |
| Sheaf.Paper.FiniteTateSourceStructuralCoherence | unclaimed | Same public statements and definitions. |
| Sheaf.Paper.IntegralComparisonSequenceSystems | unclaimed | Same actual pullback and normalized tensor existence; scalar/K-flat and adjunction proofs extracted for timing. |
| Sheaf.Paper.IntegralExpressionSystemComparison | unclaimed | Same normalized tensor existence and fields. |
| Sheaf.Paper.QuotientExpressionStrictKFlatTowers | unclaimed | Same public declarations by reexport; coefficient constructions split for timing. |

| Sheaf.Paper.StrictScalarPullbackComparison | unclaimed | Same public constructions; compile checked unchanged. |
| Sheaf.Paper.StrictPullbackEvaluationConstructor | unclaimed | Explicitly import relocated private sequencePushEvaluation and the evaluation theorem. |

## Status

landed 20261027T205959-L-1641374 2026-10-27 (merge of deliver/G2/Sheaf.Paper.AmbientPullbackTensorCoherence)
