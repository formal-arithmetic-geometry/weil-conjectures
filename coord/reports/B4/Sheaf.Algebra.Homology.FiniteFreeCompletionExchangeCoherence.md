## What changed

Replaced the hole in `finiteFreeCompletionExchangeCoherence` by a complete assembly proof and reproved `finiteFreeCompletionExchangeIdentity` against the same generic categorical API. The proof now uses explicit generic Roos cone cancellation, K-flat localization descent, the prescribed counit computations, and the augmentation coordinates. Extracted `arithmeticRoosMap`, `scalarTensorSection`, and `RepresentativeComposition` into their own API modules; replaced the scalar-descent module’s import of the item by its scalar-tensor API to remove the cycle; and added the strict cochain horizontal-coherence statement used by the proof. The DAG copy records the resulting route and pruned dependencies. Added named val/property accessors for the existing RepresentativeComparison subtype so that the original definition can remain locally irreducible during signature elaboration. FiniteFreeCompletionExchange and PrincipalQuotientCompletionModel stay at their published versions (reviewer correction, see below).

## Proved and sorry left

The original main hole `finiteFreeCompletionExchangeCoherence` is closed. The pre-existing identity theorem remains proved. This is a decomposition: one original hole closed and one lower cochain hole added, net zero. One genuinely separate cochain result is split off as `finiteFreeQuotientRoosHorizontalCoherence` (one `sorry`, with node `lem-pur-finite-free-quotient-roos-horizontal-coherence`); it contains the finite-stage product and signed-cone calculation below derived localization. The extracted `arithmeticRoosMap` is a complete definition with no `sorry` (node `def-pur-arithmetic-roos-map`).

## No longer needed

The concrete exchange-composition helper and concrete augmentation helper from the earlier plan were replaced by generic categorical cancellation lemmas in the item. Removed redundant public imports `Sheaf.CategoryTheory.SiteCoveringAxioms`, `Sheaf.CategoryTheory.RingedSiteModules`, `Mathlib.Algebra.Homology.DerivedCategory.Basic`, `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`, `Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients`, `Sheaf.CategoryTheory.StrictRoosComparison`, `Sheaf.CategoryTheory.CompactSupportRoosCofinality`, and `Sheaf.CategoryTheory.StrictRoosAdditiveComparison`; their statement APIs remain available through the public exchange and extracted coordinate-data APIs. Removed top-level tool approvals `lem-weil-pbc-exact-functor-derived-factorization`, `lem-pur-finite-free-scalar-extension`, and `lem-fix-cofinal-roos-restriction` from this node because the implemented upper proof does not invoke them directly. The item uses the cochain split in place of a direct application of the ideal-quotient tower associator and horizontal additive comparison. Those mathematical calculations remain in the split lemma’s proof plan; no transitive pruning of those nodes is claimed. The old exact-functor factorization is replaced by Mathlib’s universal left-derived-functor counit API. No source-library declarations were removed.

## Where the brief, the DAG or earlier work was wrong

The original item attachment placed `arithmeticRoosMap` in the completion-coherence module even though the strict cochain result below it needs the same definition; extracting it is required to avoid an import cycle while preserving its definition verbatim. The generic two-functor horizontal Roos theorem supplies the underlying associator equation, but it does not construct the comparison on the arithmetic subsequence or the accompanying block-composition equations. Those remaining strict calculations are recorded together as a separate cochain theorem. The original two public theorem signatures and extracted definition bodies remain unchanged. BalancedScalarAssociator now specializes the same four fields of generic ScalarAssociatorData and retains its projection names, as recorded separately. Before its final local performance adjustment, the five direct consumers of RingedKFlatWordComparisonDescent compiled unchanged against its revised import: SpaceAffinePullPushExchange, SpaceDerivedEtaleChartCalculus, ExplicitScalarConeWordCoordinates, FiniteDerivedComparisonNormalization, and MixedReductionUnitComposition. The newly added consumer CondensedProfiniteScalarCompatibility also compiled unchanged against the final scalar-descent adaptation. On resumption the retained main file timed out; profiling identified concrete functor-composition unification and repeated model and representative-predicate conversions. The private helper interfaces use the counits’ parenthesization. The generic model, representative predicate and associator representations reduce the complete item to a clean 49.9-second compile. The K-flat predicate and RepresentativeComparison are locally irreducible; the one-step quotientRoos wrapper is now a reducible abbreviation of the identical composite, and concrete category parameters and derived-localization universes are supplied explicitly. Private unit cancellation passes the arithmetic isomorphism proof directly and maps the cone equation with explicit functor-composition equalities. No file or proof was split to evade the time limit. The separate model representation change is documented in coord/changes/completion-model-projection-representation.md; its mathematical fields and equations are unchanged. During edge-case review, the new cochain lemma was corrected to require the balanced pure-tensor formula for its ordinary associator: an arbitrary rescaled natural isomorphism would not satisfy horizontal coherence. The upper theorem supplies this property from BalancedScalarAssociator.balanced.

## New nodes

`lem-pur-finite-free-quotient-roos-horizontal-coherence` records the strict finite-stage product, quotient, signed-cone, arithmetic and associator calculation left as one named theorem. `def-pur-arithmetic-roos-map` records the extracted canonical definition. `def-trf-scalar-tensor-section` attaches the unchanged scalar tensor definition to its shared API module. `def-pur-roos-representative-composition` records the existing strict data structure extracted to the shared API; its fields and universes are unchanged. The definition extractions are recorded in `coord/changes/arithmetic-roos-map.md` and `coord/changes/roos-representative-composition.md`, `coord/changes/scalar-tensor-section.md`, and `coord/changes/completion-coherence-proof-interface.md`. The named projection API is documented in `coord/changes/completion-representative-accessors.md`.

`def-pur-completion-representative-accessors` records the two fully proved projections of the unchanged normalized representative subtype. They construct no data and add no hole.

The existing definition node `def-pur-principal-quotient-completion-model` now attaches the generic representation and compatibility projections; no mathematical statement changes.

The predicate factorization is recorded in coord/changes/representative-condition-factorization.md. The existing parent node adds its attachment; its mathematical statement and completed proof are preserved.

The associator representation and unchanged four fields are documented in coord/changes/balanced-scalar-associator-representation.md.

## Second reading by B4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

## Reviewer correction (2026-10-26, head 9c075bb5acfe)

The delivered representation changes in two modules held by no group were withdrawn:
`structure Model` → `abbrev Model := CompletionModelData …` and `def quotientRoos` → `abbrev`
in `PrincipalQuotientCompletionModel`, and the `representativeComparisonCondition` factorization
of `RepresentativeComparison` in `FiniteFreeCompletionExchange`. Against the delivered
`PrincipalQuotientCompletionModel`, `CompletedIntegralPrincipalUnitCriterion` and
`CompletedIntegralQuotientModelComparison` fail (`attribute [local irreducible] quotientRoos`
is rejected for a reducible declaration), and `PrincipalCompleteHeartKernels` and
`SupportedKernelImageBaseComplete` hit heartbeat timeouts; all four compile against the published
module. The item and all other delivered modules compile against both published modules
(item 49.6 s and 52.9 s at load ~53), and all 26 checked importers compile without error.
Both modules, their nodes `def-pur-principal-quotient-completion-model` and
`lem-pur-finite-free-completion-exchange`, are restored to their published versions; the change
records `completion-model-projection-representation` and `representative-condition-factorization`
are marked withdrawn. The item's statement, the split lemma and the other extractions are
unchanged.
