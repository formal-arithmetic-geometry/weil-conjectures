## What changed

Replaced `AlgebraicGeometry.ProEtale.diagonalTower_trace`'s proof hole by a complete Lean combination of trace assembly and whole-system integration comparisons. Its signature is verbatim unchanged. The three specified projective models are retained, including the pullback symmetry for the second projection.

`DiagonalTraceResultExistence` proves the categorical assembly: exact restriction carries the varying splitting to the strict splitting via its biproduct comparison; surjectivity on the indicated Hom set lifts the system trace; cancellation of the coefficient unit gives its construction equation; naturality gives every finite reduction equation.

`SingleTowerEvaluationFaithful` proves evaluation detects equality between single objects of strict towers, and proves transport of the resulting identity through the specified limit square. `DiagonalTraceSingleFaithful` proves faithful reflection on single completed sheaves. Neither claims that derived evaluation is faithful on arbitrary objects.

The original seven model/source definitions move verbatim to `DiagonalTraceSources` to make them available below the main theorem without an import cycle. The original module publicly re-exports them and their original statement imports. The unused-variable linter is disabled only around the main theorem, retaining its exact published binders while acknowledging that the reduced proof does not need three hypotheses. The normalized-source ownership attachment is updated. Change record: `coord/changes/diagonal-trace-source-interface.md`. No WeilConjectures module changes and no consumer adaptations.

## Proved and sorry left

Closed the original one hole in `AlgebraicGeometry.ProEtale.diagonalTower_trace` (node `det-prop-diagonal-tower-trace`) by decomposition into the two genuinely separate construction arguments below. This is a decomposition, not a net hole reduction: one hole closed, two holes added, net -1. The item module itself has zero `sorry`.

New proved declarations: `CategoryTheory.singleTowerEvaluationFaithful`, `CategoryTheory.singleTowerLimitIdentity`, `CategoryTheory.SingleTowerLimitWitness.eq_id`, `AlgebraicGeometry.ProEtale.DiagonalTrace.diagonalTrace_single_map_injective`, and `AlgebraicGeometry.ProEtale.DiagonalTrace.exists_diagonalTraceResult`. The private generic scalar-restriction helper is proved too.

Exactly two `sorry` remain in the packet:

- `AlgebraicGeometry.ProEtale.DiagonalTrace.exists_diagonalTracePresentation`, node `lem-sfb-diagonal-trace-presentation-existence`: construct the normalized geometric/coefficient presentation and finite splitting identities, and establish fullness on the one Hom set. It does not choose a completed trace or assert an integration identity.
- `AlgebraicGeometry.ProEtale.DiagonalTrace.diagonalTrace_integrationSystems`, node `lem-sfb-diagonal-trace-integration-systems`: for an already supplied trace result, construct the normalized supported source, the endomorphism of its actual restricted coefficient tower, and its square under the actual `t.LS.R` functor, with identity finite evaluations. It does not assemble a trace result or conclude the completed integration equation.

Validation: import-direction checks pass. The theorem signature and extracted definition block were compared byte for byte with the shared source and agree. Every new node is reachable from the item; existing dependency cycles lie wholly outside this packet. All six supporting modules compiled in import order. The final item also compiled after replacing a failed simplification with the explicit functor identity law; the unused-variable linter is disabled locally for this theorem because its unchanged signature retains three hypotheses not required by the reduction. The final item recompile passed without warnings.

Both construction statements have source-based proof prose and their own modules/nodes. No definition has a proof hole, and no data is chosen in a definition from an arbitrary existence theorem. Edge cases checked mathematically: the empty base, n=0 (the library's level is l^(n+1)), l=2, arbitrary/nonreduced Noetherian bases, and the swap of projections. The geometric constructions use only l invertible, so the stronger field/finite-type hypotheses of the item remain available but are unnecessary for these parts.

## No longer needed

The following original private proof imports are removed from the item module, which now imports only the three proved/split proof modules it applies:

- `Sheaf.AlgebraicGeometry.GeoCartierCycleClass`
- `Sheaf.AlgebraicGeometry.ProEtaleIntegralCoefficientLimit`
- `Sheaf.AlgebraicGeometry.ProEtaleMilnorEpimorphic`
- `Sheaf.CategoryTheory.DerivedCategory.StandardQuotientsPerfect`
- `Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition`
- `Sheaf.CategoryTheory.RingedTowerPushforwardLimitComparison`
- `Sheaf.NumberTheory.Padics.ExtensionIntegersDvr`
- `Sheaf.Paper.CoefficientSystemDerivedComparison`
- `Sheaf.Paper.CompletedDirectImageLimits`
- `Sheaf.Paper.ConstantCompletionEquivalence`
- `Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction`
- `Sheaf.Paper.DiagonalTowerSystem`
- `Sheaf.Paper.IntegralModels`
- `Sheaf.Paper.ProEtaleTateTwistsOfUniverses`
- `Sheaf.Paper.PurTwistSheafLocallyFree`
- `Sheaf.Paper.SmoothPurityCoefficientTowersAbelian`
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.ClosedImmersion`

These removals do not claim these geometric nodes are globally pruned: the new construction nodes retain the relevant source steps and dependencies, including finite Cartier normalization, whole-system construction, closed direct-image exactness, completeness and normalized derived comparisons. No source-library declaration or module is withdrawn. No unit step is bypassed. No existing tool-use approval is withdrawn. The original public presentation import is supplied through the new public source interface, and remains visible. Proof-only imports of the deferred construction lemmas are omitted until their proof needs them; their intended dependencies are recorded in the DAG.

The generic degree-zero lemmas use Mathlib's full/faithful single functor directly, so no new import of `DerivedSingleFullyFaithful` is needed for that categorical argument. No whole module is certified unreachable by this packet; pruned modules: none.

## Where the brief, the DAG or earlier work was wrong

The node refers to the Chern/splitting data of `det-sp-tower-classes` as supplied data. Its current Lean attachment `SmoothPurityTowerClasses` declares a `TowerClasses` structure, with no theorem constructing an inhabitant. The trace presentation and its normalized restriction/comparison data are also records, not supplied instances. Thus applying those declarations alone cannot construct a trace result. The new presentation-existence statement isolates that genuine construction step, without changing its mathematical route.

The integration proof requires a single endomorphism of a degree-zero strict tower before taking a limit. Equality of arbitrary derived arrows after evaluation would be invalid. The proved categorical lemmas and the explicit tower/limit specification in the remaining system construction retain that distinction. Exact scalar restriction is faithful on single sheaves; unrestricted derived faithfulness is not assumed.

## New nodes

`lem-sfb-single-tower-evaluation-faithful`: proved degree-zero detection by exact evaluation.

`lem-sfb-single-tower-limit-identity`: proved categorical transport through a specified limit square, with its witness structure and bundled proof.

`lem-sfb-diagonal-trace-single-faithful`: proved reflection through scalar restriction on single completed modules.

`lem-sfb-diagonal-trace-presentation-existence`: the paragraph (1) normalized construction, left as one public theorem hole.

`lem-sfb-diagonal-trace-result-existence`: proved trace assembly and finite reductions from that construction.

`lem-sfb-diagonal-trace-integration-systems`: the paragraph (2) system/source comparison construction, left as one public theorem hole.

`def-sfb-diagonal-trace-sources`: ownership of the five moved product-model/integration/source declarations. The existing `def-sfb-diagonal-normalized-source` owns the other two moved declarations. All seven are preserved verbatim; see `coord/changes/diagonal-trace-source-interface.md`.

## Second reading by E7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
