## What changed

Repair of the landing-tools return for head `9734b5470fd`: refreshed the change
record's `## Users` table against all 18 current downstream modules, including
`Sheaf.Paper.IntegralPullbackStrictRoosNormalization` (currently unclaimed). Its
`IsUnitNormalized` uses `limitComplexUnit`, whose body and morphism type are preserved;
no consumer adaptation is required. This repair refreshes the change record and reconciles the node with the current
separated proof plan; it makes no further Lean source changes.
The retained Lean proof work and its hole counts are unchanged. On this retry,
`tools/downstream.py --uses AlgebraicGeometry.Scheme.OrderedExchange.limitComplexUnit`
confirmed the consumer row and the same 18 downstream modules. All user ownership
entries were refreshed against the current claims. The item compiled on the project
server in 11.3 seconds. Unchanged consumer copies are used only for validation and
are excluded from delivery. The two consumer checks passed without diagnostics:
`IntegralPullbackStrictRoosNormalization` in 41.0 seconds and
`CompletedExchangeCoherence` in 8.3 seconds. The all-files check also recompiled the
item successfully (1.3 seconds).

Proved `ordinaryLambda_existsUnique`, `completedHom_normalization`, and
`normalized_naturality` in `Sheaf.Paper.OrderedExchangeCoefficientComparison`.
The ordinary limit proof uses preservation and the projection universal property.
The Hom proof combines the phi unit equation with the normalized scalar adjunction.
Naturality is the naturality of explicit composites of the existing transformations.
No new mathematical obligation is introduced.

Named the unchanged complex normalization formulas `RhoNormalization` and
`LambdaNormalization`, with proved projection lemmas `rho_normalization` and
`lambda_normalization`. This avoids repeatedly elaborating the large formulas
when constructing their unique comparisons. The unique-choice construction itself
is unchanged. `limitComplexUnit`, `rawComponent`, and `constantComponent` retain their original
bodies and have explicit return types.
The final module and unchanged direct consumer
`Sheaf.Paper.CompletedExchangeCoherence` compile together on the project server
in 21.2 and 7.2 seconds. The consumer was copied only for this check and is not
part of the delivery. An instrumented compile including the delivery's axiom
scan completes in 23.9 seconds, scans 42 declarations, finds exactly the seven
listed holes and no disallowed axiom.
Local instance priorities and opacity attributes keep fixed coefficient constructions
out of definitional comparison. Scalar-restriction and complex-tower wrappers normalize
locally to their original bodies, avoiding mismatched presentations. Existing target statements are untouched.

Change record: `coord/changes/K9-ordered-exchange-comparison-normalizations.md`.

## Proved and sorry left

Closed 3 of the original 10 holes:

- `AlgebraicGeometry.Scheme.OrderedExchange.ordinaryLambda_existsUnique`
- `AlgebraicGeometry.Scheme.OrderedExchange.completedHom_normalization`
- `AlgebraicGeometry.Scheme.OrderedExchange.normalized_naturality`

Added zero holes; split off zero theorems. The seven remaining holes, all unchanged
mathematical obligations of `lem-weil-pbc-ordered-exchange-coefficient-comparison`, are:

- `AlgebraicGeometry.Scheme.OrderedExchange.ordinaryRho_existsUnique`
- `AlgebraicGeometry.Scheme.OrderedExchange.rho_existsUnique`
- `AlgebraicGeometry.Scheme.OrderedExchange.lambda_existsUnique`
- `AlgebraicGeometry.Scheme.OrderedExchange.restriction_complete`
- `AlgebraicGeometry.Scheme.OrderedExchange.phi_existsUnique`
- `AlgebraicGeometry.Scheme.OrderedExchange.rho_unit`
- `AlgebraicGeometry.Scheme.OrderedExchange.coefficientComparison`

The two normalization predicates are fully defined; their projection lemmas and
all private helpers are proved. This is a partial proof delivery, not a proof of
the final coefficient comparison.

## No longer needed

The following direct imports were unused by the completed auxiliary proofs and
are removed:

- `public import Sheaf.Paper.PbcActualRingedExchange`
- `public import Sheaf.Paper.PbcActualScalarPullback`
- `public import Sheaf.Paper.PbcActualStrictPullback`
- `import Sheaf.Paper.ConstantCompletionEquivalence`
- `import Sheaf.CategoryTheory.DiagramSiteRealization`
- `import Mathlib.Algebra.Category.Grp.FilteredColimits`
- `import Mathlib.CategoryTheory.Abelian.FunctorCategory`
- `import Mathlib.CategoryTheory.Sites.Limits`
- `import Sheaf.Paper.KoszulReconstruction`
- `import Sheaf.Paper.ProjectionFormulaBaseChangeNaturality`
- `import Sheaf.AlgebraicGeometry.ProfiniteCoefficientInverseImage`
- `import Sheaf.Paper.CompletedBaseChangeMap`
- `import Sheaf.Paper.StrictTowerOperations`
- `import Sheaf.AlgebraicGeometry.ProEtaleIntrinsicFiniteOperations`
- `import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`
- `import Sheaf.CategoryTheory.PreDerivedAdjointFunctorsGeneral`
- `import Sheaf.Paper.CompletedPullbackAdjunction`
- `import Sheaf.Paper.CompletionMateComparison`
- `import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution`
- `import Sheaf.CategoryTheory.KInjectiveTotalDerived`
- `import Sheaf.AlgebraicGeometry.ProEtaleCanonicalPullbackComposition`
- `import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp`
- `import Sheaf.Paper.RingedExchangeTensorCoherence`
- `import Sheaf.Paper.WeilCompletedTensorReflector`
- `import Sheaf.Algebra.Homology.WeilSiteDerivedTensorDescent`
- `import Sheaf.CategoryTheory.SmallModuleDiagramsGrothendieck`
- `import Sheaf.Paper.StrictTowerExchangeMateNormalization`
- `import Sheaf.CategoryTheory.RingedTowerPushforwardLimitComparison`
- `import Sheaf.CategoryTheory.RingedToposMorphism`
- `import Mathlib.Algebra.Homology.DerivedCategory.Basic`
- `import Sheaf.Paper.PerfectProjectionFormula`
- `import Sheaf.Paper.CompletedDirectImageLimits`
- `import Sheaf.Paper.CompletedRlimFunctor`
- `import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`
- `import Sheaf.CategoryTheory.FlatRingedDiagramRestriction`
- `import Sheaf.Paper.IntegralFinitePullbackComposition`
- `import Sheaf.Paper.PbcQbarCompletedPullback`
- `import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`

No DAG node or module is withdrawn. The remaining seven obligations retain the
original planned dependencies; removal of a redundant direct import does not
claim that its mathematics or its other consumers can be pruned. The unit route
is unchanged.

## Where the brief, the DAG or earlier work was wrong

The existing statement of each long normalization formula was repeated by
elaboration of its chosen comparison. Server diagnostics locate deterministic
kernel timeouts in the generated `rho._proof_16` and `lambda._proof_5` auxiliaries.
Naming the formulas preserves their meaning and gives the choice construction a
compact predicate. The ordinary inverse-limit comparison needs no derived or
flatness theorem: restriction preserves all ordinary limits directly.
The completed Hom calculation uses the already stated normalized
`proEtaleRingSheafChangeAdjunction` rather than reproving its transpose equation.

The returned packet omitted the consumer that uses `limitComplexUnit`. The refreshed
users table records that use explicitly and includes the other current downstream
modules and their current holders.

The current node had meanwhile replaced the original fourteen-step sketch by five
assembly steps using separately stated coefficient lemmas. The repaired node preserves
that current plan, its dependencies, and all maintainer approvals; it appends the
three auxiliary proof arguments and their adjunction dependency. It does not restore
the stale fourteen-step node or remove the newly stated dependencies.

The slot-wait refresh also records `Sheaf.Paper.ZlFrameworkOpenExchange`, which
returned to the current downstream closure while delivery capacity was unavailable.

## Second reading by K9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
