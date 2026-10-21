# AlgebraicGeometry.exists_affineModelCoherentObjectComparisons

## Reason

Apply the assigned cut to the adopted source implementation re-exported by the
zero-hole Sheaf item. Construct the required stage and cocone comparisons directly,
and construct the four object comparisons from the one-model chart comparison.
The simultaneous composition-coherent comparison family is unnecessary.

All existing source signatures, attributes, public imports and non-theorem bodies
are preserved. The existence proof and private proof imports change; the existing
`affineModel_scalarConjugation_nat` proof replaces definitional simplification
by direct application of the same component theorem. There are
eight new private helpers: five explicit data/equation definitions and three
fully proved correctness theorems. No target
meaning changes. The source module is unclaimed.

## Old

```lean
import WeilConjectures.AlgebraicGeometry.AffineCoordinateComparisonCoherence
```

```lean
  obtain ⟨δ, hδ⟩ := exists_affineCoordinateComparisonTransportFamily.{u, w}
```

All stage, cocone and bottom comparisons were supplied by that global family;
the four triangles specialized its simultaneous transport property.

## New

```lean
import WeilConjectures.AlgebraicGeometry.AffineCoordinateComparisonChartCocycle
```

The proof specializes the explicit `affineCoordinateDerivedComparison` constructor
only to the stage and cocone arrows, obtaining θ and θlim. It constructs αE, αK,
βE and βK directly with `affineCoordinateChartObjectComparison`, the supplied
bottom identification and inverse `perfectHomComparison`. No bottom-arrow
natural isomorphisms or comparison-family existence witness are chosen.

`affineModelTransportTriangle_of_comp` proves the elementary naturality calculation.
`affineModelChartTransportTriangle` combines it with the proved one-model chart
cocycle, using `affineModelScalarAssocIso` for scalar reassociation. The two finite
and two cocone equations then follow from `perfectHomComparison_triangle`.
The private predicate `affineModelTransportTriangle` states the generic equation.
`affineModelComparisonObject` and `affineModelProjectionComparison` construct the
object transport and projection component with explicit geometric types.
`affineModelChartTransportEquation` names the resulting one-model equation;
`affineModelLabelledTransportEquation` retains the actual two-label comparison.
`affineModelLabelledTransportTriangle` proves its two Bool cases using the
one-model theorem. Naming these equations and fixing the geometric object types
prevents expansion of very large category arguments during type checking.
Every definition is an explicit construction and every theorem is fully proved;
no obligation is split off.

The earlier source elaboration settings are preserved. Local irreducibility and
scoped transparency settings for the new helpers keep derived localization,
limit cones and the localized functors folded during elaboration. These controls
change no existing exported declaration attribute. The five new private
definitions use `no_expose`. The complete source module, including its compiled
artifact, checks in 56.1 seconds; the assigned re-export checks in 2.6 seconds.
The DAG records the direct proof route.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.AffineModelCoherentObjectComparisons | P2 | Document the repaired source proof route; same public import and API. |
| Sheaf.AlgebraicGeometry.AffineRelativeDualizingComparison | unclaimed | Same public API; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineRelativeTorAmplitudeCriterion | unclaimed | Same public API; no adaptation. |
| Sheaf.AlgebraicGeometry.RelativeDualizingPairRigidity | unclaimed | Same public API; no adaptation. |
| Sheaf.RingTheory.AlgebraicRelativeDualizingIsomorphism | unclaimed | Same public API; no adaptation. |
| Sheaf.TraceFormula.PolynomialDiagonalRhomReduction | unclaimed | Same public API; no adaptation. |
| WeilConjectures.AlgebraicGeometry.AffineModelCoherentObjectComparisons | unclaimed | Proof import and existence proof changed; all existing public signatures, attributes, public imports and non-theorem bodies preserved. |
| WeilConjectures | unclaimed | Same public API; no adaptation. |
| WeilConjectures.AlgebraicGeometry.AffineBaseChangeModelComparisonIsos | unclaimed | Same public API; no adaptation. |
| WeilConjectures.AlgebraicGeometry.AffineBaseChangeModelIsosOfSchemeComparisons | unclaimed | Same public API; no adaptation. |
| WeilConjectures.AlgebraicGeometry.AffineModelComparisonDataFromHomEquations | unclaimed | Same public API; no adaptation. |
| WeilConjectures.AlgebraicGeometry.AffineModelComparisonOfBottomModels | unclaimed | Same public API; no adaptation. |
| WeilConjectures.AlgebraicGeometry.AffineModelLimitHomEquationOfCoherentObjects | unclaimed | Same public API; no adaptation. |
| WeilConjectures.AlgebraicGeometry.AffineModelStageHomEquationOfCoherentObjects | unclaimed | Same public API; no adaptation. |
| WeilConjectures.AlgebraicGeometry.AffinePerfectChainGeometricModels | unclaimed | Same public API; no adaptation. |
| WeilConjectures.AlgebraicGeometry.AffinePerfectChainHomPresentation | unclaimed | Same public API; no adaptation. |
| WeilConjectures.AlgebraicGeometry.AffinePerfectHomPresentation | unclaimed | Same public API; no adaptation. |
| WeilConjectures.AlgebraicGeometry.AffineSpecifiedModelChainComparison | unclaimed | Same public API; no adaptation. |
| WeilConjectures.AlgebraicGeometry.PerfectDescendMorphisms | unclaimed | Same public API; no adaptation. |
| WeilConjectures.AlgebraicGeometry.PerfectHomContinuity | unclaimed | Same public API; no adaptation. |
| WeilConjectures.AlgebraicGeometry.PerfectHomContinuityAffine | unclaimed | Same public API; no adaptation. |
| WeilConjectures.AlgebraicGeometry.PerfectHomPresentation | unclaimed | Same public API; no adaptation. |
| WeilConjectures.AlgebraicGeometry.RecordedPerfectHomContinuity | unclaimed | Same public API; no adaptation. |

The table includes all 22 transitive importers from tools/downstream.py and the
adapted source module itself. Only AffineModelComparisonOfBottomModels calls the
existence theorem textually. No consumer changes are necessary.

The unchanged stage-Hom, limit-Hom, Hom-equation packaging and bottom-model
comparison modules compile against the new source artifact. An import audit of
all eighteen exported declarations and the four downstream theorems reports only
`propext`, `Classical.choice` and `Quot.sound`. No validation-only files are delivered.

## Status

landed 20261021T012419-L-2186971 2026-10-21 (merge of deliver/P2/Sheaf.AlgebraicGeometry.AffineModelCoherentObjectComparisons)
