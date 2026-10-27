## What changed

In `lean/Sheaf/Paper/VectorIntegrationChartComparison.lean`, completed four existing
supporting theorem proofs. All declaration signatures, definitions, attributes and
public imports are unchanged.

`unit_properties` uses constructibility of the constant finite coefficient sheaf,
bounded constructibility of its degree-zero single complex, and flatness of the
monoidal unit to obtain Tor amplitude [0,0]. Added the private proof import
`WeilConjectures.ConstructibleSheaf.SpecializationCriterion` for the constant-sheaf
constructibility theorem.

`orderedSourceIso_existsUnique` unfolds the zero and successor source coordinates;
HEq determines the hom, and `Iso.ext` determines the isomorphism. `open_geometry`
uses the existing Noetherian-open and composition instances.

`restrictedMap_existsUnique` proves joint equality of the recursive tower scheme
and its projection by induction. Transport along that sigma equality gives the
required endpoints, retaining the actual raw map. HEq proves uniqueness. In
particular, the argument does not choose an arbitrary orientation or map.

The completed proofs follow Step 1 and the endpoint-identification arguments in
the existing docstrings. The final theorem's DAG proof route is retained. No
statement, definition, source-library body, consumer, or DAG node was changed.

## Proved and sorry left

Closed 4 of the 5 original holes, all in namespace
`AlgebraicGeometry.ProEtale.VectorIntegrationChart`:

- `unit_properties`.
- `orderedSourceIso_existsUnique`.
- `open_geometry`.
- `restrictedMap_existsUnique`.

One original hole remains, unchanged:
`AlgebraicGeometry.ProEtale.VectorIntegrationChart.vectorIntegration_chart_comparison`
(blueprint node `lem-pur-vector-integration-chart-comparison`).
No holes were added, no statements were split off, and no definitions contain
`sorry`. This is a partial delivery under the brief's multiple-sorry-module rule.

The remaining proof must identify the exceptional mate of the chart-restricted
ordinary vector trace with the compared ordinary affine trace, then match its
unit-coefficient transpose with `AffineOrderedIntegration.integrationTranspose`.
`AffineOrderedIntegration.ordered_integration_transposes` gives the subsequent
identification with `affineSpacePurityComparison`. The exponent clause also needs
the canonical coefficient pullback/transition square; the ordinary global trace
transition is supplied by `IntegrationExponentTransposeTransport`. These named
declarations were read; they are not being treated as an obstacle because their
proofs still have holes. The missing work is the Lean composition of their
specified coordinate maps, unitors, and comparison-adjunction units.

The module compiled with all four completed proofs. The delivery tool performs
the final compile, axiom, consumer and packet checks.

## No longer needed

Removed the following unused private imports; the declarations needed for the
current definitions and completed proofs are already supplied through the retained
public imports:

- `Sheaf.Paper.FiniteTorAmplitudeSites`.
- `Sheaf.Paper.VectorPurityNormalization`.
- `Sheaf.Targets.VectorBundlePurity`.
- `Sheaf.Paper.TraceTransposeBaseChange`.
- `Sheaf.Paper.CompactSupportSiteCoherence`.

No node or module is claimed pruned from the targets' closure. The final theorem
remains open, so its declared proof dependencies and the unit's route are retained.
No dependency was imported solely because it was named in the plan.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement error was found. The two recursive affine towers have
the same zero and successor constructions, but are separate recursive definitions;
they are not definitionally equal at a variable dimension. Their scheme and
projection must be transported together, as done in `restrictedMap_existsUnique`.
No definition repair, forced consumer adaptation, or change record is required.

## Second reading by Z9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
