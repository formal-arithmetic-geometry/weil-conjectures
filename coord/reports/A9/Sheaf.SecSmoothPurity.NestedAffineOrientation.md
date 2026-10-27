## What changed

Replaced the proof hole of
`WeilConjectures.PurityFiniteSetting.NestedAffine.nested_affine_orientation`
by an assembly of three strictly partial comparison statements. The assembly
pulls the affine equality back through `chartPull`, substitutes both chart
restriction formulas, and proves the two global constructible finite-Tor clauses
using the existing ordinary-etale preservation API
(`WeilConjectures/SixFunctors/Etale/Derived/Stability/UpperShriek.lean` and
`Stability/Basic.lean`). The even-block sign is
proved directly for all natural ranks, including zero.

Moved the existing coordinate definitions, `NormalizedInputs`, `Statement`, and
four already-proved geometric helpers verbatim to
`Sheaf.SecSmoothPurity.NestedAffineFormulaData`. The original module publicly
reexports them. This relocation was undertaken to state the three comparison
steps without an import cycle, before any compile-time-limit failure; it does not change their definitions, signatures, visibility, or meaning.
The main theorem's signature is unchanged. Proof-local irreducibility
attributes keep the shared arrow constructions folded during conjunction
assembly; they do not change any exported definition or reducibility attribute.
A file-local `maxRecDepth 4096` accommodates the expanded formula terms. Profiling
of the failed default-depth run measured 709 ms in tactics; no compile-time
limit or transparency-respect option is changed. No source-library file or target
statement is changed. There are no current Lean importers requiring adaptation.
The original node remains needed by unfinished DAG parents.

Added the three proof modules listed below and updated the original node's
proof route and Lean attachment. The unit route through composition on affine
charts is retained. Change record:
`coord/changes/A9-nested-affine-formula-data.md`.

Validation: the four supporting modules compiled in the sandbox set compile.
The final assembly then compiled cleanly as a single file against those modules
(exit 0, 13.3 seconds), with all profiling options removed. The source and node
signature checks and import-cycle check also passed.

## Proved and sorry left

Closed the one original proof hole, in
`WeilConjectures.PurityFiniteSetting.NestedAffine.nested_affine_orientation`.
Its assembly proof has no local holes. The previously proved helpers `blockEq`, `blockProjection`, `mapEtale`, and
`chartComposite` in the same namespace retain their original complete proofs.

Added exactly three named proof holes, each in its own new module:

- `WeilConjectures.PurityFiniteSetting.NestedAffine.nested_affine_normalized_inputs`
  (`lem-sp-nested-affine-normalized-inputs`): normalization and domain facts for
  affine integration, independent of the nested chart data.
- `WeilConjectures.PurityFiniteSetting.NestedAffine.nested_affine_integration_regrouping`
  (`lem-sp-nested-affine-integration-regrouping`): the affine equality before
  pullback, independent of arbitrary smooth maps and their charts.
- `WeilConjectures.PurityFiniteSetting.NestedAffine.nested_affine_chart_formulas`
  (`lem-sp-nested-affine-chart-formulas`): only the two restriction identities,
  under the normalization premise; it contains neither the affine regrouping
  equality nor the final equality of restricted orientations.

This is a decomposition, not an unconditional proof or a positive net hole
reduction: one hole closed and three added, net minus two. No definition has a
hole and no data is selected from an unproved existence statement.

## No longer needed

Removed these direct private imports from the assembly module:

- `Sheaf.Paper.SfPreservationClass`
- `Sheaf.Paper.EtaleCtfChartDomain`
- `Sheaf.Paper.DualizingUnitComposite`
- `Sheaf.Paper.ChartExceptionalMateCoherence`
- `Sheaf.Paper.DiagonalOrientationCharts`
- `Sheaf.Paper.EtaleCartesianTowerTensorComparison`
- `Sheaf.Paper.AffineSpacePurityComposition`
- `Sheaf.Paper.AffineSpacePurityComparison`
- `Sheaf.CategoryTheory.OrderedAdjointTowerRegrouping`

The assembly instead imports the three named steps and the native ordinary
exceptional-preservation API. The removed imports' mathematical ingredients
remain needed in the split steps, as recorded in their proof dependencies;
none of those nodes or modules is claimed globally pruned or withdrawn.
The existing public imports are preserved transitively through the data module.
No unit step is bypassed. Pruned modules: none.

## Where the brief, the DAG or earlier work was wrong

The planned preservation and comparison interfaces are mostly expressed in the
pro-etale finite-coefficient category, while this module fixes canonical
ordinary-etale coordinates. Their signatures do not directly supply the
normalization, tensor transport, and regrouping equations in these coordinates.
The new steps record those precise comparison obligations, including the
finite-site comparison squares rather than assuming arbitrary orientations.
The native ordinary-etale preservation theorems do directly supply the two
remaining global domain clauses.

Only the affine projection square over the middle chart is used as Cartesian;
the full outer square of arbitrary nested etale charts is not assumed Cartesian.
Zero ranks and the empty scheme remain included in the new statements and their
proof plans. No false statement or target-statement repair is proposed.

## New nodes

The full blueprint index returned no matches for `nested affine`,
`ordered affine integration`, or `normalization finite Tor`. Its ancestor
lookup identifies `det-sp-composition-factors`, which is the recorded ancestor
of all four new nodes.

`def-sp-nested-affine-formula-data` attaches the existing, unchanged coordinate
constructions and geometric helpers to their new shared module. It introduces
no new proof hole and preserves the original statement dependencies.

`lem-sp-nested-affine-normalized-inputs` records projection-purity agreement,
unit normalization, finite-Tor domains, and the identity normalization at rank
zero, all in the existing ordinary coordinates.

`lem-sp-nested-affine-integration-regrouping` records the ordered affine
composition equation, including identity endpoints for either empty block.

`lem-sp-nested-affine-chart-formulas` records the total-chart and tensor-chart
restriction equations under normalized inputs, before any affine regrouping.
Each new theorem has a source and complete natural-language proof in its
module docstring and corresponding node. The change record is
`coord/changes/A9-nested-affine-formula-data.md`.

## Second reading by A9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
