## What changed

Proved the complete body of `WeilConjectures.PurityFiniteSetting.ChartFactors.chart_dnc_vector_factors` from two separately stated compatibility steps and the existing `bundleOrientation_frames` theorem. Its signature and the definitions `FrameIndependence` and `Conclusion` are unchanged. The frame clause has a complete Lean proof: cancel `normalBundleComparison`, use naturality of the explicit ordinary/pro-etale pullback comparison, and apply the frame theorem to `G ≪≫ f`. The second clause follows by genuine inverse cancellation from the forward integration-adjoint equation.

Extracted the existing canonical constructions, including all previously proved geometry, verbatim to `Sheaf.Paper.ChartDncVectorFactorData`. The original module publicly reexports them; their names, signatures, bodies and visibility are preserved. This dependency extraction lets each compatibility module state its step without importing its consumer. It is not a timeout workaround. The frame proof prevents expensive unfolding of `normalBundleComparison` with a local irreducibility attribute. The original public prerequisites remain publicly available through the data module. No source-library file changes and no consumer adaptations are needed.

The two new compatibility modules are private proof imports of the original module. Updated the existing construction ownership records and the main proof route to match the Lean. The unit's deformation, integration and frame-invariance route is retained.

## Proved and sorry left

Original item: one sorry, in `WeilConjectures.PurityFiniteSetting.ChartFactors.chart_dnc_vector_factors`. Its body is now complete; the item and extracted data module contain zero sorry. Previously proved geometry is preserved, not replaced by assumptions. The private `frame_independence` helper is completely proved from the existing finite-ring frame declaration.

Two new holes remain, each a single public theorem in its own module:

- `WeilConjectures.PurityFiniteSetting.ChartFactors.chart_dnc_naturality`, in `Sheaf.Paper.ChartDncNaturality`, node `lem-pur-chart-dnc-naturality`: only the first, normalized deformation equation, without integration or the frame clause.
- `WeilConjectures.PurityFiniteSetting.ChartFactors.chart_integration_adjoints`, in `Sheaf.Paper.ChartIntegrationAdjoints`, node `lem-pur-chart-integration-adjoints`: only the forward integration-transpose equation, without DNC or the frame clause. The consumer performs inversion and cancellation.

This is a decomposition: one upper hole closed, two strictly smaller holes added; net holes closed minus added is -1. It is not a claim of a sorry-free proof or net progress in the ledger. Both steps quantify the original arbitrary compact-support normalization and use the fixed canonical comparisons. Their statements impose no affineness on U, no frame choice, and no extra extension hypothesis. At rank zero the relevant trace is the identity adjunction; for empty U all displayed morphisms are unique. No data is chosen from either new theorem.

## No longer needed

No module or mathematical dependency is pruned. No original public prerequisite is removed: the import path now passes through the data module. The main proof no longer directly invokes `lem-pur-section-etale-restriction-coherence`, `lem-pur-vector-integration-site-comparison` or `lem-pur-finite-etale-dualizing-normalization`; their three old top-level `tool_uses` approvals are removed from `lem-pur-chart-dnc-vector-factors`. These remain needed in the split compatibility arguments and are not withdrawn from the library. Other original proof dependencies are likewise recorded under the appropriate split nodes rather than imported speculatively by the main proof.

The existing `ChartDncSquare` and `ChartNormalIntegrationSquare` modules are not imported: their `GeneralChartComparisons.Chart` interface assumes affine U and imports the present consumer, so they cannot directly prove this item's non-affine clauses. They are not declared globally unnecessary.

## Where the brief, the DAG or earlier work was wrong

No false original statement or changed target was found. Existing affine-chart equations have a narrower interface than this item's arbitrary U. The original canonical data lived in the same module as its consumer, so direct separate compatibility lemmas would otherwise create an import cycle. The unchanged data extraction resolves that issue. The main node now describes the actual three-part proof rather than suggesting all geometric and integration coherence can be closed by a single application of existing declarations.

## New nodes

`lem-pur-chart-dnc-naturality` records blueprint chart Step 3, second paragraph. Its source-and-proof docstring explains the common etale neighbourhood, restriction coherence, normalized base change, and identification of the actual normal comparison. Module: `Sheaf.Paper.ChartDncNaturality`.

`lem-pur-chart-integration-adjoints` records blueprint chart Step 4, first sentence. Its source-and-proof docstring explains the graded differential, vector integration transpose, restriction to zero, and site transport. Module: `Sheaf.Paper.ChartIntegrationAdjoints`.

`def-pur-chart-dnc-vector-factor-data` attaches the new data module and its unchanged canonical constructions. It introduces no new mathematical object or hole. Existing source-comparison and affine-comparison nodes have their Lean module/file locations updated. Module: `Sheaf.Paper.ChartDncVectorFactorData`.

Change record: `coord/changes/G4-chart-vector-factor-data.md`. It includes the verbatim old and new construction blocks and a table of every current direct importing consumer; all continue to see the same declarations through the public reexport.

## Second reading by G4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
