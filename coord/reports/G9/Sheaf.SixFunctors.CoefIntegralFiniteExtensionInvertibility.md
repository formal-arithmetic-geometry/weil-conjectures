## What changed

The target module now assembles its unchanged theorem statement from three strictly
smaller public component theorems.  The triangulated-structure, canonical-dualizing,
and evaluation-comparison obligations are each declared in its own Sheaf module with
its own blueprint-tagged DAG node.  The target imports those modules privately and
proves the conjunction by direct constructor application.  No existing source-library
module or public target signature was changed.

## Proved and sorry left

The target's original `comparison_invertibility` hole is closed by a genuine
three-part decomposition and the conjunction assembly is proved in Lean.  No
component obligation could be completed from the currently available declarations.
Three strictly smaller named sorries were added:

- `comparison_invertibility_triangulated`, node
  `lem-sf-integral-finite-extension-triangulated`;
- `comparison_invertibility_u`, node
  `lem-sf-integral-finite-extension-u-invertibility`;
- `comparison_invertibility_v`, node
  `lem-sf-integral-finite-extension-v-invertibility`.

There are no sorries inside definitions, and no axiom or unsafe declaration was
added.

## No longer needed

The target proof no longer directly imports or claims the eleven detailed proof
dependencies from the original DAG route.  Those dependencies remain attached to the
three split component nodes where their corresponding mathematical steps are stated.
No Lean import from the original target was removed; its proof-only imports are exactly
the three component modules used by the assembly proof.  No existing declaration was
withdrawn.

## Where the brief, the DAG or earlier work was wrong

The prior item bundled triangulation, dualizing invertibility, and evaluation
invertibility into one theorem, while the available library exposes no theorem that
closes any of those ambient obligations.  Treating the bundle as one proof would leave
an unstructured gap.  The route is therefore decomposed into three strict component
obligations, each with a smaller conclusion and an independent DAG record.  The
original target statement and its unit route are unchanged.

## New nodes

`lem-sf-integral-finite-extension-triangulated` records the ambient CommShift and
triangulation obligation.

`lem-sf-integral-finite-extension-u-invertibility` records invertibility of the
canonical dualizing comparison `u` under the full scheme and dualizing hypotheses.

`lem-sf-integral-finite-extension-v-invertibility` records invertibility of the
evaluation comparison `v` for complete ambient inputs and tensor presentations.

## Related modules compiled before delivery

18 related module(s) compiled against this delivery by deliver3.py: 18 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.SixFunctors.CoefIntegralFiniteExtensionInvertibility": "bc6d2cee3ee60dda8a76937e86a1e840f78ccc55", "Sheaf.SixFunctors.CoefIntegralFiniteExtensionInvertibilityTriangulated": "6835bd29bb1f055cc587f86acdac75fde5e2f48c", "Sheaf.SixFunctors.CoefIntegralFiniteExtensionUInvertibility": "742b3003747509e8e87f12e064da856360ad3c38", "Sheaf.SixFunctors.CoefIntegralFiniteExtensionVInvertibility": "1821fb8f9af5c355baf6322544140526bfbda9ab"}, "results": {"Sheaf.Paper.FiniteRestrictionDiagramNaturality": {"hash": "81365072e344a50c7cddc314c30b496374b0359e", "status": "OK"}, "Sheaf.Paper.FixedPresentationUniformizerReductions": {"hash": "2195e8aeb4868a9a702ababa433fe6e635c0b07e", "status": "OK"}, "Sheaf.Paper.GeometricSmoothReconstructionSetup": {"hash": "d5f8abc24f480c3f5afd7ca4f7437295faaef56c", "status": "OK"}, "Sheaf.Paper.IntegralGeometricComparisonData": {"hash": "cc2707568a162b346675b69ebc8591da39fe2c52", "status": "OK"}, "Sheaf.Paper.IntegralGeometricComparisonRealization": {"hash": "e2edc201638183226483011a57348a50acc201a4", "status": "OK"}, "Sheaf.Paper.IntegralGeometricPurityRealization": {"hash": "0b3aa89bec9034609abf2e195b105fef87d9a785", "status": "OK"}, "Sheaf.Paper.IntegralGeometricReindexingRealization": {"hash": "dc82db56836939bdf56488314584512a9aad340d", "status": "OK"}, "Sheaf.Paper.IntegralGeometricSupportRealization": {"hash": "9ba359469968ecca14a23af8cb500f18fb9dd9c6", "status": "OK"}, "Sheaf.Paper.IntegralGeometricTransposeIdentity": {"hash": "1ae653a0bbd43cc9d3515b58d0ae07ae3f6015a9", "status": "OK"}, "Sheaf.Paper.NormalizedIntegralTraceData": {"hash": "f7c116653c7faa062b478b61abb0a121463a5af7", "status": "OK"}, "Sheaf.Paper.RamifiedScalarSystemTranspose": {"hash": "53ac490826ec5a0fa35c7c8f9a5ca4c9b3fca77d", "status": "OK"}, "Sheaf.Paper.SystemScalarBasisDistributivity": {"hash": "d1e277ef767e0f140397fd95175d477b01bfab8d", "status": "OK"}, "Sheaf.Paper.SystemScalarProjectionData": {"hash": "6e6a70ab41d6f19ceee232ba81eb824f4b6f89c8", "status": "OK"}, "Sheaf.Paper.SystemScalarProjectionIdentification": {"hash": "1c756cefdef2387f213274b53f0077c897f22016", "status": "OK"}, "Sheaf.Paper.SystemScalarRefinementRestriction": {"hash": "ddecac2836e96c2ff72d7facaa63210ecf22337a", "status": "OK"}, "Sheaf.Paper.SystemScalarTensorConstituents": {"hash": "096756fb6038c07c81567f421c86a658ef0c40a6", "status": "OK"}, "Sheaf.Paper.TransportIntegralCounitRealization": {"hash": "362789f01525bd317330b272608a9f8d1b5f57d3", "status": "OK"}, "Sheaf.SixFunctors.CoefIntegralFiniteExtension": {"hash": "a80bce78cffaf702f091a3521d667088921b08f8", "status": "OK"}}, "seconds": 209, "time": "2026-10-28T01:15:50+0800", "transitive": 17, "version": 1}
```

## Second reading by G9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
