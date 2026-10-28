## What changed

Reduced both existing holes in `Sheaf.Paper.CoefficientTwistsDetailed` to the
first-root scalar comparison. The existing signed-line comparison constructs the
maps on powers and duals. Root-tensor uniqueness proves uniqueness in degree one;
tensor-section extensionality propagates it to positive powers, and scalar-dual
extensionality proves it for negative powers. The second theorem identifies the
chosen ordinary scalar-extension presentation with this comparison and proves
uniqueness on pure tensors.

Added one module for the remaining first-root comparison. Its assertion concerns
only the integral root line, not the family of signed twists. Its docstring gives
the construction, local inverse, and uniqueness argument. Existing statements,
definitions, and public imports retain their interfaces. Local sheafification
instance caches inside the private proof avoid repeatedly constructing the
same site instances; no new command-level attributes or sections are used. Profiling
then still found the enlarged file over the limit, so two proved helpers were
extracted into `OrdinaryScalarTensorLineTransport` and `ScalarSemilinearDualExt`.
Both have complete proofs and no holes. The former preserves the existing
tensor-line comparison proof while making its tensor sections an explicit
parameter; the latter records the generic dual extensionality argument.

The four-file dependency chain compiled in import order. The item took 52.2
seconds with profiling enabled; the helper modules took 6.3, 13.0 and 8.8
seconds. Profiling options were removed for delivery. Preflight subsequently required removing the proof marker from the root
node’s recorded signature. Its search advice was addressed by explicit
LeanSearch queries, and caches were moved inside the private proof to preserve
the original command context. With those proof-local caches the item compiled
in 40.2 seconds; the three `letI` style suggestions were then applied as `let`.
The delivery tool performs final compilation and preflight on these final files.

## Proved and sorry left

Closed the original holes in:

- `WeilConjectures.twistScalarMaps_existsUnique`.
- `WeilConjectures.twistLineScalarIso_existsUnique`.

Added one hole:

- `WeilConjectures.firstRootCoefficientScalarComparison` in
  `Sheaf.Paper.FirstRootCoefficientScalarComparison`, node
  `lem-pur-first-root-coefficient-scalar-comparison`.

The item module has zero remaining holes; the delivery adds one named theorem
with `sorry`. This is a decomposition of two holes into one strictly smaller
first-line comparison, with a net reduction of one hole, not two independent
completed proofs. No definition contains a new hole.

## No longer needed

No existing module or node is withdrawn. No existing item import is removed.
The route uses the existing generic signed-line comparison, so no separate
coefficient-specific construction of each tensor power or negative dual is
needed. The initial snapshot had no separate proof dependencies for the two holes.
Both nodes received written statements and expanded proof plans on the server
during this work. The replacement route uses the first-line comparison, the
published local rank-one theorem, the signed-line comparison, and the existing
ordinary tensor presentation. The following obsolete `tool_uses` approvals were
removed, preserving the relative order of all approvals retained:

- `lem-route-twist-line-scalar-iso-exists-unique`: `lem-pur-sheaf-ring-coefficient-ordinary-adjunction`, `lem-pur-twist-root-local-models`, `lem-sfb-localized-site-tensor-restriction`, `lem-pur-twist-coefficient-tensor`, `lem-pur-tensor-pushout-action`, `def-sp-canonical-scalar-extension-maps`, `lem-sfb-sheaf-cover-local-isomorphism`, `lem-weil-ramified-finite-tensor-sections`.

These are dependency-edge removals, not module withdrawals: for example, the
root local models are still used by the remaining first-line lemma. No global
module-pruning claim is made.
The new root module imports only the root-line definitions, scalar inclusion,
and scalar-extension API needed by its statement.

## Where the brief, the DAG or earlier work was wrong

The initial snapshot had provisional scalar-comparison nodes. The server
received both nodes’ written statements while this proof was in progress.
The first delivery attempt detected drift in the scalar-isomorphism node; the
retry detected drift in the family node. All 14 direct importers passed on
both attempts. Both node copies were refreshed from the server, preserving
its current statements and other metadata; only proof metadata and obsolete
dependency approvals are changed. No Lean statement is changed or disputed.

## New nodes

- `lem-pur-first-root-coefficient-scalar-comparison`: root-normalized scalar
  extension in exponent one, including uniqueness of its semilinear adjunct.
  This is the base case of the signed-line construction. The remaining hole
  is recorded with its source, proof in words, Lean declaration, and searches.

- `lem-pur-ordinary-scalar-tensor-line-transport`: the existing proved tensor-line
  transport helper, generalized over explicitly specified ordinary pure sections
  and extracted into its own module. This adds no hole.
- `lem-pur-scalar-semilinear-dual-ext`: the proved extensionality step for negative
  twists, extracted into its own module. This adds no hole.

## Related modules compiled before delivery

14 related module(s) compiled against this delivery by deliver3.py: 14 OK.

```json
{"capped": false, "direct": 14, "left_out": 0, "own": {"Sheaf.Paper.CoefficientTwistsDetailed": "0deda6e116a7ea95d9063783cee229ea120737b8", "Sheaf.Paper.FirstRootCoefficientScalarComparison": "412a1a909392a9813c57ffb48a734b61696dea68", "Sheaf.Paper.OrdinaryScalarTensorLineTransport": "88309cdbddeca581eb6caedf55784f3e6914d6ee", "Sheaf.Paper.ScalarSemilinearDualExt": "822cac1533e9b6b5ce9edebfecb337de86d05033"}, "results": {"Sheaf.Paper.AffineLineOrdinaryInvariance": {"hash": "3cb26936e3d4fc4b2b3c6554c62c91ff7b686b08", "status": "OK"}, "Sheaf.Paper.FiniteTateSiteDescentDefinitions": {"hash": "6529ff5404d860b796f707a4a4c13ac38692ea43", "status": "OK"}, "Sheaf.Paper.FrobeniusPositivePowerTransport": {"hash": "976e644e36286443b501e9dc9b51da25f1988a35", "status": "OK"}, "Sheaf.Paper.FrobeniusSignedPowerTransport": {"hash": "5015038bc4119e490672454ec7de94a864180641", "status": "OK"}, "Sheaf.Paper.IntegralLineTensorCompleteness": {"hash": "d0e5300b279bf3f5ef1f7e289b1f63350bdf144b", "status": "OK"}, "Sheaf.Paper.IntegralRootPowerGenerators": {"hash": "0a254681b13ed83d51f879a6e63780503a4ab625", "status": "OK"}, "Sheaf.Paper.IntegralTwistBaseChange": {"hash": "5a2885e6aa6346598dbeae80a00ae4afb58be448", "status": "OK"}, "Sheaf.Paper.IntegralTwistBaseChangeDefinitions": {"hash": "592a0b0c3daac172fb416a70a493aef732ce93aa", "status": "OK"}, "Sheaf.Paper.IntrinsicCoefficientTwists": {"hash": "1b36a0cead99940a3f501803fff0bf1fde54cef5", "status": "OK"}, "Sheaf.Paper.PurIntegralTwistLineInverseImage": {"hash": "13be10ce3e24bea123b16557ca6d2e6871a9973c", "status": "OK"}, "Sheaf.Paper.RationalAffineTensorCalculus": {"hash": "d011e06c3809ad598674b2ea10c06d16b07c32e6", "status": "OK"}, "Sheaf.Paper.RelativeSupportCoordinateModel": {"hash": "10578c3766ba1e2284ed91a08ab128bdc7d1ccf5", "status": "OK"}, "Sheaf.Paper.SignedLineTensorEquivalence": {"hash": "8051cbd29caa2f0a3002856da5697351abaad243", "status": "OK"}, "Sheaf.Paper.TateTwistFiniteLocallyFree": {"hash": "5db6ce289363b96eeb20f9f16989df490a3db3bc", "status": "OK"}}, "seconds": 85, "time": "2026-10-28T07:32:07+0800", "transitive": 0, "version": 1}
```

## Second reading by C2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
