## What changed

Replaced the hole in `transportedGamma_adjunct_bridge` by a categorical proof.
Left-adjoint uniqueness transports the adjunct. The existing intrinsic
`gamma_adjunct` equation and bridge cancellation then finish from the forward
lambda comparison. The assigned signature and public import are unchanged.

The forward comparison is proved by a five-factor pasting calculation from three
strictly smaller statements: the cartesian/restriction prefix square, the
clopen/compositor tail square, and the formal component expansions of the two
lambda words. The actual morphisms are stored in `properOpenBridgeWord`, a
structure constructed from the existing operations without any data holes.
This representation prevents repeated conversion through the derived-category
models when checking the categorical proof.

Only the assigned existing module and its node change. The support modules and
nodes are new. The current server queue identifies the assignment as a one-hole
proof item, with no current rework row or build-error file.

## Proved and sorry left

Closed the original hole in
`WeilConjectures.IntegralSystemRealization.transportedGamma_adjunct_bridge`
by decomposition. The assigned module has zero holes. The new forward theorem
`WeilConjectures.IntegralSystemRealization.properOpenLambda_bridge` is proved,
as is its private generic pasting lemma.

Exactly three new holes remain, each in its own module:

- `WeilConjectures.IntegralSystemRealization.properOpenPrefix_bridge`,
  node `lem-sf-integral-system-proper-open-prefix-bridge`.
- `WeilConjectures.IntegralSystemRealization.clopenTail_bridge`,
  node `lem-sf-integral-system-clopen-tail-bridge`.
- `WeilConjectures.IntegralSystemRealization.lambdaWord_expansions`,
  node `lem-sf-integral-system-lambda-word-expansions`.

This is a decomposition: one hole closed and three added, not net hole closure.
The prefix omits the final clopen/compositor tail. The tail uses neither the
cartesian nor restriction factor. The expansions are only the component formulas
for the two defined lambda words and use no bridge compatibility. No split
statement contains gamma or the assigned adjunct equality.

Identity arrows and empty opens require no additional hypotheses in these
factor calculations: the same units and section identities apply. The final
equality transport includes reflexive equality. The expansions are formal
component identities. These are mathematical edge-case checks, not proofs of
the remaining statements in Lean.

## No longer needed

None in the existing library. The original public import and blueprint unit route
are retained. No source-library declaration or module is withdrawn. Unsubmitted
exploratory drafts have been excluded from this packet; they are not pruning of
published work.

## Where the brief, the DAG or earlier work was wrong

The earlier single step called for identifying the lambda factors without
stating the compatibility equations needed for that calculation. The prefix and
tail statements make those obligations explicit. Their ordinary-section and
cochain-normalization arguments remain to be formalized, as does the purely
formal component expansion.

Direct component calculations repeatedly exceeded the per-file kernel-checking
limit because of derived-category conversion. The delivered diagram stores the
same real morphisms once and gives the categorical proof small field types.
No timeout is treated as a tool failure. Mathlib searches found adjunction
uniqueness and conjugate-isomorphism APIs, but no integral factor bridge theorem.

## New nodes

- `def-sf-integral-system-proper-open-bridge-word`, module
  `Sheaf.SixFunctors.IntegralSystemProperOpenBridgeWord`: `BridgeWord` records the
  objects and morphisms of the diagram; `properOpenBridgeWord` constructs them
  from the prescribed operations. There is no chosen witness or postponed data.
- `lem-sf-integral-system-proper-open-prefix-bridge`, module
  `Sheaf.SixFunctors.IntegralSystemProperOpenPrefixBridge`: the prefix square.
- `lem-sf-integral-system-clopen-tail-bridge`, module
  `Sheaf.SixFunctors.IntegralSystemClopenTailBridge`: the tail square.
- `lem-sf-integral-system-lambda-word-expansions`, module
  `Sheaf.SixFunctors.IntegralSystemIntrinsicLambdaExpansion`: both formal
  component expansions, independent of the bridge squares.
- `lem-sf-integral-system-proper-open-lambda-bridge`, module
  `Sheaf.SixFunctors.IntegralSystemProperOpenLambdaBridge`: the proved pasting
  calculation combining the preceding three equations.

Each node records its Lean statement, source, proof in words, and searches.
No existing definition, signature, instance, public attribute or public import
changes. Local proof attributes in the assigned module only control elaboration.

The elaboration-only commands and new support interfaces are recorded in
`coord/changes/IntegralSystemProperOpenTransportAdjunctBridge.md`.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.SixFunctors.IntegralSystemClopenTailBridge": "d7462262f508bee2e7d9c6cd147a0979fb730a16", "Sheaf.SixFunctors.IntegralSystemIntrinsicLambdaExpansion": "8d8e14332c23798c9766e8a0c277431d33bec839", "Sheaf.SixFunctors.IntegralSystemProperOpenBridgeWord": "05da9da3f261917280d2330c8ba96fa3fcdde11a", "Sheaf.SixFunctors.IntegralSystemProperOpenLambdaBridge": "c0e422c5951ad8e83352ca71305f5e73d3371176", "Sheaf.SixFunctors.IntegralSystemProperOpenPrefixBridge": "6e4775720dfdcebd4f614202f1a8148c36145327", "Sheaf.SixFunctors.IntegralSystemProperOpenTransportAdjunctBridge": "4ede7072590a484bfb93d130f2c6166c5e382074"}, "results": {"Sheaf.SixFunctors.IntegralSystemProperOpenTransportAdjunct": {"hash": "abdbfc787c233060769e2299661400dc96bf0f92", "status": "OK"}}, "seconds": 29, "time": "2026-10-28T13:49:16+0800", "transitive": 0, "version": 1}
```

## Second reading by H5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
