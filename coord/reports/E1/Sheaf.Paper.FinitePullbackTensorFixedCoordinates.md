## What changed

Proved `WeilConjectures.CompactSupportFiniteProjection.pullbackTensor_fixed_coordinates`
in `Sheaf.Paper.FinitePullbackTensorFixedCoordinates`, keeping its statement and public
import unchanged. The proof writes the defining ambient comparison as a realized
fixed-coordinate composite, applies `Equivalence.unitInv_naturality`, and cancels the
second-input comparison using functoriality and the isomorphism inverse identity.
The first-input inverse comparison remains exactly as in the statement. A proved
private helper packages functorial cancellation, avoiding rewriting across the large
realization expressions.

Local irreducibility of `realization` and `ProEtale.derivedTensor` prevents unnecessary
unfolding while checking the explicit composites. These are local proof elaboration
settings; no shared definition or exported attribute changes. Updated the item's DAG
proof steps to describe the two cancellations. No other existing module is changed. Final import-order compilation checked the
unchanged source of `Sheaf.Paper.FiniteProjectionFixedCoordinates` (24.6 s) and the
item (34.1 s), with no errors or warnings. The unchanged dependency copy was removed
from the sandbox after this check and is not delivered.

## Proved and sorry left

Closed the one original hole in
`WeilConjectures.CompactSupportFiniteProjection.pullbackTensor_fixed_coordinates`
(node `lem-sf-finite-pullback-tensor-fixed-coordinates`). Zero holes remain in the item;
zero holes and zero split statements were added. This is a proof, not a decomposition.
The argument uses naturality and inverse identities uniformly, including zero objects
and empty schemes, without properness or a Tor assumption on the first input.

## No longer needed

None. The existing public import `Sheaf.Paper.FiniteProjectionFixedCoordinates` remains
necessary for the statement; both declared proof dependencies are used. No node or
module is withdrawn, and the unit route is preserved. No new proof imports are needed.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction was needed. The current server queue lists the module as
a one-hole stage-3 proof item. The historical rework record and global-build error
record its failed dependency import; the module and its Lean attachment are preserved.
The proof closes the existing obligation directly without repeating the earlier splits.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.FinitePullbackTensorFixedCoordinates": "bfc9475bba501db8ba56ffdd0271375ba9c390cd"}, "results": {"Sheaf.Paper.FiniteProperProjectionTranspose": {"hash": "e383f59ebf5c73b50c4f1b2fc2e2fbe451929c34", "status": "OK"}}, "seconds": 104, "time": "2026-10-28T00:51:00+0800", "transitive": 0, "version": 1}
```

## Second reading by E1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
