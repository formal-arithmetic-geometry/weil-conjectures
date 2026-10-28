## What changed

The item's unchanged theorem now combines vanishing on the base open and its canonical
closed complement using `proEtaleRingModule_isZero_of_open_closed`. All three added
imports of the item are private proof imports; its public imports and signature stay unchanged.

Added `Sheaf.AlgebraicGeometry.ProEtaleOpenInjectiveProperAcyclicOpenRestriction`, with a
complete proof. It constructs the actual fibre product, proves the induced source open
is clopen, transports the clopen direct-image/injective calculation through the canonical
coefficient equivalences, and applies derived open restriction plus injective acyclicity.
The final coordinate comparison uses `openSquarePullbackModel`; the homology functor is
commuted only with exact pullback.

Added `Sheaf.AlgebraicGeometry.ProEtaleOpenInjectiveProperAcyclicBoundaryRestriction`,
which states just the missing closed-restriction step. Updated the item's DAG proof and
added matching nodes for both restrictions. No existing definition or statement changes.

Validation: all three modules compile together, individually in import order, through
`lcompile.py --all`; the completed open proof took 8.0 seconds and the item 2.9 seconds.
The open proof has no sorry. The boundary assertion retains the named whole-theorem sorry.
Edge cases checked in the statements: the empty open and empty closed complement are
allowed, the zero coefficient ring is allowed, and q=0 is not accidentally asserted.
The proof reconstructs the fibre product rather than assuming the witness is Cartesian.

## Proved and sorry left

Closed the item's original hole in
`AlgebraicGeometry.Scheme.isZero_higherDirectImage_open_injective_of_proper_of_witness`.
Its proof from the two restrictions is complete.

Also proved
`AlgebraicGeometry.Scheme.isZero_openRestriction_higherDirectImage_open_injective_of_proper`
(node `lem-sp-proetale-open-injective-proper-acyclic-open-restriction`), without adding a
proof hole or requiring the geometric witness.

Added one remaining hole:
`AlgebraicGeometry.Scheme.isZero_boundaryRestriction_higherDirectImage_open_injective_of_proper`
(node `lem-sp-proetale-open-injective-proper-acyclic-boundary-restriction`). It is exactly
the closed-boundary part, not the original global vanishing under a different name.
Original item: 1 sorry before, 0 after. New modules: 1 sorry total. This is a decomposition,
with zero net holes closed; it does not certify the full acyclicity theorem independently
of sorry. The complete open calculation is retained for the next worker.

## No longer needed

No existing public or proof import was removed. No global module pruning is claimed.

The item's former direct proof dependencies
`lem-sf-proetale-open-closed-sequence`, `lem-weil-extension-by-zero-adjunction`,
`lem-weil-extension-by-zero-exact`, `lem-exc-proetale-derived-open-restriction`,
`lem-sp-proetale-proper-boundary-cohomology`, and
`lem-weil-pbc-proetale-weakly-contractible-evaluation-exact` are replaced at this node
by the two restriction nodes and `lem-exc-open-closed-detection`.
The open restriction retains the open adjunction and derived restriction through their
existing implementations; the boundary node retains the relevant localization/evaluation
plan. These changes do not claim that those modules are unused elsewhere.

The etale-origin-only `ProEtaleProperBoundaryCohomology` is not imported or applied to an
arbitrary injective sheaf. It cannot close the boundary step with the item's hypotheses.

## Where the brief, the DAG or earlier work was wrong

The parent plan's boundary-cohomology application does not match its cited theorem:
`proEtale_proper_boundary_cohomology` has an explicit `hetale` witness, while this item
has no etale-origin assumption on J. Injectivity alone has not supplied that witness.
The outstanding boundary node records this gap explicitly; no extra hypothesis was added
to the item, and the narrower theorem is not used under an unsatisfied premise.

`OpenProperClopenWitness` records factorization equations and open/proper/closed properties,
but does not assert that its V is the fibre product. The completed open proof therefore
constructs the actual fibre product instead of treating the witness as Cartesian.

The current blueprint under `literature/blueprint/latest` has moved the unit to
`sec-six-functors-basics` and states an exceptional adjoint on the localizing constructible
class, rather than the old all-pro-etale clause (b). The unchanged assignment and node still
refer to that historical clause; this delivery preserves their statement and isolates its
unresolved arbitrary-injective boundary content. Its source record points to the actual
parent proof plan, not to a nonexistent current blueprint path.

A preliminary fixed-degree restatement was discarded before the final packet; it is not
part of the delivery. Mathlib searches through LeanFinder, Loogle, LeanSearch and grep found
no complete specialized theorem; the generic injective-acyclicity lemma found by grep is
used in the open proof.

## New nodes

`lem-sp-proetale-open-injective-proper-acyclic-open-restriction`: a proved open-restriction
statement, implemented by `ProEtaleOpenInjectiveProperAcyclicOpenRestriction.lean`.

`lem-sp-proetale-open-injective-proper-acyclic-boundary-restriction`: the outstanding
closed-boundary statement, implemented by
`ProEtaleOpenInjectiveProperAcyclicBoundaryRestriction.lean`. Together the two restrictions
imply the unchanged item by existing open-closed detection. No change record is needed for
an existing public interface, since none changes.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.AlgebraicGeometry.ProEtaleOpenInjectiveProperAcyclicBoundaryRestriction": "fb70d957a86b473f56287755ef84c758873f9d78", "Sheaf.AlgebraicGeometry.ProEtaleOpenInjectiveProperAcyclicFromWitness": "9e5fade8bfe1860f830030c1bef852c5fb56dfed", "Sheaf.AlgebraicGeometry.ProEtaleOpenInjectiveProperAcyclicOpenRestriction": "868930a970050943a86bc66a1893bc20711eed00"}, "results": {}, "time": "2026-10-28T09:33:22+0800", "transitive": 0, "version": 1}
```

## Second reading by F1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
