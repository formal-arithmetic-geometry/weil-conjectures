# IsomorphicSingleTensorCounit proof imports
## Reason
The target proof uses two new proof-only modules.
## Old
No proof-only imports.
## New
The item adds the proof-only import
`import Sheaf.AlgebraicGeometry.IsomorphicSingleTensorCounitEquation`.
The new equation module publicly imports
`Sheaf.AlgebraicGeometry.IsomorphicSingleTensorCounitTransport` because its
statement selects the uniquely characterized transport. The new transport
module publicly imports `Sheaf.AlgebraicGeometry.PinnedSingleTensorShifts`
for its signature.
## Users
| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.IsomorphicSingleTensorCounit | T2 | required proof imports |
## Status
landed 20261013T190155-L-3221152 2026-10-13 (merge of deliver/T2/Sheaf.AlgebraicGeometry.IsomorphicSingleTensorCounit)

## Repair of E2

The returned transport statement formerly asserted only `exists t, True`; it now asserts that every inverse component is the explicitly written composite of the selected derived adjunction unit, direct image of the pinned single tensor counit for e, and the single image of the underived tensor composition comparison. This uniquely determines the witness, so its selection is legitimate.

The returned equation formerly took an arbitrary natural isomorphism `t` as an argument. It now fixes `t` to the witness of the characterized transport theorem. The target proof uses this same witness and calls the equation without an arbitrary t argument. The equation's public statement needs a public import of the transport module. All three modules are original parts of this new-node delivery held by T2; no existing foreign module is adapted.
