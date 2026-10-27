## What changed

Added `Sheaf.Paper.NativeWeilHomClosedStructure`, whose named theorem isolates the
action-site construction of a `CoefficientClosedStructure` on `M.weilHom`. Updated
`Sheaf.Paper.NativeWeilHomRightAdjoint` to import that theorem and obtain the target
right-adjoint instance from the closed structure's adjunction field. Updated the
item node proof and proof dependencies to record this route.

## Proved and sorry left

The target theorem `AlgebraicGeometry.ProEtaleWeilSheaf.native_weil_hom_isRightAdjoint`
is proved by applying `(S.adjunction K).isRightAdjoint` after obtaining the closed
structure `S`. One new proof obligation remains as the named theorem
`AlgebraicGeometry.ProEtaleWeilSheaf.native_weil_hom_closed_structure` in node
`lem-sf-native-weil-hom-closed-structure`; it is the action-site tensor--Hom
construction and is left as `sorry` for a subsequent worker.

## No longer needed

The target proof uses only the new closed-structure node. The four original proof
nodes `lem-sf-weil-frobenius-action-resolutions`,
`lem-weil-pbc-site-derived-tensor-descent`, `lem-sf-ringed-derived-tensor-hom-adjunction`,
and `lem-sf-ringed-forget-two-injective-hom` are no longer direct dependencies of this
module and are pruned from its proof route. No imported module was removed from the
new proof beyond those absent from the item source.

## Where the brief, the DAG or earlier work was wrong

The original proof plan required the full action-site construction but supplied no
Lean declaration packaging its resulting native closed structure. The new node makes
that missing construction explicit; the target then follows from the standard
`CoefficientClosedStructure.adjunction` interface.

## New nodes

`lem-sf-native-weil-hom-closed-structure`: the action-site tensor--Hom construction
of a closed structure on `M.weilHom`; source module
`lean/Sheaf/Paper/NativeWeilHomClosedStructure.lean`.

## Second reading by E5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
