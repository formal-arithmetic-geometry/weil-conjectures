## What changed

Replaced the hole in
`WeilConjectures.IntegralVerdier.finiteIntrinsicBidualComparison` with a categorical
construction and proof, keeping its signature and existing docstring unchanged.
Private helpers construct the closed comparison by transposing realized evaluation,
prove it is invertible using Hom-set bijections and essential surjectivity, and prove
the biduality equation by inverse transposition. The comparisons are constructed at
the arbitrary input isomorphism directly, so the supplied first-input evaluation
naturality `he` is not needed.

Added `Sheaf.SixFunctors.FiniteIntrinsicTensorRealization`: restrict the existing
intrinsic tensor presentation to termwise flat K-flat representatives, apply the
already constructed `finiteScalarTensorRealization`, invert its components, and
uncurry. All data and naturality proofs are constructed in Lean.

Added `Sheaf.SixFunctors.FiniteIntrinsicTensorSymmetry`, containing only the signed
interchange equation for that constructed tensor comparison. The item imports this
module privately. Updated the item's proof plan and added nodes for the construction
and the remaining signed equation.

The generic categorical argument is specialized through abstract coefficient data.
This keeps the concrete derived constructions out of repeated kernel conversions;
all transparency changes in the item are local. The complete item compiles in
32.1 seconds, and both new modules compile within 15 seconds each.

## Proved and sorry left

This is a decomposition, not a net decrease of holes: one upper hole closed and one
strictly smaller hole added.

Closed the original hole in
`WeilConjectures.IntegralVerdier.finiteIntrinsicBidualComparison`.
Its categorical Hom-comparison, invertibility and bidual-transpose argument is complete.

The only new remaining hole is
`WeilConjectures.IntegralVerdier.finiteIntrinsicTensorSymmetry`
(`lem-sf-finite-intrinsic-tensor-symmetry`). It asserts an equation for an already
constructed tensor comparison; it has no internal-Hom comparison, evaluation,
double dual, dualizing input or biduality conclusion. Its docstring gives the
representative normalization, homogeneous signed-generator calculation and
fully faithful restriction argument needed to prove it.

`finiteIntrinsicTensorModel` and `finiteIntrinsicTensorRealization` have zero holes.
No hole is placed in a definition or private helper.

## No longer needed

No existing module or declaration is withdrawn. The original public import is
preserved; no original import is removed.

The item's direct proof dependencies on
`lem-exc-intrinsic-realization-tensor-complex` and
`lem-sf-ringed-derived-closed-symmetric-monoidal` are replaced by the existing
normalized finite scalar tensor realization and its signed compatibility step.
The categorical argument uses the supplied adjunctions directly, rather than
constructing an intrinsic monoidal structure or comparing K-injective Hom models.
These shared nodes may still be needed by other consumers; no global pruning of
their modules is claimed.

## Where the brief, the DAG or earlier work was wrong

The current server queue assigns the one-hole proof route, not a zero-hole repair.
There was no current rework/return row for this item. The historical build-error
file reports a bad import in `IntegralVerdierModels`; the original item compiled
against the published dependency artifacts.

The existing `finiteScalarTensorRealization` already supplies the tensor isomorphism
planned in the original node; reconstructing it would duplicate work. The remaining
normalization issue is only its signed swap equation.

The signed representative formula alone does not assert naturality away from
representatives. The new signed compatibility theorem therefore retains the
original theorem's exact two-input symmetry naturality hypothesis `hs`. The
zero-object, zero-ring and empty-site cases do not require additional hypotheses.
The unit route and all target statements are preserved.

## New nodes

`def-sf-finite-intrinsic-tensor-realization` records the constructed restriction of
the tensor model and the uncurried inverse scalar tensor isomorphism. It uses
existing normalized data and has no proof hole.

`lem-sf-finite-intrinsic-tensor-symmetry` records only the signed interchange square
for that specified isomorphism, with the original symmetry naturality hypothesis.
It is the tensor/symmetry part of original proof steps 1–2, strictly before the
Hom-set-bijection and biduality arguments now completed in the item. The ordinary
tensor comparison, total comparison, representative normalization and resolving
restriction it needs already have Lean declarations.

## Related modules compiled before delivery

2 related module(s) compiled against this delivery by deliver3.py: 2 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.SixFunctors.FiniteIntrinsicBidualComparison": "1771fe5d0709a59c10696374c8a352f48fc54400", "Sheaf.SixFunctors.FiniteIntrinsicTensorRealization": "f4db51c21f31afade083f7064add106c4b195f31", "Sheaf.SixFunctors.FiniteIntrinsicTensorSymmetry": "77064c20536e12b75c6e3ddce7b07eb388c2e979"}, "results": {"Sheaf.Paper.FiniteIntrinsicProjectionRealization": {"hash": "183faf7f2d752f235aed814f1e607ee3f14b03aa", "status": "OK"}, "Sheaf.SixFunctors.FiniteIntrinsicVerdierBiduality": {"hash": "ca4e9d4a6bb7b41c2bb4b29b971ac5dda95e1da7", "status": "OK"}}, "seconds": 35, "time": "2026-10-28T07:24:13+0800", "transitive": 1, "version": 1}
```

## Second reading by V1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
