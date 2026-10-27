## What changed

Implemented the finite and tower comparison assembly in
`Sheaf.Paper.CompositionComparisons`, retaining every existing public signature and definition.
The finite argument restricts the canonical direct-image maps to the full intrinsic Dctf
categories, uses the existing exceptional coefficient theorem for all three adjunctions,
and applies `finiteAdjointCompositorTransposes` to obtain the normalized exceptional
compositors, uniqueness, composite counits and right coefficient equation.

The tower argument uses the actual finite adjunctions supplied by the three `Pair.levels`
records. Its coefficient maps are the prescribed `coefficientMate` arrows: their counit
identities follow by the Hom equivalence, and naturality follows by injectivity of that
equivalence. The finite transpose theorem and its uniqueness identify its right compositors
with the published `finiteTheta`. Both finite identities are then passed to
`towerAdjointCompositorRealization`. The existing integral descent proof is retained.

Added two proof-only imports and two new statement modules for distinct, strictly smaller
left-adjoint steps: constructing the normalized finite support compositor, and proving its
single left coefficient equation. Neither new statement asserts an exceptional compositor,
right coefficient equation, tower realization or integral result. The parent DAG proof now
records this assembly and the exact remaining steps.

Validation: the two new statement modules compiled, and the final item compiled through
`lcompile.py` in 36.9 seconds. Existing public theorem signatures and the integral theorem
body were checked against the shared source and are unchanged.

## Proved and sorry left

Original holes: 2. Closed in the item:

- `AlgebraicGeometry.ProEtale.compositionComparisons_finite`.
- `AlgebraicGeometry.ProEtale.compositionComparisons_towers`.

No sorry remains in the item. Added holes:

- `AlgebraicGeometry.ProEtale.finiteSupportCompositor_exists`
  (`lem-sp-finite-support-compositor-existence`).
- `AlgebraicGeometry.ProEtale.finiteSupportCompositor_coefficient`
  (`lem-sp-finite-support-compositor-coefficient`).

This is a decomposition of two upper holes into two proper shared left-adjoint steps,
not two fully closed proofs. All private helpers have complete proofs. The already proved
`compositionComparisons_integral` is retained.

## No longer needed

No modules withdrawn and no public imports removed. The original etale-origin, tensor
pullback, exact comparison, site comparison, compact-site coherence and etale/pro-etale
coefficient dependencies now occur in the two smaller nodes rather than as direct proof
steps of the parent. They are still mathematically needed, so no global pruning is claimed.
The original separate `sk-prop-sf-rf-shriek-preservation` direct proof step is subsumed by
`reductionExceptional_isIso`, which supplies the needed actual restricted adjunctions.
`det-sp-scalar-extension-functor` is likewise used through that theorem's scalar closure
outputs. These declarations and their modules remain in the library.

## Where the brief, the DAG or earlier work was wrong

The existing plan's supplied declarations state the geometric site and coefficient
identities in other coordinates. They do not directly supply a natural compositor of
the intrinsic full subcategories, nor its coefficient identity for any normalized input
data. Those are the two explicit remaining coordinate-transport steps.

The finite result alone does not directly supply the tower identities: tower finite
adjunctions are specified by `Pair.levels`, whereas a finite existence result may choose
other right adjoints. This implementation keeps the specified level adjunctions, proves
the coefficientMate counit equations, and uses uniqueness to obtain exactly `finiteTheta`.

Edge cases checked in the statements and argument: zero coefficient rings and empty
schemes do not require cancellation of elements or nonzero objects; all cancellations
are by isomorphisms or bijective Hom equivalences. Quotient level n is exponent n+1,
so the torsion witness is positive even at n=0. The proof takes every m<=n, including
m=n. No flatness or finite projective dimension assumption is added.

## New nodes

`lem-sp-finite-support-compositor-existence` in
`Sheaf.Paper.FiniteSupportCompositorExistence`: only existence and etale normalization
of the left support compositor, for three given support restrictions. Its normalization
determines it uniquely through etale origin and full faithfulness. It is used for both
finite rings and for the fixed tower level adjunctions.

`lem-sp-finite-support-compositor-coefficient` in
`Sheaf.Paper.FiniteSupportCompositorCoefficient`: only the left coefficient equation
for given normalized data, obtained from the existing etale/pro-etale composition theorem
by finite origin and site transport. It is used for both finite and tower coefficients.

Both modules carry their sources and complete natural-language proof plans, with separate
DAG nodes and actual LeanSearch, Loogle and Mathlib grep search records. No definitions or
existing statements change, so there is no change record or forced adaptation.

## Second reading by Y5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
