## What changed

Replaced the hole in
`WeilConjectures.PurityFiniteSetting.OrdinaryDiagonal.realize_restriction`
by an explicit categorical pasting calculation, without changing its statement.
The private helpers derive comparison composition from the proved ordinary
comparison coherence and the source library's
`Functor.mapDerivedCategorySquareIso_hom_app_comp`. Naturality of the exact-to-derived
comparison converts that equation to the specified left-derived compositor.
The final calculation treats every ordinary local isomorphism, including the
unit conversion and both ordinary open compositors.

Added `Sheaf.Paper.OrderedTateExactOpenComposition`. Its definition
`AlgebraicGeometry.Etale.orderedTateExactPullback` is a concrete composite of
existing specified comparisons; it chooses no new data. Its one theorem isolates
the coefficient-only part of the original plan. The main module imports it,
`Sheaf.AlgebraicGeometry.ComparisonPullbackCoherence`, and the source library's
`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.RestrictScalars`
privately. Existing public imports and signatures are preserved.
The source compositor uses a generic equality-transport lemma, keeping the
geometric inclusion equality out of kernel reduction. The main proof compiled
in 22.4 seconds. The new coefficient module also compiled independently.

## Proved and sorry left

Original holes: one, `OrdinaryDiagonal.realize_restriction`.
Closed that hole by reduction to a strictly smaller coefficient identity.
Added one hole:
`AlgebraicGeometry.Etale.orderedTateExactOpenComposition`, node
`lem-pur-ordered-tate-exact-open-composition`.
There are no holes left in the item module, no holes in definitions, and one
hole in the new module. This is a decomposition (one hole closed, one added;
net zero), not a completed proof of the whole remaining mathematical input.

The new statement involves only ordinary pullback of the ordered Tate coefficient.
It has no dualizing object, comparison of sites, compactification, arbitrary
local isomorphism, realization map or gluing assumption. The site-comparison
and conjugation parts are proved in this delivery, rather than moved into it.
Its docstring supplies the induction, normalization and exact-to-derived
argument. Edge cases checked in formulating it are dimension zero, identical or
empty opens, zero coefficients, and N=0 (invertibility then forces an empty base).

## No longer needed

No existing import was removed and no module was withdrawn.
The original proof edge to
`lem-weil-pbc-proetale-derived-pullback-composition` is unnecessary: that node's
integral/ringed pullback setting is not needed for this fixed finite coefficient
comparison. The proved exact-square pasting theorem and the actual
`ProEtale.leftDerivedUpperStarComp` definition give the required composition law.

The original direct proof edges to `def-amb-vector-integration-charts` and
`def-asd-ordinary-finite-p1-arrows` move to the new coefficient lemma, where they
remain needed. The edge to `det-prop-sfb-cartesian-coefficients-twists` is removed:
the calculation uses the concrete normalized ordinary finite coefficient
transport, without the broader signed/integral Cartesian-twist interface.
These are local dependency changes; no claim is made that these declarations or
modules are globally unused. The unit's route is preserved.

## Where the brief, the DAG or earlier work was wrong

The original statement is unchanged and no false statement was found.
The planned generic pullback-composition dependency was broader than the actual
fixed-coefficient comparison needed here. The exact-square coherence already
proved in the adopted source library supplies that part directly.

## New nodes

`lem-pur-ordered-tate-exact-open-composition` is the ordinary coefficient
composition step from the combining/canonicity paragraph of the latest
blueprint's diagonal-dualizing proof. It records the normalized roots and line
calculation, tensor induction and exact derived compositor. Its module is
`Sheaf.Paper.OrderedTateExactOpenComposition`; its theorem is
`AlgebraicGeometry.Etale.orderedTateExactOpenComposition`.
No existing definition or statement changed, so no change record is required.

## Second reading by Q1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
