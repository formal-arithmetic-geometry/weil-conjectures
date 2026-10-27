## What changed

Filled the proof of
`WeilConjectures.PurityFiniteSetting.DiagonalPasting.doubleDiagonalSectionIdentifications`
in `Sheaf.Paper.DoubleDiagonalSectionIdentifications`, preserving every existing
statement and definition. Added proved private helpers for the unit specialization
of the horizontal smooth exceptional pasting clause and for the two derived
pullback section-composition calculations. The proof explicitly establishes all
finite-type, quasi-compact, separated and structural-map hypotheses used in the
two pasting applications. The third restriction equation is definitional. The complete module compiled through
`lcompile.py` in 43.9 seconds and through the delivery probe in 40.3 seconds.
The first delivery stopped on an inherited unused simp argument; that argument
was removed before rerunning delivery.

The horizontal pasting input is the same-unit sibling
`Sheaf.Paper.SmoothExceptionalTensorPasting`. Its equality in pro-etale coordinates
is reflected to etale coordinates on the bounded-below exceptional image of the
pulled-back unit; the resulting beta identities are pulled along the indicated
sections and mapped back to the specified pro-etale comparison. No orientation
or Tate isomorphism is chosen. All added imports are private proof imports:
`Sheaf.Paper.SmoothExceptionalTensorPasting`,
`WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionMonoidal`,
`WeilConjectures.SixFunctors.Etale.Derived.WeilComplexDual`, and
`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.HomComparison`.
The section-composition helpers work over a general coefficient category to avoid
repeated elaboration of the concrete module-category instances. Updated the node proof and dependency list
to record the bounded-below comparison reflection and pullback unit coherence
used to implement its existing horizontal-pasting route; no statement or unit route changed.

## Proved and sorry left

Closed the one original hole:
`WeilConjectures.PurityFiniteSetting.DiagonalPasting.doubleDiagonalSectionIdentifications`
(blueprint: `lem-pur-double-diagonal-section-identifications`).

No holes added; no `sorry` remains in this module. The existing proofs of
`doubleDiagonalGeometry` and `doubleDiagonalProperties` are retained, apart from
removing one unused simp argument reported by the delivery probe. The proof
uses the stated horizontal pasting theorem as a dependency, as required by the
DAG; dependencies that remain unproved elsewhere are not new holes in this delivery.

## No longer needed

None. The proof retains the reviewed geometric and horizontal-pasting route.
There are no withdrawn modules or nodes, and no removed public imports.

## Where the brief, the DAG or earlier work was wrong

None. The two nontrivial restrictions require the explicit canonical pullback
composition and unit comparisons in addition to the beta identities written
without these comparisons in the mathematical shorthand. The proof includes
these comparisons and checks the bounded-below hypothesis before reflecting
an equality through the site-comparison functor.

## Second reading by H6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
