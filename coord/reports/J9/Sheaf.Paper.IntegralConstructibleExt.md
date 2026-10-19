## What changed

Proved `AlgebraicGeometry.ProEtale.integralConstructibleExt` from the existing
`CondensedRing.integralExtHomContinuous` and `CondensedRing.integral_stratum_ext_bound`.
The continuity argument constructs the prime-characteristic instances from the finite-field
cardinality and packages X as an Over object. The bound argument transports coefficients,
applies the existing bound, and transfers vanishing through the induced derived equivalence,
its singleFunctor and shift comparisons, and injectivity on morphisms.

The new module `Sheaf.Paper.IntegralCoefficientExtComparison` proves
`AlgebraicGeometry.ProEtale.integralCoefficientExtComparison`. Its private helpers construct
the scalar ring equivalence and homeomorphism from uniqueness of the extending absolute
value, then construct the condensed-ring isomorphism by continuous postcomposition.
Restriction of scalars gives the additive equivalence. Finite biproduct and cokernel
comparisons transport the point's finite presentations; the existing coefficient-change
pullback comparisons transport local models, strata, and affine-local constructibility.
No existing signature, definition or visibility changes. New proof imports are non-public.

## Proved and sorry left

Original holes: 1. Closed: `AlgebraicGeometry.ProEtale.integralConstructibleExt`
(node `sk-lem-int-ext`). New holes: 0. Split off: 0.
The new `AlgebraicGeometry.ProEtale.integralCoefficientExtComparison`
(node `lem-integral-coefficient-ext-comparison`) and every private helper are proved.
Neither delivered Lean module contains a sorry.

The geometric dependency theorems retain their existing holes. The proof also uses the
existing DVR theorem's characterization of its uniquely determined integer subring.
No arbitrary data is selected from a mere existence assertion: the ring equivalence,
homeomorphism, sheaf isomorphism, and scalar equivalence are explicit constructions.
The delivery's compile and axiom checks are run by deliver3.py.

## No longer needed

Removed the retained, never-delivered `Sheaf.Paper.IntegralConstructibleExtBound` module
and its proposed `sk-lem-int-ext-bound-consequence` node from the sandbox. That split
repeated the bound conjunct; the proved coefficient comparison now permits application
of the actual existing geometric bound. Neither removed file exists in the current
shared repository, so no withdrawal is required.
No original proof-dependency module is pruned: IntegralStratumExtBound and
IntegralExtHomContinuity are both used, preserving the unit route. No original public
import was removed. No existing DAG dependency becomes unnecessary.

## Where the brief, the DAG or earlier work was wrong

The retained report said IntegralStratumExtBound was absent. It exists. Its coefficients
use a different construction and universe from this item's coefficients: passing E.val
directly fails. We lift E to the scheme universe and prove the comparison between the
embedded and spectral continuous coefficient rings. The retained comparison sorry has
now been proved, including preservation of constructibility, rather than delivered again.

The topological comparison must explicitly select the spectral metric: generic ULift
instances otherwise select the lifted embedded topology. The proof records the metric
instances explicitly and proves equality of distances before using continuity.

Edge cases: the comparison has no finite-field, finite-type, qcqs or nonempty hypothesis.
It preserves zero and torsion modules by the same finite-presentation argument. On a
non-qcqs scheme the proof handles every affine open. Empty stratifications and covers
are retained without adding assumptions. Integer Ext degrees, including negative ones,
are unchanged by the derived equivalence and shift comparison.

## New nodes

`lem-integral-coefficient-ext-comparison`, in the item's chapter and unit, records the
proved additive coefficient equivalence preserving finite constant models. It is a
coefficient comparison independent of geometric Ext vanishing. Its proof follows the
coefficient conventions of the blueprint, with the scalar norm comparison supplied by
Mathlib and the module comparisons supplied by the existing library. No change record
is required because all existing statements and definitions are unchanged.

## Second reading by J9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
