## What changed

Proved the sole theorem in `Sheaf.AlgebraicGeometry.ProperTorsionProjectionFormula`
by reusing `AlgebraicGeometry.Etale.isIso_rightDerivedLowerStarProjectionMap_of_isProper`
from `WeilConjectures.SixFunctors.Etale.Derived.Kunneth.ProperProjectionFormula`.
That existing theorem proves invertibility of the entire canonical bifunctor
transformation for precisely the same torsion commutative ring and proper morphism.
The new proof supplies its instance and takes the two components at E and K.
The signature, coefficient universes, canonical map, definitions and public imports
are unchanged. The replacement proof import is private. No consumer adaptation or
change record is needed. The import-direction check reports no cycle.

The source theorem already implements the planned geometric-fibre route: proper
base change, finite cohomological dimension on the fibre, the constant-complex
projection formula over a separably closed field, and geometric-point detection of
isomorphisms. The DAG retains these inputs, records the direct source equivalence
at the point and the final component specialization, and removes the two auxiliary
indirect point-identification dependencies. No unit statement or route is bypassed.

The assigned file compiled cleanly with lcompile.py (exit 0, 3.7 seconds).
Lean elaboration checks the precise canonical map, including all coefficient-category
instances. Reuse applies also to the zero ring, empty source or base, and arbitrary
unbounded complexes because it adds no hypotheses.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.Etale.isIso_rightDerivedLowerStarProjectionMap_app_app_of_isProper_of_isAddTorsion`
(node `lem-kun-0f0g`).

Zero holes remain in the delivered module. Zero holes added; zero split off.
This closes the assigned proof from the existing library; it makes no claim that
all imported foundational theorems are sorry-free. No other module is changed.

## No longer needed

Removed these seven direct proof imports:

- `Sheaf.AlgebraicGeometry.Sites.FiniteTorsionEtaleCohomologicalDimension`
- `Sheaf.AlgebraicGeometry.GeometricStalkAsPullback`
- `Sheaf.AlgebraicGeometry.AbelianSheavesGModules`
- `Sheaf.AlgebraicGeometry.ProperUnboundedBaseChange`
- `WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comparison`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint`
- `WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjectionBaseChange`

The source proof supplies the dimension, base-change, monoidal-comparison and
stalk-conservativity inputs transitively; these mathematical inputs are retained,
and their modules are not claimed globally unreachable.

`lem-kun-stalk-as-pullback` and `lem-exc-abelian-sheaves-gmodules` are no longer
needed by this route: the source has the direct constant module-sheaf equivalence
at a separably closed point. Their modules
`Sheaf.AlgebraicGeometry.GeometricStalkAsPullback` and
`Sheaf.AlgebraicGeometry.AbelianSheavesGModules` are no longer direct imports.
Removed the obsolete `lem-exc-abelian-sheaves-gmodules` tool approval from this
node. No module is withdrawn and no global reachability claim is made.

## Where the brief, the DAG or earlier work was wrong

The assigned statement was already proved, in the stronger bifunctorial form,
in the source library's `Kunneth.ProperProjectionFormula` module. The original
DAG/import plan did not identify this exact reuse. Its indirect construction
through abelian Galois-module sheaves is unnecessary. The existing direct
module-sheaf equivalence and full projection theorem cover arbitrary torsion
rings, not merely finite rings. Mathlib searches (LeanFinder, Loogle and grep)
returned no matching projection theorem; source-library search found the exact
result. No mathematical statement correction was necessary.

## Second reading by N2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
