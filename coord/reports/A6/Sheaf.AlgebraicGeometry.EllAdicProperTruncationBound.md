## What changed

Proved `AlgebraicGeometry.ProEtale.CondensedRing.ellAdic_proper_lowerTail_bound` in
`Sheaf.AlgebraicGeometry.EllAdicProperTruncationBound`, with its signature and public imports
unchanged. There are no definition, statement or consumer changes.

The shorter source-library route uses the three existing
`properLowerStarHeartHypotheses_*` declarations from
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProperLowerStarEllAdic`.
They work on `constructibleCoproductClosure`, so no comparison between arbitrary finite
coefficient extensions and embedded intermediate fields, nor between the two constructibility
predicates, is needed. The hull's intersection universal property places its objects in the
corresponding homology property. This property is stable under good truncations.

For the integer heart bound d, choose c = d.toNat + 1. If a = q-c and L = tau<a K,
then L is at most a-1. The existing bounded dévissage theorem bounds every lower truncation's
image by a-1+d. The existing left-completeness Milnor theorem bounds the full image by
a-1+d+1, which is at most q-1. This deliberately coarse bound suffices because c is existential.
Zero complexes, empty fibres and negative d are covered by the same inequalities.

The item compiled cleanly through lcompile.py after preserving the original binders and
suppressing the theorem-local unused-section-variable linter. No bound or completeness
assumption was added. The ordinary pro-etale module categories' exact countable products and
the derived pushforward's right-adjoint/triangulated instances are the existing source ones.
The DAG now follows this proof; new records attach existing declarations, without adding Lean
modules or theorem aliases. The unit's proper-adjoint route is preserved.

## Proved and sorry left

Closed 1 of 1 holes:
`AlgebraicGeometry.ProEtale.CondensedRing.ellAdic_proper_lowerTail_bound`
(node `lem-sfb-adic-proper-truncation-bound`).

Added 0 holes. Split off 0 statements. The item has no remaining sorry.

The proof uses existing, still-sorried source inputs
`properLowerStarHeartHypotheses_continuousMapRingObj`,
`properLowerStarHeartHypotheses_padicIntegersRingObj`, and
`properLowerStarHeartHypotheses_padicAlgClRingObj` in namespace
`AlgebraicGeometry.ProEtale.CondensedRing`. They were already present in the library;
this delivery does not change them, add a replacement, or claim to prove them. New DAG
records identify these existing inputs explicitly. The bounded dévissage and generic
left-completeness steps are already proved in the source library.

## No longer needed

Removed these nine proof imports from the item:

- `Sheaf.AlgebraicGeometry.FiniteTypeFibreDimensionBound`
- `Sheaf.CategoryTheory.TruncationsAndHomotopyColimits`
- `Sheaf.CategoryTheory.Triangulated.LeftCompleteHeartUpperBound`
- `Sheaf.Paper.AmbientIndDerivedSums`
- `Sheaf.Paper.AmbientIndDerivedTriangulated`
- `Sheaf.Paper.IntegralConstructibleCompactness`
- `Sheaf.Paper.IntegralProperDirectSums`
- `Sheaf.Paper.ProperHeartBound`
- `Sheaf.Paper.ProperIndConstructibleUnbounded`

The corresponding old direct proof dependencies are removed:
`det-ambient-ind-derived-sums`, `det-ambient-ind-derived-triangulated`,
`det-prop-int-compactness-compact`, `det-prop-int-compactness-direct-sums`,
`det-proper-unbounded-window-arbitrary`, `lem-fin-finite-type-fibre-dimension-bound`,
`lem-sfb-left-complete-heart-upper-bound`, and `sk-lem-proper-heart-bound`.
The new source-heart nodes still cite the rational/integral geometric heart results as
underlying mathematical dependencies; this is not a claim that those geometric results
are globally unnecessary. The item needs neither the explicit geometric dimension bound
nor the sharp arbitrary-complex bound or eventual-stabilization argument.
`def-kun-truncations` and `def-sfb-bounded-constructible-localizing-closure` remain used.
No module is withdrawn, and global reachability/pruning remains for the maintainer to compute.

## Where the brief, the DAG or earlier work was wrong

The existing plan was valid but unnecessarily sharp for this existential statement.
A coarse Milnor bound costing one extra degree avoids proving eventual stabilization.
The source library already contains a Serre-class formulation of the three heart inputs,
with exactly the coefficient constructors of the certificate. The initial proof imports
pointed instead to specialized paper interfaces, making coefficient and constructibility
transport look necessary. No mathematical statement has been corrected or weakened.

## New nodes

`lem-sfb-proper-serre-heart-continuous`, `lem-sfb-proper-serre-heart-integral`, and
`lem-sfb-proper-serre-heart-qbar` attach the existing coefficient-specific
`properLowerStarHeartHypotheses_*` declarations. They state the separate heart-amplitude
and coproduct input on the weak Serre coproduct closure, rather than the target tail bound.
Their source is the proper heart-bound proof and integral direct-sum proof, as identified
in the upstream declarations. These are existing Lean inputs, with no new modules or holes.

`lem-sfb-bounded-heart-amplitude-devissage` attaches the already-proved
`DerivedCategory.isLE_obj_of_isLE_of_homologyProperty` from the source library, with the
finite-truncation induction written in its proof record. The already-existing
`lem-sfb-derived-left-complete-truncation-bound` supplies the coarse Milnor step.

Searches used LeanSearch, LeanFinder, Loogle, Mathlib/source grep, and the blueprint/DAG
index. No exact Mathlib result or existing node attachment for the four new records was
found. No change record is required: all Lean signatures, visibility and public imports
are unchanged, and no other Lean file is edited.

## Second reading by A6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
