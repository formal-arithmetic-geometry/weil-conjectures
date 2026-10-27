## What changed

Proved `AlgebraicGeometry.ProEtale.torsionCd_bounded_serre_coimage` with its existing
signature unchanged. The proof privately imports
`Sheaf.Paper.TorsionCdCriticalCoimageSurjectivity` and applies its existing theorem
at the larger natural dimension bound `e = (q - 2).toNat`. Since `q > d+2`, we have
`d ≤ e` and `e+2=q`. Both the geometric dimension hypothesis and the input
cohomology bounds remain valid with `e` in place of `d`. The resulting epimorphism
onto degree-q coimage cohomology has zero source by `hMb`, so Mathlib's
`CategoryTheory.Limits.IsZero.of_epi` proves the conclusion.

Updated the item's DAG proof, proof dependencies and proof origin to this argument.
No definition, statement, public import, source-library declaration or unit route changes.

## Proved and sorry left

Closed the one original direct hole in
`AlgebraicGeometry.ProEtale.torsionCd_bounded_serre_coimage`
(`lem-sfb-torsion-cd-bounded-serre-coimage`). Zero holes remain in the item; zero
holes are added and zero statements split off. This is a complete proof from an
existing declared dependency, whose own hole remains outside this delivery:
`AlgebraicGeometry.ProEtale.torsionCd_critical_coimage_surjectivity`
(`lem-sfb-torsion-cd-critical-coimage-surjectivity`). Thus the geometric critical
surjectivity obligation is still open; the two residual obligations of the earlier
kernel split are not independent.

## No longer needed

Removed the item's direct proof import of
`WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.HomologySequence`:
the proof uses no long exact sequence. That API remains available to the critical
surjectivity module and other consumers.

The item's former direct planned dependencies
`lem-sfb-finite-discrete-serre-heart-cd` (`Sheaf.Paper.FiniteDiscreteSerreHeartCd`) and
`lem-sfb-condensed-sections-ind-vanishing` (`Sheaf.Paper.CondensedSectionsIndVanishing`)
are not needed directly by this proof. They remain dependencies of critical
surjectivity, so no claim of global pruning or module withdrawal is made. No
unused proof imports were added. All existing public imports remain needed by the
unchanged statement. The unit statement and steps are preserved.

## Where the brief, the DAG or earlier work was wrong

The earlier split's critical-surjectivity docstring says it gives no bound in
higher degrees. At a fixed dimension parameter it only concerns that critical
degree, but its universal quantification over the parameter lets one raise the
bound and obtain every strict higher-degree vanishing by the present argument.
The original direct geometric coimage comparison is therefore unnecessary as a
separate proof task. The critical-surjectivity declaration and node have no import
or DAG dependency back on this item; both directions were checked before using it.

No claim of a geometric proof of critical surjectivity is made. No finite-heart
presentation or completeness hypothesis is introduced. The smallest admissible
integer degree is `q=d+3`, giving `e=d+1`; larger degrees give still larger valid
bounds. Zero maps, isomorphisms, zero modules and empty schemes are covered without
case distinctions by the existing surjectivity statement and the zero-object lemma.
Mathlib searches (LeanFinder, Loogle and grep through `msearch.py`) identified
`IsZero.of_epi` as the required categorical step. No new nodes or change records
are needed.

## Second reading by C1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
