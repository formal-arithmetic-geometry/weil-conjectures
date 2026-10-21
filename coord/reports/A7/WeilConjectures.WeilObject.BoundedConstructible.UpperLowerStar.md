## What changed

Filled `AlgebraicGeometry.ProEtale.CondensedRing.isIso_boundedConstructibleBaseChange_of_isIso`.
The inverse of pullback along an isomorphism is pullback along its inverse, using the existing
bounded-constructible identity and composition comparisons. The proved library theorem
`CategoryTheory.isIso_mateEquiv_of_isEquivalence_of_fullyFaithful` then makes the base-change
mate invertible. A proved private helper identifies `Adjunction.exchangeRight` with Mathlib's
mate transformation. Added only the two private proof imports needed for these steps; all
existing public imports, signatures, definitions, attributes and docstrings are preserved.

## Proved and sorry left

Closed one hole:
`AlgebraicGeometry.ProEtale.CondensedRing.isIso_boundedConstructibleBaseChange_of_isIso`.
Added zero holes, split off zero statements; zero `sorry` remain in the item.
Both private helpers have complete proofs. The mate theorem imported from
`Sheaf.CategoryTheory.MateIsoAlongEquivalences` is already proved.

## No longer needed

None. Both original public imports remain necessary for the existing statements and definitions.
Both new private imports are used. No module or DAG dependency is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The module docstring's assertion that the bounded-constructible pullback identity comparison
is unavailable is stale: `boundedConstructibleUpperStarId` is now defined and proved in
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructiblePullback`.
The repository contains no DAG node attached to this item module or its holed declaration
(searches by module name and declaration name), so there is no existing node proof to update.
The generic mate theorem used has node `lem-weil-mate-iso-along-equivalences`.
The rework row records an earlier cluster-restore revert; the current source and quarantine
preserve the same declaration. This delivery fills its proof without withdrawing either.

Searches used LeanFinder (mate invertibility), Loogle (`CategoryTheory.mateEquiv`), the launcher's
grep search, and repository/Mathlib ripgrep. Mathlib supplies the mates correspondence and the
quasi-inverse criterion `Functor.IsEquivalence.mk'`; the exact invertibility result is already
proved in the project's `Sheaf` library. The proof needs no properness or cartesian assumption.

## Second reading by A7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
