## What changed

Proved `CategoryTheory.exists_signedFibre_triangulated` with its original signature and
coordinate conventions. Its proof imports `SignedFibreCone` and `ConeFunctorDescent`
privately. All eight steps of the original DAG argument are implemented.

Four new, fully proved helper modules construct the signed complex and homotopies,
the coherent comparisons with every integer shift, the signed cone interchange,
and the general descent to homotopy categories. The objects, maps, homotopies,
component inverses and quotient lift are actual constructions. No data are chosen
from an unproved existence statement. The original node now records these dependencies.

Validation: all five modules compile without warnings. The main theorem's axiom
check lists exactly `propext`, `Classical.choice`, and `Quot.sound`. The coordinate
calculations cover zero complexes, zero functors, `r = 0`, `f = 0`, and `f = id`
without additional hypotheses. Boundedness uses the actual quotient lift's object
equality, preserving Mathlib's strict underlying-complex property `plus`.

## Proved and sorry left

Closed the single original hole in `CategoryTheory.exists_signedFibre_triangulated`
(node `lem-amb-signed-fibre-triangulated`). Proved 1 of 1 original sorries;
0 sorries added, 0 split off, 0 remaining in the five delivered Lean modules.
This is a proof, not a decomposition into unproved lower statements.

The helper declarations include `SignedFibre.d_sq`, `SignedFibre.homotopy`,
`SignedFibre.obj_isStrictlyGE`, `SignedFibre.commShift`, `SignedFibre.coneIso`,
its projection/naturality/inclusion/boundary identities, and
`CategoryTheory.exists_coneFunctor_descent` (all under `CategoryTheory`).

## No longer needed

No existing DAG node or library module is pruned. The original dependencies on
abelian categories, complexes, shifts, and the homotopy-category triangulation
remain needed through the new proved nodes. No original public import is removed.

During helper cleanup, the unused `DerivedCategory.Basic` import was removed from
`ConeFunctorDescent`; `SignedFibreComplex` uses `CochainComplexPlus` instead of the
broader `HomotopyCategory.Plus`. The cone helper imports the cone-triangle API
explicitly. Unused draft coordinate-wrapper lemmas were removed before delivery.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement correction was needed. The eight-step plan was correct.
Its shift-one calculation also requires coherent comparisons for every integer
to instantiate Mathlib's `CommShift ℤ`; the shift helper proves these using
`Int.negOnePow_add`. The descent must retain equality on quotient objects because
`HomotopyCategory.plus` is not invariant under arbitrary isomorphisms.

No existing definition or statement was changed, and no forced adaptation or
change record is needed.

## New nodes

`lem-amb-signed-fibre-complex`: `SignedFibreComplex.lean`, an explicit additive
signed complex construction with its homotopies and preservation of strict bounds.

`lem-amb-signed-fibre-shift`: `SignedFibreShift.lean`, explicit natural chain
isomorphisms and their integer shift coherence.

`lem-amb-signed-fibre-cone`: `SignedFibreCone.lean`, the signed four-coordinate
interchange, its inverse, chain-map equation, naturality, inclusion and boundary.

`lem-amb-cone-functor-descent`: `ConeFunctorDescent.lean`, quotient descent,
triangulatedness from cone preservation, and strict boundedness preservation.

All four nodes are proved in this delivery. They refine the item's existing route
within its unit; the unit statement and realized steps are unchanged.

## Second reading by J2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
