## What changed

Proved `AlgebraicGeometry.Etale.hasConstructibleHigherDirectImages_comp` with its
original signature. Implemented the prescribed four-step argument using the
proved source Leray spectral sequence, constructible kernel/cokernel/extension
closure, simultaneous induction on the pages, and descending induction on the
finite abutment filtration. Three proved private helpers express homology,
page propagation, and filtration descent. The final transport uses
`lowerStarComp`, functoriality of ordinary right derived functors, and
`Functor.homologyRightDerivedFunctorPlusObjSingleFunctorIso`.

Imported the recorded finite-value/finite-stalk constructibility comparison
privately, and `WeilConjectures.ConstructibleSheaf.OpenClosed` for constructibility
of the zero filtration step. Updated the item's DAG proof to describe these
identifications and added the existing comparison node to its proof dependencies.
No statement, definition, exported import or target changed. No other module
was adapted. The static checker requires a record for the added local `open` and
section `variable` commands; this is documented in
`coord/changes/B8-constructible-composition-private-proof-context.md`, including
all three unchanged downstream modules and their current holders.

The full proof compiled without diagnostics through `lcompile.py` in 28.5 seconds
before final comment/import cleanup. The delivery dry run checks the final file,
including every declaration's axioms. Edge cases are handled by the same proof:
degree zero has a one-step filtration; the empty scheme and the zero coefficient
ring require no exceptions; every filtration quotient uses a monomorphism and
its cokernel. No arbitrary-subobject closure or uniform dimension bound is used.

Searches: LeanFinder on spectral-sequence abutments in a Serre subcategory found
only general Serre-class declarations. Loogle on `"SpectralSequence", "AbutsTo"`
returned no hits. The msearch grep query found only a group-cohomology docstring.
Repository searches found the already-proved relative Leray sequence, the
finite-value comparison, and all three constructible closure clauses. Thus the
existing blueprint route can be implemented completely without new statements.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.Etale.hasConstructibleHigherDirectImages_comp`
(node `lem-finrepair-composition-c`).

Added zero holes; split off zero statements. There are no remaining `sorry`s
in any delivered Lean file. All three private helpers are proved.

## No longer needed

Removed `Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence`, a retired
re-export whose former duplicate theorem was already withdrawn. The proof uses
`WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.LeraySpectralSequence`
directly. This also avoids the retired wrapper's extra imports, including its
unused `Sheaf.CategoryTheory.Filtration` route. No planned mathematical dependency
was dropped: `def-finrepair-property-c`,
`lem-weil-pbc-grothendieck-spectral-sequence`, and `thm-constructible-serre`
are all used. No blueprint unit statement or step is bypassed; the unit's
`realized` lists are empty. No further node or module is claimed to leave the
target closure, since other importers may still need it.

## Where the brief, the DAG or earlier work was wrong

The planned mathematics was correct. The retired spectral-sequence wrapper no
longer declares the formerly planned theorem; the node now correctly records
the proved source declaration. Its abutment is expressed using the ordinary
right derived functor of the composite underived functor, whereas property C
uses homology of the bounded-below derived functor of the composite morphism.
The proof supplies both identifications explicitly. The page API is indexed
by natural-number bidegrees, and `pageInfinity (p,q)` is the page `p+q+2`, so
neither explicit negative-quadrant terms nor another stabilization theorem is
required. The recorded constructibility comparison is also needed to apply
the source closure lemmas to the predicate used by property C.

## Second reading by B8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
