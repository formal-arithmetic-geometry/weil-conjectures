## What changed

Proved `AlgebraicGeometry.locallyClosedStratum_separated_finiteType` in the assigned
module, with its statement and all binders unchanged. The proof establishes local
Noetherianity of `T`, calculates the stratum image with Mathlib's vanishing-ideal
support API, composes the immersion/separated/locally-finite-type/quasi-compact
instances, and uses uniqueness of initial objects for the empty case.

Replaced the public `Proper` import by `Morphisms.Separated` and the public
`WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme` import by
`Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme`. All constructions in the
statement are already Mathlib constructions. Kept `Noetherian` as a private proof
import and removed five unused proof imports. Updated the theorem proof description
and the existing node's proof, proof dependencies and origin to match the proof.
Removed its obsolete top-level tool approval for the stronger reduced-subscheme theorem.

There are zero current Lean downstream modules (`tools/downstream.py` and a
source search), so the reduced public import surface requires no consumer adaptations.
The item's DAG attachment and statement dependencies remain intact; its unfinished
parents still need this theorem. The blueprint unit and its route are unchanged.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.locallyClosedStratum_separated_finiteType`
(node `lem-dl-a1-locally-closed-stratum-separated-finite-type`).
Added 0 holes; split off 0 theorems; no `sorry` remains in the delivery.

The final file compiles without warnings through `lcompile.py`. A `#print axioms`
check in the defining file reports only `propext`, `Classical.choice` and
`Quot.sound`; the temporary command was then removed. The proof uses Mathlib only.
Edge cases are covered by the uniform argument: empty S (with the explicit
isomorphism), S equal to the whole space, arbitrary containing open U, and
nonreduced T. Local Noetherianity, rather than global compactness, makes the
arbitrary open inclusion quasi-compact. The supplied locally-closed hypothesis
is redundant once a containing open and its closed inverse image are specified;
it is kept verbatim, with the unused-variable linter disabled for this declaration.

## No longer needed

Removed imports:

- `WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme`: the image and
  closed immersion are properties of the existing Mathlib construction. Replaced
  with `Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme`.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: separated composition suffices;
  replaced with `Mathlib.AlgebraicGeometry.Morphisms.Separated`.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`.
- `Mathlib.AlgebraicGeometry.Morphisms.Integral`.
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`.
- `Mathlib.AlgebraicGeometry.AffineScheme`.
- `Mathlib.RingTheory.Noetherian.Defs` (already supplied by `Noetherian`).

Removed proof dependencies:

- `lem-weil-pbc-reduced-induced-closed-subscheme`: the stronger project theorem is
  unused; Mathlib computes the vanishing-ideal subscheme's range directly. The
  statement dependency is retained because it describes the construction.
- `lem-weil-pbc-affine-scheme-qcqs`: only local Noetherianity is needed.
- `lem-weil-pbc-finite-type-over-noetherian`: its global compactness conclusion is
  unnecessary; use the local permanence API already recorded on `pqf-def-locnoeth`.
- `lem-weil-pbc-finite-over-separated-finite-type`: compose the closed and open
  immersion properties directly instead of routing through this finite theorem.

No modules are withdrawn and no upstream declaration is removed or modified.
The removed dependency edge to the project reduced-subscheme module does not
claim that module is globally unused; other consumers and DAG statements may
still need it.

## Where the brief, the DAG or earlier work was wrong

No false statement or broken tool was found. The planned argument was longer
than necessary: global Noetherianity, affine compactness and the finite-morphism
wrapper are unnecessary. The statement already chooses the genuine Mathlib
vanishing-ideal subscheme, whose immersion and range properties are proved there.
No new node, statement repair, definition repair or forced adaptation was needed.

## Second reading by A5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
