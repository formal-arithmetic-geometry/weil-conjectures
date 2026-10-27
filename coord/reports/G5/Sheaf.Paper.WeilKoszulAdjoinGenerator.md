## What changed

Constructed the head and tail inclusions and exterior wedge multiplication explicitly in
`Sheaf.Paper.WeilKoszulJoinGraded`. The multiplication on the extended graded modules
uses the coproduct universal property of the total tensor; no data is chosen from an
unproved existence statement.

In `Sheaf.Paper.WeilKoszulAdjoinGenerator`, private helpers prove that this multiplication
commutes with the diagonal power transitions and sends the tensor of the two exterior
units to the exterior unit. Then the local contraction equation is assembled
into a chain map, degreewise bijectivity makes that map invertible, and inversion gives
the original theorem with its unchanged statement and both compatibility equations.

Validation: all four modules compiled through `lcompile.py`; the final item compile took
14.0 seconds. The original theorem signature was compared verbatim, the existing node
changes only its proof fields, every named node dependency exists, and Lean lines are
at most 100 characters. The delivery tool runs the final packet checks.

## Proved and sorry left

Closed the original hole in `AlgebraicGeometry.Scheme.koszulAdjoinGenerator`
(`lem-weil-pbc-koszul-adjoin-generator`) by decomposition. The delivery adds two holes:

- `AlgebraicGeometry.Scheme.koszulJoinGraded_bijective`
  (`lem-weil-pbc-koszul-join-graded-bijective`): bijectivity of the explicitly defined
  graded map, independent of coefficients, differentials, transitions, and units.
- `AlgebraicGeometry.Scheme.koszulJoinSummand_leibniz`
  (`lem-weil-pbc-koszul-join-summand-leibniz`): the local contraction equation on one
  tensor summand, with neither invertibility nor transition or unit assertions.

The original module has zero holes; the added modules have two in total. This is a
one-to-two decomposition, not a net reduction of the sorry count. The transition and
unit calculations and the assembly/inversion argument have complete Lean proofs.

## No longer needed

No original imports are removed and no module is withdrawn. The exterior-basis and
Koszul-differential nodes cease to be immediate proof dependencies of the item; they
remain needed by the two smaller coordinate statements. They are not globally pruned.
The proved source modules on final-generator cone coordinates were examined but are
not imported: they do not provide the required first-generator cochain tensor map or
its strict transition and unit equations.

## Where the brief, the DAG or earlier work was wrong

The stated dependency declarations provide exterior bases and contraction, but no
ready-made head-tail map into Mathlib's extended total tensor. The new construction
makes that map explicit. Its types retain the actual coefficients and power index to
avoid expensive definitional identifications with complexes having other coefficients.
The two remaining statements isolate respectively its
underlying graded bijectivity and its local differential equation, instead of asserting
another existence of a compatible family of complex isomorphisms.

Edge cases were checked in the natural-language arguments: the zero ring, empty tail,
exterior degree zero, degrees above the rank, positive cochain degrees, arbitrary
characteristic, and vanishing or invertible coefficients. No hypotheses or conclusions
of the original statement change, and no unit-level route changes.

## New nodes

`def-weil-pbc-koszul-join-graded` records the real multiplication construction, including
extension by zero and the total coproduct. The item proves its transition and unit
equations with private helpers.

`lem-weil-pbc-koszul-join-graded-bijective` isolates the coefficient-independent partition
of exterior bases. `lem-weil-pbc-koszul-join-summand-leibniz` isolates the contraction
formula on a single tensor summand. Both have complete proof descriptions in their
nodes and declaration docstrings, and each is strictly a part of the original argument.
They do not assert the original existential statement, repackage its hypotheses, or
include its compatibility assertions. No change record is needed because existing
statements and definitions are unchanged.

### Not duplicates

The three new nodes use the same source as the item, but state different parts of its
argument. The definition node supplies actual maps, the bijectivity node is a statement
only about graded modules, and the local Leibniz node is a differential equation on one
summand. None asserts a family of isomorphisms with transition and unit compatibility.
`tools/blueprint_refs.py search 'exterior multiplication'` and the search for
`'Koszul tensor'` returned zero blueprint nodes; searches of current Lean declarations
found no name clashes. The source's final-generator assembly is a different map with
different source and target; it does not supply the total coproduct or the cochain
Leibniz equation stated here.

## Second reading by G5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
