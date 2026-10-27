## What changed

Proved both declarations in `Sheaf.CategoryTheory.SequenceAdjunctionCochainTransposes`,
with their signatures unchanged. The sequence unit and counit follow by choosing the
ordinary cochain transpose and inverse transpose in the existing normalized sequence
adjunction. The scalar proof transports the existing coefficient adjunction to the
specified cochain model through uniqueness of its universal left derived pair, then
uses its normalized unit and naturality of exact restriction. Private proved helpers
repeat the full/essentially-surjective Kan comparison already used in
`DerivedChangeOfRingsCochainModel`; a private tensor-at-one equation handles sections.
Updated the node proof and dependencies to match these arguments.
The source was checked against the adjunction and representative compatibility
arguments in `sites-cohomology.tex`, Tags 07A6 and 0FPI.
LeanFinder, Loogle, the prescribed grep search, and local source searches found
the existing adjunction, transport, and homotopy-quotient unit APIs used here.

## Proved and sorry left

Closed 2 of 2 holes:
- `SheafOfModules.SequenceProjection.adjunctionCochainTransposes`.
- `SheafOfModules.SequenceProjection.scalarCochainTranspose`.

Both belong to `lem-coef-sequence-adjunction-cochain-transposes`.
No holes remain in this module; no holes were added or split off.
The complete module compiled cleanly through `lcompile.py`,
with no errors or warnings. Both public theorem signatures were compared with
the repository source and are unchanged; all Lean lines are at most 100 characters.

## No longer needed

Removed the proof imports `Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition`
and `Sheaf.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction`.
The dependency node `lem-weil-pbc-ringed-topoi-derived-pushforward-composition` is
unnecessary here (its obsolete `tool_uses` approval is also withdrawn): the sequence projection theorem already supplies the K-injective
comparison, and the unit/counit equations are formal consequences of its normalized
Hom identity. No direct use of `lem-pur-sheaf-ring-coefficient-ordinary-adjunction`
is needed: its ordinary adjunction and section formula are included in
`lem-pur-sheaf-ring-derived-coefficient-adjunction`. These dependencies may still be
needed elsewhere; no module is withdrawn. Added the private proof import
`Mathlib.CategoryTheory.Limits.Final` for the full homotopy quotient comparison.

## Where the brief, the DAG or earlier work was wrong

The original mathematical statements need no repair. The sequence proof need not
construct new cones, strict maps, or invoke a separate direct-image convention:
the existing ordinary and derived adjunction declarations already encode them.
The scalar interface is on homotopy categories whereas the assigned model is on
cochain complexes, so the proof explicitly transports the universal pair between
those presentations before applying the normalization. No statement, definition,
public import, or blueprint unit route was changed.
The first preflight requested a change record for a newly opened notation scope.
That scope was removed and the private helper uses the existing scalar-extension
unit instead, so the final packet introduces no scope command or interface change.

## Second reading by A4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
