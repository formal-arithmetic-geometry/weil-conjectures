## What changed

Filled the proof of `CategoryTheory.ExceptionalHomTransport.fullyFaithful_transport`
in `Sheaf.CategoryTheory.FullyFaithfulExceptionalHomTransport`, preserving all
signatures, definitions, docstrings and imports.

The proof follows the existing five-step node plan. The four maps are bijective;
naturality follows from the comparison and the two specified adjunctions. For
origin targets, naturality of the comparison unit factors the transport as the
specified preimage Hom chain followed by `originMap`. The unit is invertible
by full faithfulness. The counit maps to the origin comparison, and injectivity
then proves both unique-preimage statements. All auxiliary facts are local,
proved facts inside the existing theorem.

The existing Mathlib import supplies both planned Mathlib leaves:
`lem-weil-pbc-adjunction-of-natural-bijection` (the adjunction Hom formulas and
naturality) and `lem-sp-adjunction-unit-fully-faithful-left` (the invertible unit).
The route and its dependency records therefore remain unchanged. No blueprint
unit step is bypassed.

Validation: the complete module compiled through `lcompile.py`, exit code 0,
in 1.4 seconds with no warnings. The delivery checks also probe declaration axioms.

## Proved and sorry left

Closed 1 of 1 holes:
`CategoryTheory.ExceptionalHomTransport.fullyFaithful_transport`
(node `lem-sf-fully-faithful-exceptional-hom-transport`).

Holes added: 0. Holes remaining in the item: 0. Split-off statements: 0.

## No longer needed

None. No import, dependency node or module is removed. Both planned Mathlib
leaves are used through the original import
`Mathlib.CategoryTheory.Adjunction.FullyFaithful`.

## Where the brief, the DAG or earlier work was wrong

No mathematical or interface error was found. The planned proof works as stated.
Mathlib's adjunction naturality and fully faithful unit instances suffice;
no additional library statements or new nodes are needed.

## Second reading by E2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
