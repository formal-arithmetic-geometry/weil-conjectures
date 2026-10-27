## What changed

Proved `CategoryTheory.ScalarCompositorReplacement.pasting` in
`Sheaf.CategoryTheory.ScalarCompositorReplacementPasting` with four fully proved private
helpers: inverse replacement, the coefficient equation, lambda transport, and composition
of compositor model squares. All public statements, definitions, docstrings and imports
are unchanged.

The proof follows the existing eight-step node plan. It uses naturality and the whiskering
interchange identity, cancels only specified isomorphisms, transports both sides of the
coefficient equation explicitly, proves the equivalence by cancelling the endpoint
isomorphisms, and verifies identity/composite coherence and cancellation of F-only changes.
There are no nonemptiness assumptions and no inversion of coefficient transformations.

Validation: the whole item compiled cleanly through lcompile.py, without warnings.
The delivery preflight checks axioms of every declaration, including private helpers.

## Proved and sorry left

Closed 1 of 1 original holes:
`CategoryTheory.ScalarCompositorReplacement.pasting`
(node `lem-sp-scalar-compositor-replacement-pasting`).

Zero holes remain; zero holes added; zero statements split off. All four private helpers
are completely proved from Mathlib and the original system/model square hypotheses.

## No longer needed

None. The original sole import `Mathlib.CategoryTheory.Whiskering` remains necessary.
No new imports were added. The sole declared dependency `def-nagata-category` is used;
no nodes or modules are pruned. The DAG proof and unit route are unchanged.

## Where the brief, the DAG or earlier work was wrong

No mathematical or interface errors found. The existing eight-step proof plan is realized
without changing its statement, dependencies, or proof route. Search found the needed
whiskering interchange and functoriality identities already in the original Mathlib import;
no additional general pasting theory was needed.

## Second reading by H4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
