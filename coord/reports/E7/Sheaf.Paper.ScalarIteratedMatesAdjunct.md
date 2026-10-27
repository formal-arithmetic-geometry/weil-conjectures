## What changed

Completed `AlgebraicGeometry.Etale.scalarMate_iterated_adjunct` in
`Sheaf.Paper.ScalarIteratedMatesAdjunct`. Apply Mathlib's `mateEquiv_counit`
to each specified scalar mate, use naturality of the s-counit, substitute the
two single-mate equations, and use naturality of the r-scalar/pullback
comparison. Functoriality and associativity give the displayed normal form.
This implements all four steps of `lem-pur-scalar-iterated-mates-adjunct`
without changing its proof dependencies or the unit route.

The public signatures, definitions, docstrings and imports are unchanged.
No other module is changed.

Validation: `lcompile.py` compiled the complete item without diagnostics
in 10.5 seconds.

## Proved and sorry left

Closed the sole existing hole:
`AlgebraicGeometry.Etale.scalarMate_iterated_adjunct`
(node `lem-pur-scalar-iterated-mates-adjunct`).

Holes closed: 1. Holes added: 0. Holes left in the item: 0.
No statements are split off.

## No longer needed

None. All four declared proof dependencies are used, through the specified
scalar mate, scalar/pullback comparison, geometric adjunctions and Mathlib's
mate/counit identity. No imports, nodes or modules are removed.

## Where the brief, the DAG or earlier work was wrong

None. Mathlib's proved `mateEquiv_counit` directly supplies step 1 of the
existing plan, including its generic adjunct/counit identity. The two
naturality steps apply without any additional geometric or coefficient
hypotheses. No boundedness, properness or invertibility of a scalar mate is
used.

## Second reading by E7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
