## What changed

Proved `WeilConjectures.VerdierHomChainComposition.projection_exceptional_paste`
without changing its statement or imports. Private proved helpers establish inverse
exceptional-transpose composition, naturality of signed tensor uncurrying, equality
transport of the closed presentations, and projection composition on the full finite-Tor
subcategories. The ambient projection equation is the finite, integral, rational, or
common composition field of `compactSupportProjectionFormula S`.

The complete proof was checked by `lcompile.py` in 15.8 seconds; the delivery
checks validate the final lint cleanup and probe every declaration.

## Proved and sorry left

Closed the one original hole:
`WeilConjectures.VerdierHomChainComposition.projection_exceptional_paste`
(node `lem-sf-verdier-projection-exceptional-paste`). No holes added or split off.
No `sorry` remains in the delivered module. Existing dependencies are unchanged.

## No longer needed

None. The proof uses both declared proof dependencies:
`def-sf-verdier-hom-composition-coordinates` and `fix-prop-projection-formula`.
No imports, nodes, or modules are removed. The blueprint unit route is preserved.

## Where the brief, the DAG or earlier work was wrong

No statement or definition repair was needed. The proof follows the three steps of
the existing node. First-factor tensor naturality on Z suffices for this equation;
the original hypotheses on X and Y remain in the unchanged statement.

## Second reading by A4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
