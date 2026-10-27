## What changed

Proved `WeilConjectures.PurityFiniteSetting.finite_adjoint_mate_composition`, the one
remaining hole in the current item. A proved private categorical helper computes the
counit of the successive coefficient mates and applies the existing pointwise
coefficient-exchange theorem to the compact-support compositors. Smooth exceptional
finite-Tor preservation makes the existing compact scalar composition equation applicable.
The tensor, arbitrary Cartesian base-change and transpose proofs already in the current
library are preserved. No statement, definition or public import changes.

## Proved and sorry left

Closed: `WeilConjectures.PurityFiniteSetting.finite_adjoint_mate_composition`
(node `lem-pur-finite-adjoint-mate-compatibility`).

Original holes closed: 1 of 1 in the current library version. Holes remaining in the
item: zero. Holes added: zero. Split-off statements: zero. The private helper is proved.

## No longer needed

No direct import is removed from the current library version, and no module is withdrawn.
The composition proof no longer uses the bundled `lem-coef-finite-exceptional` theorem
or `lem-sf-compact-coefficient-composition`: it uses the defining `mateMap_counit`
equations and `lem-pur-etale-compact-scalar-coherence` directly, then a proved composite
counit calculation. These two obsolete top-level `tool_uses` entries are removed from
the node, and its proof dependencies follow the actual proof.

`Sheaf.SixFunctors.CompactCoefficientComposition` remains imported for the finite
coefficient instance used by the existing clause definitions. The exceptional coefficient
maps and intrinsic finite exceptional data also remain needed; removing the bundled
theorem from this proof does not withdraw their definitions or modules. The blueprint
unit and its realized steps are preserved.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement or definition needed repair. The general pointwise
coefficient-exchange theorem also handles the composition square: the only additional
calculation is the counit of the composite mate. Thus a separate geometric exceptional
composition compatibility theorem is unnecessary here. The proof does not assume
invertibility of the exceptional coefficient comparison.

## Second reading by V6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
