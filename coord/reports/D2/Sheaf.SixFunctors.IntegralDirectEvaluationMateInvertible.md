## What changed

Proved `WeilConjectures.IntegralSystemRealization.integralDirectEvaluationMate_invertible`
from the existing normalized singleton-extension construction and the normalized
extension-mate comparison theorem. The statement and the public imports stay unchanged.
All added helpers and proof imports are private. The proof identifies both specified
ordinary and derived evaluation squares, proves preservation of the flat-term K-flat
resolving class by intrinsic finite pullback, and applies iterated mates twice.
The item node records this route. Remote `lcompile.py` compiled the delivered module
without warnings in 36.2 seconds. The declaration signature and public-import list
were compared with the current source and are unchanged.

## Proved and sorry left

Closed the one original hole in
`WeilConjectures.IntegralSystemRealization.integralDirectEvaluationMate_invertible`.
Added zero holes and split off zero statements. No `sorry` remains in the delivered module.
The delivery uses existing declarations; their proof obligations remain their own items.

## No longer needed

The direct proof dependency `lem-pur-coefficient-system-derived-comparison`
(`Sheaf.Paper.CoefficientSystemDerivedComparison`) is not used: its existential
presentation choices are unnecessary for the fixed interfaces here. The existing singleton
model and the abstract normalized extension-mate theorem supply exactly the adjunctions
and comparison needed. No existing import is removed, and no module is withdrawn.
This removes the theorem from this item's proof dependencies. Its module remains in the
public import closure of `IntegralSystemOperations` for the existing interfaces, so no
module is globally pruned.

## Where the brief, the DAG or earlier work was wrong

The original plan suggests identifying the arbitrary direct-image datum using its
`factors` and `transpose` fields. Invertibility requires only `d.adj` and its fixed left
adjoint. The iterated-mates conjugation identity handles every such adjunction directly.
The original statement is preserved, including arbitrary `n` and arbitrary `Direct` datum;
no quotient-flatness, boundedness, or cartesianness hypothesis is introduced.

## Second reading by D2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
