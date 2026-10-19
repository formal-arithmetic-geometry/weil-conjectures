## What changed

Proved `RingHom.isExcellent_of_weaklyEtale` in
`Sheaf.RingTheory.ExcellentOfWeaklyEtale`, following all six existing DAG steps.
The proof obtains source Noetherianity from excellence, obtains the Nagata property
from quasi-excellence, and obtains prime-local Nagata properties from Nagata
localization. It applies the three stated weakly-etale ascent theorems and assembles
Noetherianity, the G-ring property, J-2, and universal catenarity of the target.
The signature, definitions, docstrings, imports, and DAG route are unchanged.
The module compiled successfully through `lcompile.py` (exit code 0, 2.2 seconds).

The required semantic, name, and textual searches found no shorter Mathlib result:
Lean Finder returned etaleness lemmas; Loogle returned no `IsExcellent` match;
Mathlib grep returned only an unrelated bibliographic use of “excellent”. The
source library's ring-theory directory likewise has no excellence theorem.

## Proved and sorry left

Closed one hole: `RingHom.isExcellent_of_weaklyEtale`
(node `lem-exc-weakly-etale-excellent`). No holes remain in the item and no holes
were added or split off. This is a complete proof from the existing named
proof dependencies, whose remaining proofs are separate stage-3 items.

## No longer needed

None. All five proof-only imports and all six declared proof dependencies are
used. No nodes or modules are pruned. Existing public imports are preserved.

## Where the brief, the DAG or earlier work was wrong

None. The dependency signatures fit the plan, including different universes for
source and target. The proof adds no nontriviality, finite-presentation, or
faithful-flatness assumption, so the zero-ring case is covered unchanged.

## Second reading by E7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
