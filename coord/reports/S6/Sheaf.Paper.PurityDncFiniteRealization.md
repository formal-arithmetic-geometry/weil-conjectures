## What changed

Proved `WeilConjectures.PurityFiniteSetting.Dnc.etaleUnitPlus` in
`Sheaf.Paper.PurityDncFiniteRealization`, without changing any signature or definition.
Use lower bound zero and transport Mathlib's `IsGE 0` instance for a single complex
through `DerivedCategory.singleFunctorObjUnitIso`. The canonical `comparisonUnit`
and `sectionComparison` constructions are unchanged.

Validation: `deliver3.py --no-push` compiled the complete module through `lcompile.py`,
passed its axiom probe and the server preflight, and reported review class `AUTO`.
The proof applies to every scheme in the
statement, including the empty scheme, and uses no additional coefficient hypothesis.
LeanFinder and Loogle located the single-complex boundedness instance; source search
found the existing unit isomorphism and the same construction in
`Sheaf.Paper.BoundaryDualizingComposition.boundaryCoefficientPlus`.

## Proved and sorry left

Closed 1 of 1 original holes:
`WeilConjectures.PurityFiniteSetting.Dnc.etaleUnitPlus`
(node `def-pur-finite-section-comparison`).

No `sorry` remains in the item. No holes were added, and no statements were split off.
The two existing definitions remain the original explicit canonical constructions.
This closes the local hole; imported dependencies retain their existing proof status.

## No longer needed

None. No imports were added; the proof uses `DerivedCategory.FlatModel`, already
publicly imported by the module, and Mathlib's canonical t-structure API.
The existing public import interface is retained. The node has no planned proof
steps or proof dependencies to prune; no new dependency nodes or modules are needed.
The surrounding DNC unit route is unchanged.

## Where the brief, the DAG or earlier work was wrong

None. The declaration's documented degree-zero argument is supplied directly by
existing library and Mathlib results.

## Second reading by S6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
