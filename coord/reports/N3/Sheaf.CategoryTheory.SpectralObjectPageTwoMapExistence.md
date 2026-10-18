## What changed

Proved `CategoryTheory.Abelian.SpectralObject.exists_pageTwoMap_data` in
`Sheaf.CategoryTheory.SpectralObjectPageTwoMapExistence`, following both steps of
`lem-sp-spectral-object-page-two-map-existence` without changing the statement.

Private constructions apply the components of a spectral-object morphism to its
three-term complexes and take their homology maps. Naturality on cycles proves
compatibility with the page differentials. Naturality under changes of interval
indices provides the kernel and quotient maps in Mathlib's successor-page homology
data; `ShortComplex.LeftHomologyMapData.homologyMap_comm` then proves the
spectral-sequence morphism equation. On the first page,
`ShortComplex.HomologyMapData.ofZeros` proves compatibility with `EIsoH`, giving
the required page-two comparison.

Added only the proof import
`import all Mathlib.Algebra.Homology.SpectralObject.SpectralSequence` to access
the proof bodies of its homology data. No exported statement, existing definition,
consumer module, or DAG route changed. The static interface checker flags the
section-scoped variable commands and local unsealing commands; these are documented
in `coord/changes/spectral-object-page-two-map-proof-context.md`. The existing node's two proof steps and
both proof dependencies are retained. The unit record has no realized statement
or proof step attached to this item.

Validation: the entire file compiles through `lcompile.py` with no errors or
warnings (3.6 seconds). Its unmodified direct consumer,
`Sheaf.CategoryTheory.SpectralObjectPageTwoMap`, also compiles against the
proved module (2.6 seconds). The delivery dry run checks the declarations' axioms.

## Proved and sorry left

Closed 1 hole:
`CategoryTheory.Abelian.SpectralObject.exists_pageTwoMap_data`
(node `lem-sp-spectral-object-page-two-map-existence`).

Added 0 holes. No `sorry` remains in the delivered module. No split-offs.
All private helpers are proved or actual constructions; none chooses arbitrary
data from an unproved existence assertion.

## No longer needed

None. No import was removed, no declared dependency was bypassed, and no module
or node was pruned. The proof uses the abelian-category and spectral-sequence
structures recorded by `def-sp-abelian` and `def-sp-spectral-sequence`, together
with Mathlib's proved spectral-object homology API.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction was needed. Mathlib's existing `SpectralObject.map`
varies interval indices within one spectral object, so it cannot directly serve
as the map induced by a morphism between two spectral objects. The private
three-term-complex and homology maps supply precisely that missing construction.
The successor-page calculation works for arbitrary complex shapes using their
chosen predecessor and successor, including positions without a differential;
the specialization here imposes no quadrant or vanishing hypothesis.

## Second reading by N3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
