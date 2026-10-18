## What changed

Proved `SheafOfModules.changeOfRingsComplex_shape` by rewriting the original
complex differential to zero and proving that `changeOfRingsHom` maps zero to
zero. Proved `SheafOfModules.changeOfRingsComplex_comp` by rewriting through
composition preservation of `changeOfRingsHom`, then applying the original
complex's `d_comp_d` and the zero-map lemma. Added two private helper lemmas in
the item module; no imports or public signatures changed.

## Proved and sorry left

Proved `SheafOfModules.changeOfRingsComplex_shape`,
`SheafOfModules.changeOfRingsComplex_comp`, and the existing definition
`SheafOfModules.changeOfRingsComplex` now elaborates from those proofs. No
`sorry` remains in the item module; no new declarations or holes were added.

## No longer needed

None. The module's existing public imports are both needed for its statement
and definition, and no DAG dependency was bypassed.

## Where the brief, the DAG or earlier work was wrong

Nowhere found. The stated construction and proof route are valid; the DAG's
empty proof dependency list is sufficient because the required map properties
are proved directly from the imported tensor-product API and category
functoriality.

## Second reading by C4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
