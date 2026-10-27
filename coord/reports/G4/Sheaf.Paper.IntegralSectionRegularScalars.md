## What changed

Imported the scalar-comparison split module and replaced the `regularComparison` proof with a real reduction from arbitrary endomorphisms of the lifted regular module to multiplication by one scalar. Added the proved private `endomorphism_eq_scalar` lemma and its explicit scalar endomorphism helper. The new scalar comparison theorem is in `Sheaf.Paper.IntegralSectionRegularScalarsScalar`.

## Proved and sorry left

Closed the `regularComparison` sorry. Added one strictly smaller theorem, `scalarComparison`, whose remaining sorry is recorded by node `lem-sfb-integral-section-regular-scalars-scalar`. The rank-one linear algebra reduction is fully proved.

## No longer needed

No imports or declared proof dependencies were removed. The target proof still uses the normalized section-action, completed coefficient, stratified perfect model, continuous scalar, regular-extension, coefficient-encoding, and constant-section projection dependencies through `scalarComparison`.

## Where the brief, the DAG or earlier work was wrong

The original node's two proof paragraphs hide a separate scalar-naturality statement. The arbitrary endomorphism clause is a genuinely simpler final reduction because every endomorphism of the lifted regular module is multiplication by its value on `1`; this is now proved directly. No target statement was changed.

## New nodes

Added `lem-sfb-integral-section-regular-scalars-scalar`, the scalar-endomorphism comparison theorem used by the target proof.

The split node records the complete Lean statement verbatim, including its local functor lets and scalar endomorphism formula.

## Second reading by G4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
