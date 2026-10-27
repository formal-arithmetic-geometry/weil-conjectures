## What changed

Proved `compactSupportCoefficientModels_moduleBalancing` in the item module.
The proof uses the existing ordinary tensor cancellation construction in
`SiteDerivedTensorRestriction` and a locally proved tensor-generator
extensionality helper via the module sheafification adjunction. An abstract, proved private uniqueness lemma
keeps the chosen scalar-extension object out of the generator calculation.
The scalar-one specialization and the inverse identity determine every generator.

Added a proof import for the ordinary cancellation helper. The existing private comparison
specifications in `FiniteFreeCompletedScalarComparison` replace direct unfolding
in the already proved chi clause, with the two comparisons locally irreducible.
All existing public signatures, definitions, instances and public imports remain.
Updated the existing node's proof, proof dependencies and proof origin.

## Proved and sorry left

Original item holes: 3. Item holes closed: 1. Item holes left: 2. Holes added: 0.

- `WeilConjectures.compactSupportCoefficientModels_moduleBalancing`: proved.
- `WeilConjectures.compactSupportCoefficientModels_ordinary`: original `sorry` remains.
- `WeilConjectures.compactSupportCoefficientModels_furtherTensor`: original `sorry` remains.

The remaining theorems retain their original source and complete proof in words.
No split statements, axioms or postponed data constructions are added.
A complete candidate for the chain argument compiled in a focused probe but made
the full item exceed the compile limit; it is not included in this delivery.

## No longer needed

None. No existing import, node or module is withdrawn. The original dependencies
remain for the two open clauses; the unit route remains unchanged. No node is
claimed globally unnecessary.

## Where the brief, the DAG or earlier work was wrong

No statement correction is made. The module comparison requires no flatness of
the ramified quotient map, including the zero quotient and zero modules.
An identical ordinary-comparison statement exists in
`CompactSupportScalarLimitReduction`, but its node depends on this item; that
route was not used because it would make a circular proof dependency.

## Second reading by R7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
