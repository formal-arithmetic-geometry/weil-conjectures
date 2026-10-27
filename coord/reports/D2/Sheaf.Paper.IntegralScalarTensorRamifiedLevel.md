## What changed

Proved `WeilConjectures.integralScalarTensorRamifiedLevel`, with its original signature,
in `Sheaf.Paper.IntegralScalarTensorRamifiedLevel`. The proof uses the existing normalized
principal quotient tower comparison and balanced scalar comparison, then the two normalized
tensor tower identifications and the ordinary scalar tensor chain isomorphism.

Proved private helpers identify the cochain scalar model with the published ordinary
functor, compare the actual and principal quotient towers preserving their augmentations,
and assemble the ramified reduction isomorphism. Naturality of the reduction augmentation
proves a chain-map equation for the final composite; evaluating it on pure bidegree generators
proves the required normalization. The arithmetic index is `m = e * (n + 1) - 1`, with its
inequality proved from `1 ≤ e`. No flatness, boundedness, or completeness hypothesis is added.

Updated the item's DAG proof, proof dependencies, and proof origin to this route. All changes
are confined to the item module and its node. The public import and public signature remain
identical. No shared definition, instance, or importer interface changes.

Validation: the complete delivered module compiled through `lcompile.py` in 23.1 seconds,
with no errors or warnings. The delivery tool performs the required independent compile
and axiom/hole probes before pushing.

## Proved and sorry left

Closed one original hole: `WeilConjectures.integralScalarTensorRamifiedLevel`
(`lem-pur-integral-scalar-tensor-ramified-level`).

Zero holes added; zero holes left in the delivered module; zero split-off statements.
All four private helpers are proved in full, including the elementary categorical
cancellation identity used by the two comparison equations.

## No longer needed

The planned direct dependency on `lem-weil-ramified-coefficient-quotient-comparison`
(`Sheaf.Paper.RamifiedCoefficientQuotientComparison`) is unnecessary: the existing
augmentation-preserving principal cokernel comparison supplies the required reduction
isomorphism directly. The planned direct dependency on
`lem-pur-change-of-rings-tensor-cancellation-independent` is also unnecessary in this
module: the already proved quotient and ordinary tensor comparisons encapsulate that
calculus. These two direct DAG edges are removed, and neither module is newly imported
for this proof. Their transitive uses in retained library proofs are preserved.

No existing Lean module is withdrawn, and no public import is removed.

## Where the brief, the DAG or earlier work was wrong

The original finite quotient route is mathematically sound, but its direct assembly is
unnecessary. Existing private proved APIs in `CompletedIntegralPrincipalUnitCriterion`
and `FiniteFreeQuotientRoosComparison` already provide the normalized principal quotient
comparison for every complex. They apply before derived completion or a Roos construction,
so those larger constructions need not be assembled here.

Searches used LeanFinder for ramified quotient scalar extension, Loogle for tensor
association, and Mathlib grep for quotient maps and cancellation. The useful complete
route was found in the existing project library. The unit's route is retained.

The zero complex and empty-site cases use the same universal comparisons. Index zero is
a positive quotient exponent one; for `e = 1` the chosen target index equals the source
index. No exceptional case is omitted.

## Second reading by D2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
