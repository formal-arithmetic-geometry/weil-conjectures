## What changed

Restored the quarantined item from its recorded archive and proved
`AlgebraicGeometry.Scheme.integralResidueFiniteReduction` without changing either
published declaration or its signature. The proof uses the existing four-corners
comparison and coefficient equivalences. Private proved helpers identify the large
finite-coefficient inverse image with the continuous-function presentation, using
the constant-section normalization and uniqueness of left adjoints. Exact
localization supplies the comparison on arbitrary derived objects and their
canonical representatives.

Added proof imports of `Sheaf.Paper.ScalarCoefficientEquivalence`,
`Sheaf.Paper.IntegralPullbackScalarComparison`, and
`Sheaf.Paper.ConstructibleCoefficientSerre`; imported the private restriction
comparison from the already publicly imported
`Sheaf.Paper.IntegralCoefficientCompletenessTransport`. Updated the item's proof
plan and proof dependencies to this argument. All public imports, definitions,
and theorem signatures are preserved. No other existing module is changed.

Validation: the complete item compiled through lcompile.py in 49.5 seconds, with
no warnings or errors. Import-direction checks passed for all three added proof
imports. Text comparison with the archived source confirmed the public theorem
signature and finite-model definition are verbatim. The revised proof dependency
list equals the union of the proof steps' uses.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.integralResidueFiniteReduction`
(node `lem-weil-pbc-integral-residue-finite-reduction`).
Added zero holes and zero split statements. The item's remaining hole count is zero.
All new private helpers have complete proofs. The original
`integralResidueFiniteModel` construction is preserved verbatim.

The argument imposes no completeness, constructibility, boundedness, covering,
nonempty-scheme or nonzero-object hypothesis. The quotient index remains n+1,
including n=0. Arbitrary unbounded complexes are handled by exact localization.

## No longer needed

No original import was removed and no module was withdrawn.
The direct planned proof dependency
`lem-weil-pbc-ringed-topos-kflat-pullback`
(`Sheaf.Paper.KFlatRingedToposPullback`) is unnecessary here: the existing
four-corners comparison supplies the derived tensor/pullback interchange.
This does not assert that this dependency is absent from the library's transitive
imports or authorize removing any of its declarations.

## Where the brief, the DAG or earlier work was wrong

The original second proof step suggested reconstructing the K-flat tensor
comparison. That comparison already exists as `AdicCoefficientDatum.chi`.
The extra work needed here is exact finite coefficient-presentation transport,
which follows from the existing normalized scalar and sheafification adjunctions.
No statement correction or definition repair is required, and the unit route is
unchanged. The item was initially absent from lean/ and was copied from the exact
quarantine path recorded in coord/rework.tsv; its Lean attachment is retained.

## Second reading by R2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
