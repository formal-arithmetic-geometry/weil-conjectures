## What changed

Proved `WeilConjectures.IntegralOnSlice.ordinaryQuotientModuleComparison` in
`Sheaf.Paper.OrdinaryQuotientModuleComparison`, keeping its signature and the
quotient functor definition unchanged. The proof identifies each quotient unit
as the cokernel of multiplication by the uniformizer power. The ordinary left
adjoint preserves these cokernels, yielding a natural comparison isomorphism.
Semilinearity and the completed-map projection equations establish the required
formula on every generator; adjunction and tensor extensionality prove uniqueness.

Added private proof imports of `IntegralDerivedOperationsOnSlices`,
`OrdinaryCommonQuotientTower`, `CompletedIntegralFiniteQuotientHomExt`,
`CompletedIntegralProjectionDivisibility`, and Mathlib's preservation-of-kernels
module. All helpers are private and proved. Updated the item's DAG proof,
proof dependencies and proof origin to describe this route. No other existing
module, public import, definition or statement was changed.

Validation: the complete delivered Lean module compiled through `lcompile.py`
with exit code zero and no warnings in 18.6 seconds. The theorem signature was
compared verbatim with the shared source; the node changes are restricted to
`proof`, `proof_deps`, and `proof_origin`.

## Proved and sorry left

Closed the one original hole:
`WeilConjectures.IntegralOnSlice.ordinaryQuotientModuleComparison`
(node `lem-fix-ordinary-quotient-module-comparison`).
No holes added or split off; no `sorry` remains in the delivered module.
The proof uses existing declarations, including their existing proof dependencies;
it does not claim to close holes in those other modules.

## No longer needed

No original Lean imports were removed. The planned dependency
`def-pur-cochain-tensor-coherence-data`
(module `Sheaf.SecSmoothPurity.CochainTensorCoherenceData`) is not needed: this argument
concerns a single module quotient and uses cokernels rather than cochain tensor
coherence. The planned dependency `prop-weil-pbc-proetale-constant-ring-map`
(module `Sheaf.AlgebraicGeometry.ProEtaleConstantRingMap`) is not needed for its
invertibility comparison: constant coefficient naturality and the specified
finite-projection equations suffice. These two nodes were removed from this
node's proof dependencies; no module is withdrawn and no claim is made about
other consumers or transitive imports.

## Where the brief, the DAG or earlier work was wrong

The planned tensor-coherence route is longer than necessary. Quotient
surjectivity and uniformizer-kernel divisibility already available in the
library give a cokernel description, which every additive left adjoint preserves.
In fact this proof does not need the coefficient-map invertibility hypothesis;
the assigned theorem retains that hypothesis verbatim. The quotient normalization
and uniqueness are proved explicitly, including exponent one and zero modules;
no flatness or nonemptiness hypothesis is introduced. No tool or statement
repair was required.

The proof uses `lem-sp-completed-integral-projection-divisibility` and the
constant-quotient surjectivity helper in
`lem-sp-completed-integral-finite-quotient-hom-ext` from the coefficient-towers
unit, and the proved generic epic-unit and local-kernel helpers in
`lem-weil-pbc-ordinary-common-quotient-tower` from the proper-base-change unit,
as tools. They supply the scalar-kernel and sheaf-tensor quotient facts used to
construct the cokernel; the assigned unit's existing comparison declarations do
not supply these facts. No unit statement or prescribed unit step is bypassed.
No maintainer `tool_uses` approval has been edited.

## Second reading by U8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
