## What changed

Completed three proofs in `Sheaf.Paper.EtaleDerivedScalarTensor` without changing any
existing declaration signature or definition. `scalarSheafExtension_additive` uses
`Adjunction.left_adjoint_additive`. `scalarSheafTensorMap_naturality` specializes a
proved private monoidal-adjunction calculation: unit naturality, lax-tensorator
naturality, and right-unitor naturality. `scalarTensorFunctor_eq` specializes a
proved private reflexive identity for an arbitrary coefficient category. Keeping
that identity abstract avoids expensive reduction of the concrete module/sheaf
monoidal instances. The final module compiles in 8.8 seconds. A separate compiled axiom check
shows that each of the three completed theorems depends only on `propext`,
`Classical.choice`, and `Quot.sound`.

## Proved and sorry left

Original holes: 4. Closed: 3. Added: 0. Remaining: 1.

- Proved `AlgebraicGeometry.Etale.scalarSheafExtension_additive`.
- Proved `AlgebraicGeometry.Etale.scalarSheafTensorMap_naturality`.
- Proved `AlgebraicGeometry.Etale.scalarTensorFunctor_eq`.
- Left untouched: `AlgebraicGeometry.Etale.scalarTensorIso_existsUnique`, whose
  source and proof plan remain in its docstring under
  `lem-pur-derived-change-of-rings`.

This is a partial delivery of the multi-hole module, with no decomposition or
new postponed statements. The remaining hole concerns the normalized derived
scalar/tensor comparison, including compatibility of the selected left adjoint
with the explicitly transposed ordinary unit on all cochain representatives.

## No longer needed

Removed the unused proof-only imports
`WeilConjectures.Algebra.Homology.ChangeOfRingsTensorComparison` and
`Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients` from this module.
None of the three completed proofs uses their declarations. Their APIs concern
ring-sheaf module presentations, whereas these proofs only need additive and
monoidal adjunction identities and definitional equality. No claim is made that
these modules disappear from the targets' transitive import closure: the public
ring-sheaf change-of-rings interface is still reexported, and the final hole is
unchanged. No DAG node or blueprint unit is withdrawn.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement was changed or disputed. The module has no current
`lean.module` attachment in a DAG node; existing review notes record that its
former attachment to `lem-pur-derived-change-of-rings` was rebound to
`Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients`. Thus that
node's Lean theorem is a general ring-sheaf derived-change-of-rings existence
statement, rather than the explicit normalized comparison in this module.
The shared blueprint id in the docstrings is preserved. The completed proofs
follow their existing proof descriptions and require no node-route change.

## Second reading by K3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
