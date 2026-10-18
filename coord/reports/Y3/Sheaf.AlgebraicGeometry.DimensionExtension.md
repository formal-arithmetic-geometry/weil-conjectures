## What changed

Proved `AlgebraicGeometry.topologicalKrullDim_fieldExtension_and_denseOpen` without changing
its signature. Reused the already proved source-library theorems
`topologicalKrullDim_pullback_eq_of_field` and `topologicalKrullDim_le_of_dense`.
The dense-open proof transports the latter inequality through the open embedding's
homeomorphism onto its range and uses inducing-map dimension monotonicity in the other direction.
Updated the theorem docstring and its DAG proof to this route; the unit has no prescribed steps.
Only the two source modules are added as proof imports. Removed unused statement and proof imports.

Public-import cleanup is recorded in
`coord/changes/Y3-dimension-extension-imports.md`. No definitions or signatures change.

## Proved and sorry left

Closed one of one holes:
`AlgebraicGeometry.topologicalKrullDim_fieldExtension_and_denseOpen`
(node `lem-kun-dimension-extension`). Added zero holes and split off zero theorems.
No `sorry` remains in the delivered module. This is a proof, not a decomposition.
Both reused source proofs were read in full; their statements require no nonemptiness,
reducedness, irreducibility or separatedness, so empty schemes and arbitrary field extensions
are included. Validation: deliver3.py --no-push succeeded: the module compiles and passes preflight,
including the axiom probe. Static signature, import-pruning, line-width and DAG
dependency-union checks also pass. Two preceding lcompile.py attempts received no answer
from the server; the successful dry run resolved that temporary infrastructure issue.
The pruned module and all three unchanged direct importers compiled together in dependency
order through lcompile.py: DimensionExtension (3.5 s), EtaleExceptionalConstantTensor (1.6 s),
OpenProductExchange (1.7 s), and FlatFpRelativeDimensionDenseOpen (0.1 s).
Review class is CODEX because the delivery changes the DAG and removes public imports.

## No longer needed

Removed imports:

- `Mathlib.Algebra.Algebra.Defs`
- `Mathlib.Algebra.Category.Ring.Colimits`
- `Mathlib.Algebra.Field.Defs`
- `Mathlib.AlgebraicGeometry.Modules.Sheaf`
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`
- `Mathlib.AlgebraicGeometry.Morphisms.Immersion`
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`
- `Mathlib.AlgebraicGeometry.Noetherian`
- `Mathlib.AlgebraicGeometry.Properties`
- `Mathlib.AlgebraicGeometry.ResidueField`
- `Mathlib.AlgebraicGeometry.Scheme`
- `Mathlib.FieldTheory.IsAlgClosed.Basic`
- `Mathlib.RingTheory.AlgebraicIndependent.Basic`
- `Mathlib.Topology.Irreducible`
- `Mathlib.Topology.NoetherianSpace`
- `Mathlib.Topology.Sheaves.Functors`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct`
- `Sheaf.AlgebraicGeometry.BaseChangeConventions`
- `Sheaf.AlgebraicGeometry.ClosedIrreducibleDimensionTrdeg`
- `Sheaf.AlgebraicGeometry.DimensionPreservedFieldExtension`
- `Sheaf.AlgebraicGeometry.FieldBaseChangeAffineCovers`
- `Sheaf.AlgebraicGeometry.TensorPullback`
- `Sheaf.Topology.InverseImageModule`
- `WeilConjectures.AlgebraicGeometry.Picard.Defs`

The following original direct proof dependencies are unnecessary in this module; the existing
source proofs supply both global comparisons directly. Some may still be used transitively
or by other project modules; no claim is made that they are globally unreachable:

- `def-kun-dimension`
- `def-kun-transcendence-degree`
- `def-pc-base-change`
- `def-weil-finite-type-morphism`
- `def-weil-irreducible-components`
- `def-weil-residue-field`
- `lem-pc-dim-base-change-affine-covers`
- `lem-sc-closed-irreducible-dimension-trdeg`
- `lem-sc-noetherian-closed-subset-finite-components`
- `lem-weil-pbc-dimension-bound-open-cover`
- `lem-weil-pbc-dimension-preserved-field-extension`
- `lem-weil-pbc-finite-type-over-noetherian`
- `lem-weil-pbc-homeomorphism-krull-dimension`
- `lem-weil-pbc-noetherian-open-subscheme-noetherian`
- `lem-weil-pbc-proper-fp-permanence`
- `lem-weil-pbc-qc-open-immersion-finite-type`
- `lem-weil-pbc-scheme-sober`
- `pqf-def-locnoeth`

In particular the three removed Sheaf proof modules are
`Sheaf.AlgebraicGeometry.FieldBaseChangeAffineCovers`,
`Sheaf.AlgebraicGeometry.DimensionPreservedFieldExtension`, and
`Sheaf.AlgebraicGeometry.ClosedIrreducibleDimensionTrdeg`.
The old top-level tool_uses entries are withdrawn because none are used directly by this proof.
The source field-extension theorem is already a closed source attachment in
`lem-pc-dim-base-change.lean_audit.slopmaster2`; the dense-open comparison is already attached
to `lem-weil-pbc-dense-open-dimension-comparison`. No new nodes are needed.

## Where the brief, the DAG or earlier work was wrong

The nine-step plan was mathematically usable but redundant: the source library already proves
both global comparisons. Local rg located the source theorems after leanfinder, loogle and grep
searches found no matching Mathlib invariance theorem. The field-extension node's main Lean
attachment points to the Sheaf conjunction, but its audited closed source attachment is the
more general theorem used here (as in other existing project proofs).
There is no statement correction and no change to the unit's route.

## Second reading by Y3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
