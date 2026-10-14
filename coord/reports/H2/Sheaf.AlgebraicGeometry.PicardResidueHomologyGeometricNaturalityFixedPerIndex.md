## What changed

Withdraw the item and its six unused caller modules through `deleted.txt`.
The current parent already follows the direct chosen-map route, so no parent rewrite
is delivered. Detach the Lean attachments of the eight retained DAG nodes.
The change record is `coord/changes/picard-residue-unused-wrapper-withdrawal.md`.

## Proved and sorry left

Proved: none. This is a completed pruning delivery under item brief §8d.
Holes removed by withdrawal: one,
`AlgebraicGeometry.Scheme.picard_residue_homology_geometric_naturality_fixed_positive_per_index`
(node `new-picard-residue-homology-geometric-naturality-fixed-per-index`).
Holes added: zero. No admitted declaration remains in a delivered Lean module.
The existing root-facing
`AlgebraicGeometry.Scheme.picard_residue_homology_chosen_geometric_maps` remains outside
this delivery; it is not claimed as proved or removed.

## No longer needed

The seven withdrawn modules are:

- `Sheaf.AlgebraicGeometry.PicardResidueHomologyGeometricNaturalityFixedPerIndex`
- `Sheaf.AlgebraicGeometry.PicardResidueHomologyGeometricNaturalityFixed`
- `Sheaf.AlgebraicGeometry.PicardResidueHomologyGeometricNaturality`
- `Sheaf.AlgebraicGeometry.PicardResidueCyclesGeometricNaturality`
- `Sheaf.AlgebraicGeometry.PicardFixedModelResidueCycleComparison`
- `Sheaf.AlgebraicGeometry.PicardFixedModelResidueDerivedComparison`
- `Sheaf.AlgebraicGeometry.PicardFixedModelResidueChainComparison`

The eight detached nodes are:

- `lem-sc-picard-residue-homology-geometric-naturality`
- `lem-sc-picard-fixed-model-residue-cycle-comparison`
- `new-picard-residue-homology-naturality-fixed`
- `lem-sc-picard-fixed-model-residue-chain-comparison`
- `lem-sc-picard-residue-cycles-geometric-naturality`
- `new-picard-residue-homology-geometric-naturality-fixed-per-index`
- `new-picard-residue-homology-naturality-fixed-positive`
- `lem-sc-picard-fixed-model-residue-derived-comparison`

All imports of those seven withdrawn modules are removed with their callers:

- `Sheaf.AlgebraicGeometry.PicardResidueHomologyGeometricNaturalityFixedPerIndex`: `Mathlib.AlgebraicGeometry.Morphisms.Proper`, `Mathlib.AlgebraicGeometry.Morphisms.Flat`, `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`, `Mathlib.AlgebraicGeometry.Morphisms.Immersion`, `Mathlib.AlgebraicGeometry.Fiber`, `Mathlib.LinearAlgebra.TensorProduct.Tower`, `Mathlib.RingTheory.LocalRing.ResidueField.Ideal`, `Sheaf.AlgebraicGeometry.TensorPullback`, `Sheaf.AlgebraicGeometry.StructureSheafCohomologyPullback`, `WeilConjectures.AlgebraicGeometry.Modules.Invertible`, `Sheaf.AlgebraicGeometry.AffineResidueCycleHomology`, `Sheaf.AlgebraicGeometry.PerfectComplex`, `Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage`.
- `Sheaf.AlgebraicGeometry.PicardResidueHomologyGeometricNaturalityFixed`: `Mathlib.AlgebraicGeometry.Morphisms.Proper`, `Mathlib.AlgebraicGeometry.Morphisms.Flat`, `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`, `Mathlib.AlgebraicGeometry.Morphisms.Immersion`, `Mathlib.AlgebraicGeometry.Fiber`, `Mathlib.LinearAlgebra.TensorProduct.Tower`, `Mathlib.RingTheory.LocalRing.ResidueField.Ideal`, `Sheaf.AlgebraicGeometry.TensorPullback`, `Sheaf.AlgebraicGeometry.StructureSheafCohomologyPullback`, `WeilConjectures.AlgebraicGeometry.Modules.Invertible`, `Sheaf.AlgebraicGeometry.AffineResidueCycleHomology`, `Sheaf.AlgebraicGeometry.PerfectComplex`, `Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage`, `Sheaf.AlgebraicGeometry.PicardResidueHomologyGeometricNaturalityFixedPerIndex`, `Sheaf.AlgebraicGeometry.PicardResidueHomologyGeometricComparisonSource`.
- `Sheaf.AlgebraicGeometry.PicardResidueHomologyGeometricNaturality`: `Mathlib.AlgebraicGeometry.Morphisms.Proper`, `Mathlib.AlgebraicGeometry.Morphisms.Flat`, `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`, `Mathlib.AlgebraicGeometry.Morphisms.Immersion`, `Mathlib.AlgebraicGeometry.Fiber`, `Mathlib.LinearAlgebra.TensorProduct.Tower`, `Mathlib.RingTheory.LocalRing.ResidueField.Ideal`, `Sheaf.AlgebraicGeometry.TensorPullback`, `Sheaf.AlgebraicGeometry.StructureSheafCohomologyPullback`, `WeilConjectures.AlgebraicGeometry.Modules.Invertible`, `Sheaf.AlgebraicGeometry.AffineResidueCycleHomology`, `Sheaf.AlgebraicGeometry.PerfectComplex`, `Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage`, `Sheaf.AlgebraicGeometry.PicardResidueHomologyGeometricNaturalityFixed`.
- `Sheaf.AlgebraicGeometry.PicardResidueCyclesGeometricNaturality`: `Mathlib.AlgebraicGeometry.Morphisms.Proper`, `Mathlib.AlgebraicGeometry.Morphisms.Flat`, `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`, `Mathlib.AlgebraicGeometry.Morphisms.Immersion`, `Mathlib.AlgebraicGeometry.Fiber`, `Mathlib.LinearAlgebra.TensorProduct.Tower`, `Mathlib.RingTheory.LocalRing.ResidueField.Ideal`, `Sheaf.AlgebraicGeometry.TensorPullback`, `Sheaf.AlgebraicGeometry.StructureSheafCohomologyPullback`, `WeilConjectures.AlgebraicGeometry.Modules.Invertible`, `Sheaf.AlgebraicGeometry.PerfectComplex`, `Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage`, `Sheaf.AlgebraicGeometry.PicardResidueHomologyGeometricNaturality`.
- `Sheaf.AlgebraicGeometry.PicardFixedModelResidueCycleComparison`: `Mathlib.AlgebraicGeometry.Morphisms.Proper`, `Mathlib.AlgebraicGeometry.Morphisms.Flat`, `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`, `Mathlib.AlgebraicGeometry.Morphisms.Immersion`, `Mathlib.AlgebraicGeometry.Fiber`, `Mathlib.LinearAlgebra.TensorProduct.Tower`, `Mathlib.RingTheory.LocalRing.ResidueField.Ideal`, `Sheaf.AlgebraicGeometry.TensorPullbackAdjunction`, `Sheaf.AlgebraicGeometry.StructureSheafCohomologyPullback`, `WeilConjectures.AlgebraicGeometry.Modules.Invertible`, `Sheaf.AlgebraicGeometry.PerfectComplex`, `Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage`, `Sheaf.AlgebraicGeometry.PicardDescendedFibreCoefficientTrivial`, `Sheaf.AlgebraicGeometry.PicardResidueCyclesGeometricNaturality`.
- `Sheaf.AlgebraicGeometry.PicardFixedModelResidueDerivedComparison`: `Mathlib.AlgebraicGeometry.Morphisms.Proper`, `Mathlib.AlgebraicGeometry.Morphisms.Flat`, `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`, `Mathlib.AlgebraicGeometry.Morphisms.Immersion`, `Mathlib.AlgebraicGeometry.Fiber`, `Mathlib.LinearAlgebra.TensorProduct.Tower`, `Mathlib.RingTheory.LocalRing.ResidueField.Ideal`, `Sheaf.AlgebraicGeometry.TensorPullbackAdjunction`, `Sheaf.AlgebraicGeometry.StructureSheafCohomologyPullback`, `WeilConjectures.AlgebraicGeometry.Modules.Invertible`, `Sheaf.AlgebraicGeometry.PerfectComplex`, `Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage`, `Sheaf.AlgebraicGeometry.DerivedFiberBetti`, `Sheaf.AlgebraicGeometry.AffineBettiModelResidueMinimality`, `Sheaf.AlgebraicGeometry.PicardFixedModelResidueCycleComparison`, `Sheaf.LinearAlgebra.ResidueCycleProductComparison`.
- `Sheaf.AlgebraicGeometry.PicardFixedModelResidueChainComparison`: `Mathlib.AlgebraicGeometry.Morphisms.Proper`, `Mathlib.AlgebraicGeometry.Morphisms.Flat`, `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`, `Mathlib.AlgebraicGeometry.Morphisms.Immersion`, `Mathlib.AlgebraicGeometry.Fiber`, `Mathlib.LinearAlgebra.TensorProduct.Tower`, `Mathlib.RingTheory.LocalRing.ResidueField.Ideal`, `Sheaf.AlgebraicGeometry.TensorPullbackAdjunction`, `Sheaf.AlgebraicGeometry.StructureSheafCohomologyPullback`, `WeilConjectures.AlgebraicGeometry.Modules.Invertible`, `Sheaf.AlgebraicGeometry.PerfectComplex`, `Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage`, `Sheaf.AlgebraicGeometry.DerivedFiberBetti`, `Sheaf.AlgebraicGeometry.PicardFixedModelResidueDerivedComparison`, `Sheaf.AlgebraicGeometry.PerfectAffineMapRepresentative`.

The source and target geometric comparison modules, residue quotient models,
affine minimality, descended coefficient trivialization and representative theorem
are retained because the direct route still uses them.

## Where the brief, the DAG or earlier work was wrong

The claim was dispatched while this item was on the old root path. During this
session the checkout acquired the BYPASS-picardh1 parent rewrite (file timestamps
2026-10-15 04:28:32 CST). After that rewrite this item and all of its wrapper callers
have no target path or independent caller. The route note’s preferred pruning has
already happened at the parent, and §8d applies to these now-unused modules.

Checks on the current checkout: `TargetsCheck` import closure contains 11,405 modules;
none of the seven withdrawn modules is in it. The outer chain-comparison module
has zero direct importers. All remaining direct importers lie in the withdrawal set.
The eight nodes have zero dependency users outside the set and no unit realizations.
All six other modules are unclaimed; no other group’s held module is adapted.

Exploratory affine naturality proofs and the attempted parent rewrite are kept only
in the sandbox scratchpad. They are not delivered: their full geometric dependency
has no current source attachment, and restoring that obsolete route would add work
that the targets do not need.

## Second reading by H2

1. **Signatures and accidental changes.** I compared every withdrawn module with the
repository checkout and checked the complete import and declaration-name scans. The
seven paths in `deleted.txt` are the only changed Lean paths; no replacement module is
present. The eight copied DAG nodes preserve their statements, proof plans, sources,
units, and statuses, while only their `lean` attachments are detached. Verdict: no
signature was silently weakened, strengthened, or altered.

2. **Proof and kernel checks.** This delivery intentionally contains no Lean declaration:
it is a permitted §8d withdrawal after the parent route made the chain unreachable.
The withdrawn target had one `sorry`; deletion removes that admitted declaration, and
no `sorry`, axiom, unsafe declaration, opaque declaration, or hollow definition is
introduced. There is therefore no replacement proof to compile or to probe for extra
axioms. Verdict: the withdrawal is proof-free and introduces no kernel obligations.

3. **Split-off statements.** No new statement is added. I checked the eight detached
nodes and found no new Lean declaration or restatement hidden in the delivery; their
mathematical statements and source/proof records remain in the DAG for possible future
work. Verdict: no split-off statement is claimed, changed, or needed here.

4. **Pruning and route.** I independently scanned the current `TargetsCheck` closure:
none of the seven modules is reachable, the outer chain-comparison module has no direct
importer, and all remaining importers are within the withdrawal set. The eight nodes
have no dependency users outside that set and do not realize a unit or unit proof step.
The current parent uses the chosen-map route, so this withdrawal preserves the realized
unit route and removes obsolete proof-dependency imports. Verdict: pruning is complete
and does not bypass a realized unit.

5. **DAG agreement.** Each detached node has `lean: null` in the delivery copy, while
its statement, `proof`, `proof_deps`, `proof_origin`, chapter, and unit agree with the
repository node. The change record documents the seven deletions, the six internal
caller links, the detached nodes, and the unchanged direct parent route. Verdict: the
DAG and the delivered withdrawal agree.

Changed in this second reading: only this report section was added; no Lean source,
node statement, proof plan, or unit record was modified.
