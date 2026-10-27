## What changed

This is the assigned compilation repair, with no mathematical statement change.
The 3,950-line module is separated at its existing section boundaries into eleven
modules: `PbcScalarTriangulation`, `PbcScalarTensor`, `PbcScalarComposition`,
`PbcScalarAmbientShift`, `PbcScalarRationalShift`, `PbcScalarStages`,
`PbcScalarAmbientOperations`, `PbcScalarOperationShift`,
`PbcScalarOperationIdentity`, `PbcScalarOperationComp`, and
`PbcScalarRestriction`, all under `Sheaf.Paper`.
`Sheaf.Paper.PbcScalarExtension` retains the primary theorem, the completed scheme-composition theorem and its helper, and publicly
re-exports every companion declaration. All original public imports remain
available. Proof imports are placed in the partitions that use them.

The original module and an optimized monolithic diagnostic both stopped at the
120-second diagnostic limit while elaborating the ambient scalar-shift instance.
The first thousand lines also exceeded the 60-second acceptance limit on their
own. A local irreducibility scope for `completedAdicDerivedChange`, introduced
before the ambient shift declarations, prevents expansion of its nested chosen
construction. The duplicate local attribute in the inner adjunction section is
removed. This changes neither the definition nor its exported reducibility.
After that optimization, the existing self-contained sections are compiled
separately, as permitted by the worker's explicit step 3a instructions.

A source comparison verifies that all 93 public names and signatures are
preserved. Existing proofs and constructions are moved, with their source and
proof docstrings retained; the primary theorem's proof is unchanged. The DAG now
attaches each companion declaration to its actual source module and records the
same nine-step unit route through these components. The change record is
`coord/changes/E5-pbc-scalar-extension-compilation.md`.

All twelve final delivery modules passed `lcompile.py` with the per-file limit
unchanged. The temporary `import all` probe resolved all sixty original private
helper names and compiled successfully; it is retained only in scratch, outside
the delivery. Static comparison also confirms unchanged public proof and
construction bodies, not only unchanged signatures.

## Proved and sorry left

This repair closes zero of the eight existing holes and adds zero mathematical
holes. No theorem is replaced by a weaker statement or a new unproved copy.
The following eight existing obligations are relocated, unchanged:

- `AlgebraicGeometry.Scheme.pbcEmbeddingAmbientTensor_preserves`:
  `lem-pbc-scalar-tensor-construction`.
- `AlgebraicGeometry.Scheme.pbcStageAssociator_laws`:
  `lem-pbc-scalar-stage-coherence`.
- `AlgebraicGeometry.Scheme.pbcScalarDirectImageMap_isIso`:
  `lem-pbc-scalar-ambient-operation-comparisons`.
- `AlgebraicGeometry.Scheme.pbcScalarCompletionIso_exists`:
  `lem-pbc-scalar-ambient-operation-comparisons`.
- `AlgebraicGeometry.Scheme.pbcScalarCompletedExchange`:
  `lem-pbc-scalar-ambient-operation-comparisons`.
- `AlgebraicGeometry.Scheme.pbcScalarOperations_identity`:
  `lem-pbc-scalar-operation-unit-coherence`.
- `AlgebraicGeometry.Scheme.pbcScalarOrdinaryPull_comp`:
  `lem-pbc-scalar-operation-composition-coherence`.
- `AlgebraicGeometry.Scheme.pbcScalarOrdinaryPull_coefficients`:
  `lem-pbc-scalar-operation-composition-coherence`.

The earlier attempt's proposed pentagon and repeated-index split theorems are not
part of this delivery. Its original coherence obligation is retained instead.

## No longer needed

No mathematical dependency, unit step or module is pruned.
The entry-point module needs none of its twelve original private proof imports.
It imports the private ambient and identity helpers for the retained completed
scheme-composition proof.
Their disposition is complete below (all module names are their full import names).

| Original proof import | Location after the repair |
| --- | --- |
| `WeilConjectures.CategoryTheory.DerivedCategory.Complete.RationalizationHom` | Triangulation partition |
| `Sheaf.Algebra.Homology.DerivedScalarExtensionCounitShift` | Rational-shift partition |
| `WeilConjectures.CategoryTheory.RightKanExtensionCoherentShift` | Ambient-shift partition |
| `WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates` | Removed; the used mate lemmas are in the unchanged public Mathlib import |
| `WeilConjectures.Mathlib.CategoryTheory.Linear.LinearFunctor` | Restriction partition |
| `Mathlib.Algebra.Homology.DerivedCategory.Linear` | Removed; already publicly exported by `PbcRationalCategory` |
| `Sheaf.CategoryTheory.SemilinearScalarLocalization` | Tensor construction partition |
| `all Sheaf.CategoryTheory.CanonicalRightDerivedAdjunctionShift` | Ambient-shift and operation-shift partitions |
| `all Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction` | Ambient-shift partition |
| `WeilConjectures.CategoryTheory.DerivedCategory.Shift.ExactFunctor` | Ambient-shift, rational-shift and operation-shift partitions |
| `all Sheaf.Paper.PbcActualScalarPullback` | Operation-shift partition |
| `WeilConjectures.Mathlib.CategoryTheory.Shift.Adjunction` | Ambient-shift and operation-shift partitions |

The rational-shift proof directly imports `Mathlib.CategoryTheory.Shift.Localization`
for its localization shift construction.
Private imports of preceding partitions provide the helpers used across section
boundaries. The entry-point module privately imports all extracted sections to
preserve its existing `import all` view: eleven direct consumers use some of the
sixty original private helpers. Public imports retain the original re-exported
interface. A temporary probe checks all sixty private helper names through
`import all Sheaf.Paper.PbcScalarExtension`.

## Where the brief, the DAG or earlier work was wrong

The rework row still names a quarantine path, but that path is absent in the
current shared clone and the complete module is already present at its original
`lean/` path. This repair uses that current source, preserving its statements,
dependencies and eight holes. The formerly missing imports listed in the brief
are currently available. The reproducible remaining failure was compilation
cost, not a missing mathematical dependency.

The previous attempt added two coherence holes without resolving the compilation
failure. Those changes were set aside in the sandbox scratch directory. The
current repair keeps the original bundled coherence theorem and addresses the
observed compilation stall. No launcher script or limit is changed.

## New nodes

`lem-pbc-scalar-triangulation-adapters` records the existing canonical rational
triangulation and integral isomorphism-closure adapters.

`lem-pbc-scalar-tensor-construction` records the existing completed coefficient
map, constructible restriction, semilinearity and raw rational tensor functor.

`lem-pbc-scalar-tensor-composition` records the existing coefficient-map
composition, ambient/rational associators and unit comparisons.

`lem-pbc-scalar-ambient-shift-normalization` records the existing counit-normalized
ambient shift and its adjunction and associator compatibility proofs.

`lem-pbc-scalar-rational-exactness` records the existing integral/rational shift
descent, composition-shift compatibility and rational exactness proofs.

`lem-pbc-scalar-stage-coherence` records the existing normalized finite-field
stages, the retained pentagon/unit obligation, exactness and shift coherence.

`lem-pbc-scalar-ambient-operation-comparisons` records the existing coefficient
structure square, operation/completion comparisons and completed-exchange routes.

`lem-pbc-scalar-operation-shift-coherence` records the existing shift compatibility
proofs for the operation comparisons.

`lem-pbc-scalar-operation-unit-coherence` records the existing operation identity
obligation and the completed identity comparison proof.

`lem-pbc-scalar-operation-composition-coherence` records the existing ordinary/direct-image scheme and
coefficient-tower composition equations, retaining their two ordinary-pull holes.

`lem-pbc-scalar-constructible-operation-restriction` records the existing linear
restriction and conditional rational operation-comparison proofs.

These nodes partition already existing declarations; they add no new Lean
statement or proof obligation. The change record is
`coord/changes/E5-pbc-scalar-extension-compilation.md`.

## Second reading by E5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
