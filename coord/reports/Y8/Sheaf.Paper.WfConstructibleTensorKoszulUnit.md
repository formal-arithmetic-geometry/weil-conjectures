## What changed

Filled all three proofs in `Sheaf.Paper.WfConstructibleTensorKoszulUnit`, preserving
all public signatures and public imports. Added one proved private helper for
constructibility of the ordinary tensor under the normalized coefficient transport.
The category comparison reuses `integralStratifiedPerfectDetailed` and the existing
finite-reduction natural isomorphism. The quotient/Koszul comparison reuses
`completedKoszulQuotientComparison`; its chosen inverse components are natural by
the reflector uniqueness property, and preserve the actual specified units.

For tensor constructibility, the detailed tensor completion comparison is an
isomorphism on constructible inputs. Its target is constructible by
`integralOperations_preserve_constructible`. Flat K-flat representatives and
`ProjectionTensorCoefficient.totalIso` identify the coefficient transport of the
ordinary detailed tensor with `wfOrdinaryDerivedTensor`. The resulting property
implies invertibility of the actual intrinsic unit by `wfConstructible_complete`.
Constructibility transfers along that unit; naturality follows from the reflector
bijection defining `wfCompletion.map` for arbitrary integral arrows.

Updated the existing node's proof route and dependencies accordingly. Added only
private proof imports; no definitions, statements, public interfaces or consumers
were changed. No new nodes or split-off statements.

## Proved and sorry left

Closed three original holes:

- `WeilConjectures.wfConstructibleTensorCategories`.
- `WeilConjectures.wfConstructibleTensorKoszulComparison`.
- `WeilConjectures.wfConstructibleTensorKoszulUnit`.

The private helper `transported_tensor_constructible` is fully proved.
The item has zero `sorry` left. This delivery adds zero holes. These proofs use
existing stated dependencies, including dependencies whose own proofs remain
unfinished; it does not claim to have discharged those downstream holes.

## No longer needed

Removed private imports:

- `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType`.
- `Sheaf.Paper.IntegralAmbientOperationModels`.
- `Sheaf.Paper.ConstantCompletionEquivalence`.
- `Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients`.
- `Sheaf.Paper.IntegralUniformCoefficient`.

Removed direct proof dependencies and their obsolete top-level tool approvals:

- `lem-pod-separated-finite-type-base-change`, `lem-weil-pbc-qcqs-over-affine`,
  `lem-weil-pbc-finite-type-over-noetherian`, and `lem-kun-dimension-finite-type`:
  geometry is already packaged in `weilGeometricFiber_coefficientHypotheses`.
- `lem-pur-integral-ambient-operation-models`: ordinary tensor constructibility
  uses flat representatives and the existing coefficient tensor-total comparison.
- `lem-weil-pbc-constant-completion-equivalence` and
  `lem-weil-pbc-ringed-strict-tower-homotopy-limit`: the existing normalized
  `completedKoszulQuotientComparison` supplies the objectwise comparison, and
  reflector uniqueness supplies naturality.
- `def-weil-pbc-bounded-constructible-tower`: its data is handled by the existing
  category-comparison and isomorphism-invariance theorems.

These are direct-route removals. Some remain transitive dependencies of the reused
results; no module is withdrawn and no global closure pruning is asserted.
The original public imports remain verbatim. Removed tool approvals are the seven
geometry/ambient/comparison entries listed above; no tool approval was added or
reordered. New direct dependencies are recorded in the proof steps for independent
review.

## Where the brief, the DAG or earlier work was wrong

No false statement or definition repair was needed. The original plan duplicated
already available normalized quotient/Koszul comparison work and transported
constructibility through more completion comparisons than necessary. Its unit has
no realized proof steps to bypass. The new route retains the actual ordinary tensor,
quotient augmentation, intrinsic unit and naturality for arbitrary arrows.
The quotient/Koszul comparison itself does not need separatedness, but its original
separatedness parameter is retained to preserve its public signature.

## Second reading by Y8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
