## What changed

Filled four supporting proofs in `Sheaf.Paper.ExtensionByZeroPunctual` without changing
any declaration signature or definition. Local finite type over the finite field
makes the target locally Noetherian, and Mathlib then supplies quasi-compactness of
its open immersion. `MorphismProperty.overPullbackMap` supplies the geometric-fibre
open immersion. Heart membership of a finite-stage Weil object follows separately
from its two rational standard-class witnesses.

The finite-stage Frobenius naturality proof uses the prescribed representative-map
formula for common-stage pullback. Naturality of the rational scalar comparison,
conjugated by the stage-transition comparisons, identifies the two representatives.
A proved private equality-transport helper handles the functor's prescribed object
coordinates; it introduces no new public interface.

## Proved and sorry left

Closed four of the six original holes:

- `WeilConjectures.zlOpen_quasiCompact`.
- `WeilConjectures.zlOpenFiber_isOpenImmersion`.
- `WeilConjectures.zlWeilStageSquare_naturality`.
- `WeilConjectures.zlWeilHeartStage_mem`.

The original holes in `WeilConjectures.zlOpenWeilPull_isRightAdjoint` and
`WeilConjectures.extensionByZero_punctual` remain unchanged,
attached to `lem-zl-extension-by-zero-punctual`. Its complete source and proof plan
remain in its existing docstring and node. No holes were added or split off. This
is a partial delivery of the supporting proofs, not completion of the combined
fibre and weight theorem. The proofs use existing named dependency theorems that
are themselves still open; no claim of an axiom-free transitive closure is made.

## No longer needed

No DAG node or module is withdrawn: the combined theorem remains open, so its
planned dependencies remain needed. No change to the unit route is proposed.

## Where the brief, the DAG or earlier work was wrong

No statement repair was needed. The geometric facts can be proved directly from
Mathlib, and the finite-stage heart membership follows immediately from the two
standard-class definitions. The existing normalized open-unit and t-exactness
statements supply the categorical data required for the right-adjoint proof;
their being open theorems does not prevent using them at this stage.

The shorter-route searches used LeanFinder for quasi-compact open immersions,
Loogle for open-immersion base change, the launcher grep search, and local `rg`
for the actual common-stage representative formula and adjunction APIs.

## Second reading by W9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
