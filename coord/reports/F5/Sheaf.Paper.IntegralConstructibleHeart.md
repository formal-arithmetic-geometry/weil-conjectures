## What changed

Repair of reviewer C-26f9f, points D1 and 2. The local finite-model and duality
argument is proved in the item from `integralHeartLocalModel` at degree zero,
`singleFunctorCompHomologyFunctorIso`, `integralHeartDualizable`, and
`BraidedCategory.exactPairing_swap`. The stratification and every cover are retained
from the local-model theorem. The finite scalar module on a chart is the zeroth
homology of its finite free scalar complex.

Private helpers package the categorical conclusions with an explicit coefficient
monoid structure. Equality of the canonical and cached coefficient structures
transports those conclusions before the proof applies them to modules. Instance
removal is scoped to private helpers. The public theorem retains the cached instances. Its local clause now uses the
existing cached coefficient alias and stratum-complex abbreviation. This equivalent
type presentation is explicitly declared in the change record, taking the second
option in reviewer point 2. No shared coefficient construction is changed.
The proof commands are recorded in
`coord/changes/F5-integral-heart-proof-elaboration.md`.

## Proved and sorry left

The original hole in `AlgebraicGeometry.ProEtale.integral_constructible_heart`
(node `sk-lem-int-integral-heart`) is closed from existing detail declarations.
There are zero retained or added holes in the delivery. The rejected intermediate
`integralHeartStratifiedModels` is removed from the packet; no split is left.
No definition contains a hole. Existing holes in imported detail theorems remain
outside this delivery.

## No longer needed

The rejected proposed module `Sheaf.Paper.IntegralHeartStratifiedModels` and its
proposed node `det-int-heart-stratified-models-and-duals` are unnecessary: the item
now proves that argument itself. Neither has landed in the shared library, so this
packet creates neither. The direct proof import `Sheaf.Paper.IntegralModels` is
unnecessary because the detail declarations already incorporate the model criterion.
Its node remains a statement dependency; it is not globally withdrawn.
All four original public imports remain. `IntegralHeartDualizable` becomes public
because the statement uses its stratum-complex abbreviation. No existing module
is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The returned packet merely repackaged assertions (2)--(3), and changed the elaborated
public type by disabling coefficient instances at the public theorem. Both points
are repaired; the equivalent type presentation is declared rather than hidden. A locally irreducible private proposition prevents elaboration from
expanding the sheaf and derived-category constructions during coefficient transport.

The degree-zero homology is finite without a torsion-free hypothesis. The duality
theorem supplies the pairing in the opposite order from the item's conclusion;
braiding reverses it while retaining the two Tor bounds. The construction works for
the empty scheme, zero modules, and torsion modules. The unit route is unchanged.

## Second reading by F5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
