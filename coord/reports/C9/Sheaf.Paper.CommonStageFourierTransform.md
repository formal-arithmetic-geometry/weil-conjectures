## What changed

Completed all nine postponed theorem proofs in
`Sheaf.Paper.CommonStageFourierTransform`. No existing signature, definition body,
visibility, or docstring changed. Added proof-only imports of
`Sheaf.Paper.DerivedPullbackTensorIso` and
`Sheaf.AlgebraicGeometry.FrobeniusDetailed`.

The coefficient proofs use Mathlib's `charP_of_card_eq_prime_pow` and transport
units along the model's residue-field maps. The model projection equation uses
the existing Galois-map projection equation. Tensor/Frobenius naturality follows
from the existing specified common-stage natural tensor comparison applied to
`(f, identity)`, followed by functoriality of tensor with the fixed Weil map.
The affine geometry uses existing finite-type, affine and base-change instances.
The global-section characteristic proof constructs a section from the pair of
zero sections, proving nontriviality even in rank zero and for infinite coordinate
types; only the separate finite-type assertion assumes finitely many coordinates.

Updated the existing `def-fd-transform` node's proof, proof dependencies and proof
origin to record these arguments. Its statement, Lean attachment and unit route
are unchanged. The completed module compiled without warnings on the project
server in 13.5 seconds before the additional direct Frobenius proof import;
delivery validation recompiles the final file and checks its declarations.

## Proved and sorry left

Closed 9 original holes, all attached to `def-fd-transform`:

- `WeilConjectures.fourierModelPrime_isUnit`
- `WeilConjectures.fourierModelProjection_frobenius`
- `WeilConjectures.fourierTensorFrobenius_naturality`
- `WeilConjectures.fourierAffineModel_finiteType`
- `WeilConjectures.fourierAffineModel_quasiCompact`
- `WeilConjectures.fourierAffineModel_separated`
- `WeilConjectures.fourierSquareModel_geometry`
- `WeilConjectures.fourierSquareModel_characteristic`
- `WeilConjectures.fourierBaseCharacteristic`

Zero holes remain in the delivered module; zero holes added; zero split off.
The tensor proof uses the existing `derivedPullbackTensorIso` theorem, whose
own dependencies remain the responsibility of their existing items. This is a
proof from the project's recorded declarations, not a claim that the entire
transitive import closure is already free of `sorry`.

## No longer needed

None. No imports, nodes or modules removed. Each existing public import supplies
the preserved ordinary-etale or Weil transform interfaces or the definitions of
this module. Both new proof-only imports supply declarations used directly.
The existing node had no proof dependencies to prune; its new dependency list is
exactly the two existing nodes supplying the non-elementary proof steps.

## Where the brief, the DAG or earlier work was wrong

The existing definition node had an empty proof list despite recording nine
postponed verification theorems in its Lean attachment. The delivery fills those
proofs and records their dependencies. No false statement, definition repair,
forced adaptation, or new node was necessary.

## Second reading by C9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
