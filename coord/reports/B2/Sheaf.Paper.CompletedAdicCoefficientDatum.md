## What changed

Completed all nine proofs in `Sheaf.Paper.CompletedAdicCoefficientDatum`.
Finite-ring commutativity uses local sheafification sections; completed-ring commutativity
uses jointly injective limit projections. The finite-module transition is constructed from
its section formula and the cone equation. The tower derives from the stated K-flat
resolution and resolving-class theorems. Restriction exactness follows through abelian
sheaves. The finite reduction comparison uses a natural restricted-extension/tensor
isomorphism and a proved comparison on resolving models. The normalized ordinary
adjunction proves balancing and its uniqueness. Projection composition is cone naturality.

Added only private proved helpers and private proof imports. Existing public signatures,
definitions, attributes and public imports are unchanged. Updated the proof and dependencies
of `def-weil-pbc-adic-coefficient-datum` to describe this completed-coefficient implementation;
its existing attachment to the other published implementation remains unchanged. The unit
route is preserved. No consumer adaptations are needed. The scoped proof-command record is
`coord/changes/B2-completed-adic-private-proof-scopes.md`; it documents the static gate
classification and lists all transitive consumers with unchanged interfaces.

Validation: the final single-file server compile through `lcompile.py` passed without
warnings in 42.5 seconds after import cleanup. The delivery tool performs the final compile
and preflight checks. The first preflight requested the scoped-command change record;
that record is included in this packet.

## Proved and sorry left

Closed all 9 original holes (namespace `AlgebraicGeometry.Scheme`):

- `completedAdicRing_mul_comm`
- `completedAdicFiniteModuleStep_exists`
- `completedAdicOrdinaryTower_additive`
- `completedAdicReduction_exists`
- `completedAdicFiniteRing_mul_comm`
- `completedAdicRestriction_exact`
- `completedAdicFiniteReduction_comparison`
- `completedAdicBalance_exists`
- `completedAdicCommProjection_comp`

Zero holes remain in the item; zero holes were added or split off. Existing imported
theorems are used as the stage-3 dependency interface permits. This is a proof of the item
from those declarations, not a claim that all transitive dependencies are sorry-free.

## No longer needed

No original import, declaration, module or planned dependency is withdrawn. During proof
cleanup the candidate private imports `Sheaf.Algebra.Homology.KFlatTensorQuasiIso`,
`Mathlib.CategoryTheory.Sites.LocallyBijective` and
`WeilConjectures.Algebra.Homology.HomotopyCategory.Braided` were removed: the required
interfaces are already provided by the retained imports. The one-point specialization in
KFlatTensorQuasiIso is not used; the proof works with the general-site K-flat interface.
No global pruning is claimed.

## Where the brief, the DAG or earlier work was wrong

The main adic coefficient node is attached to `Sheaf.Paper.AdicCoefficientDatum`, while the
assigned companion module is directly attached only through the derived-reduction record
node. The companion's docstrings identify the same adic coefficient construction. This
packet preserves both attachments and records its proof route in the main node.

An earlier companion proof available in another sandbox referenced two absent comparison
modules. Those imports were not used: their needed categorical and tensor comparisons are
proved locally here. The current K-flat API is named `IsAcyclicTensorKFlat`.

## Second reading by B2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
