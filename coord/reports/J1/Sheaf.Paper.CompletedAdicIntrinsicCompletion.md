## What changed

Constructed the completed-coefficient Koszul degree-zero unit from the compatible
sheafified pure tensor of scalar units, using the unit-module/sections equivalence.
Proved the tensor-unit differential identity in an arbitrary additive monoidal
category and specialized it to the completed coefficient sheaf. Proved the raw,
constant-sheaf and completed-coefficient transition identities, the resulting
product one-minus-shift relation, and the shifted-cone chain-map identity.

Proved representative independence by constructing the tensor, product and shifted-cone
functors, showing they preserve quasi-isomorphisms, and localizing the functor and
its natural unit. The representative comparison is the composite of the localization
factorization isomorphisms and the descended functor applied to the two representative
identifications. Naturality gives the required unit equation.

Added private proof imports of `ConstantModuleKFlat`,
`ChangeOfRingsKFlatAllIndependentCoefficients`, `BoundedFlatIndependentCoefficients`,
`ProEtaleCountableProductsExact`, `ExteriorPower.Basis`, the source mapping-cone
acyclicity API, and `DerivedCategory.TowerLimit`. The construction also privately imports
`CompletedIntegralCoefficients` for its explicit coefficient-universe instance. Updated
the shared blueprint node's
proof and dependency metadata to record this realization while retaining its existing
Lean attachment and the dependencies used by the other realization.

Separated the self-contained construction into
`Sheaf.Paper.CompletedAdicKoszulConstruction` after profiling and optimizing the
large definitional comparisons. The original module publicly imports it. All existing
public declaration names, signatures, definition bodies and original public imports
are preserved; representative independence remains in the assigned module. New helpers
are private and proved. No source-library module is changed. Scoped local irreducibility
keeps the large
completed-ring and standard-derived-category constructions from unfolding in proofs;
explicit type changes avoid expensive instance-type comparisons.

The arguments include the rank-zero Koszul complex and the zero coefficient ring:
no generator is selected and no nonzero scalar is cancelled. The complex being
completed may be unbounded; only the Koszul tensor factor is required to be bounded.

Final verification: the construction module compiled cleanly in 43.4 seconds and
this item in 51.8 seconds. All five direct importers compiled unchanged against the
final delivered definitions (12.5 to 45.9 seconds). Their temporary source copies
and the axiom-check module were removed from the packet. `#print axioms` for each
of the four closed declarations reports exactly `propext`, `Classical.choice` and
`Quot.sound`, with no `sorryAx`.

## Proved and sorry left

Closed:

- `AlgebraicGeometry.Scheme.completedAdicKoszulUnitZero_exists`.
- `AlgebraicGeometry.Scheme.completedAdicKoszulTensorUnitF_comm`.
- `AlgebraicGeometry.Scheme.completedAdicKoszulUnitF_comm`.
- `AlgebraicGeometry.Scheme.completedAdicIntrinsicCompletion_comparison`.

The first three proofs now live in `CompletedAdicKoszulConstruction`; the comparison
proof remains in the assigned module. All four original holes are closed. There are
zero remaining holes in the item and
zero holes added. All four declarations realize the existing blueprint node
`def-weil-pbc-intrinsic-completion`; the new node records the relocated construction
segment. No unfinished statement was split off.

## No longer needed

No original public import, module or DAG node is removed. The unit route is retained.
The item uses the strictly smaller `CategoryTheory.isKFlat_constantModule` statement
from `Sheaf.CategoryTheory.ConstantModuleKFlat` instead of importing the full derived
scalar-extension comparison module. That larger module remains needed by the other
realization attached to the shared node, so its dependency is retained there.

Removed exploratory direct proof imports of `BifunctorMappingCone`,
`ModuleCat.Projective`, `DerivedCategory.HomologySequence`,
`GrothendieckAxioms.Basic`, and `HomotopyCategory.MappingCocone`: their APIs are
already publicly available through the item's existing imports. No pruning of
library modules is claimed.

## Where the brief, the DAG or earlier work was wrong

The item has no direct `lean.module` attachment in the DAG: its docstrings cite
`def-weil-pbc-intrinsic-completion`, whose existing attachment is to
`Sheaf.Paper.IntrinsicCompletionCompleted`. That distinct module and its attachment
are preserved. Its proved helpers also provide the corresponding abstract tensor
and localization arguments; they are private, so the needed calculations must be
reproved locally for the completed coefficient construction used by this item.

## New nodes

`lem-weil-pbc-completed-adic-koszul-unit-chain-map` records the existing chain-map
statement and its construction segment in `CompletedAdicKoszulConstruction`. Its
proof constructs the normalized scalar and degree-zero unit, checks the tensor
differential and transition identities, and checks the shifted-cone differential.
It introduces no new mathematical statement or hole. The module separation and
unchanged public headers are recorded in
`coord/changes/J1-completed-adic-koszul-construction.md`.

## Second reading by J1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
