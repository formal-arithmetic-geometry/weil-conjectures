## What changed

Replaced `AlgebraicGeometry.ProEtale.SpTowerClasses.linePullback_nonempty` by a proof
from the existing normalized finite comparisons and ordinary system-isomorphism
assembly, with one strictly smaller horizontal-compatibility obligation.

The proved public `finiteLineComparisons_exists` theorem in the new module
`Sheaf.Paper.TowerClassFiniteLineComparisons` pulls the global unit into the residue fields of both schemes,
uses `spFiniteTwists_cartesian` for each actual finite coefficient quotient, and
identifies its root direct image with `restrictRoot`. The private `adjoint_evaluation`
proof derives evaluation of arbitrary ordinary transposes from
`SpTowerShriek.geometry_unit_evaluation` and naturality. Its cancellation argument
is first proved over abstract categories and functors in the private
`adjoint_evaluation_of_unit` helper, avoiding unfolding of concrete geometry data. The main proof conjugates
the finite isomorphisms, assembles them using `systemIsoOfEvaluation_exists`, and
proves the required tensor normalization by cancellation and naturality of the
finite adjunction. No isomorphism or scalar-extension data is defined by choosing a
witness from a new unproved existence theorem.

The finite proof is isolated so the main file imports its result without directly
importing the large signed-twist proof module.

Added `Sheaf.Paper.TowerClassLinePullbackHorizontal`, which assumes a family of
already constructed finite isomorphisms and their explicit tensor formulas and
asserts only their horizontal transition equation. It constructs neither finite
isomorphisms nor a system isomorphism and states no tower adjoint formula. Updated
the assigned node's proof and dependencies to match this argument.

Validation: all three modules compiled with lcompile.py. The final main module
compiled cleanly in 9.0 seconds; the two supporting modules compiled cleanly in
54.1 and 55.1 seconds. All profiler options are removed.

## Proved and sorry left

Closed the one original hole in
`AlgebraicGeometry.ProEtale.SpTowerClasses.linePullback_nonempty`
(node `lem-sfb-tower-class-line-pullback-existence`). The finite comparison
construction, evaluated-transpose identity, assembly, and final tensor formula
are proved in Lean. The additional public theorem
`AlgebraicGeometry.ProEtale.SpTowerClasses.finiteLineComparisons_exists`
is proved without a new hole.

Added one hole:
`AlgebraicGeometry.ProEtale.SpTowerClasses.linePullback_components_horizontal`
(node `lem-sfb-tower-class-line-pullback-horizontal`). This leaves precisely the
horizontal compatibility calculation for the already normalized finite
comparisons. It is a decomposition: one original hole closed, one strictly smaller
hole added, net zero holes. There are no holes left in the assigned module and no
holes in definitions. The imported existing theorems retain their own obligations.

## No longer needed

No existing module is withdrawn and no public import is removed. The original
public import of `TowerClassTensorPullback` is still needed by the unchanged theorem
signature. The proof does not use `q`, `k`, `nY`, or `nX`: the actual ordinary scalar
models and normalized finite root comparisons already supply the necessary
finite transport. Thus `def-sfb-tower-class-tensor-pullback` and
`def-sp-tower-class-chern` are removed as direct proof dependencies of this node;
their statement dependencies, definitions, and all unit routes remain intact.
The tensor-pullback structure is not required to prove this root-line transport.
No formerly needed Lean proof import was present in the original module.

## Where the brief, the DAG or earlier work was wrong

The prior proof plan combined finite comparison construction, horizontal
compatibility, assembly, and normalization in one paragraph citing mostly
definitions. Finite comparisons are already available from
`spFiniteTwists_cartesian`; system assembly is already proved in
`systemIsoOfEvaluation_exists`; the ordinary unit normalization is already proved
in `geometry_unit_evaluation`. The delivery uses these rather than restating their
existence. The only new obligation is the transition equation missing from the
existing finite-line evaluation API.

The new equation includes arbitrary morphisms, n = m, empty charts, and the zero
coefficient ring: identity transitions give the identity square, and on zero
objects both sides are the unique map. No finiteness hypothesis on f or additional
normalization hypothesis is introduced. The unit's statement and route are unchanged.

## New nodes

`lem-sfb-tower-class-finite-line-comparisons` records the proved specialization of
`spFiniteTwists_cartesian` to every actual tower coefficient quotient. It includes
the explicit coefficient/root formula and makes no horizontal assertion. Its
proof maps the global unit into residue fields and identifies the given root
restriction by its unique section formula.


`lem-sfb-tower-class-line-pullback-horizontal` is the horizontal square for the
explicitly conjugated finite comparisons. Its source is the scalar-extension
paragraph of the current classes blueprint and the explicit transition
calculation in the assigned node. Its complete proof in words explains the
coefficient-quotient/root-power tensor formula, transport of
`ordinaryPullTransition`, the constant coefficient naturality square, and
`map_pow`. No shared interface changes or change records are required.

## Second reading by H5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
