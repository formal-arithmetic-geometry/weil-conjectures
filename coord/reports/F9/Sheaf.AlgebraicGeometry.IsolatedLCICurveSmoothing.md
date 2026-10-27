## What changed

The statement of `AlgebraicGeometry.isolated_lci_curve_smoothing` is unchanged.
Its proof now enumerates the exceptional closed points, obtains the prescribed
local Fitting smoothings, algebraizes their compatible quotients, applies a
separate local-to-global Fitting criterion, and glues generic smoothness over a
proper open cover. The proof explicitly transports Laurent series to the
localization Away t required by the statement.

Added `Sheaf.AlgebraicGeometry.IsolatedCurveLocalAlgebraization`, with a complete
proof of `AlgebraicGeometry.isolated_curve_local_algebraization` from the existing
formal-lifting and proper formal-algebraization declarations. It constructs the
polynomial/power-series truncation equivalences, quotient algebra structures,
flatness and transition maps, and transports the finite-jet stalk comparisons
including their scalar compatibility. It does not assert equality of unreduced
local rings.

Added `Sheaf.AlgebraicGeometry.IsolatedCurveLocalFittingCriterion` for the
Cohen--Macaulay dimension partition and reduction to the separate
local-to-global Fitting calculation of Tag 0E7Y. The partition is fully proved; it and the uniform-exponent reduction compile.
The new `Sheaf.AlgebraicGeometry.IsolatedCurveLocalFittingBounds` contains a separate
source argument about an already given algebraized family; its conclusion is
finite-jet ideal membership on given pure pieces. The proved criterion supplies
the partition. The item combines these conclusions with the
existing finite-jet smoothness theorem by an explicit open-cover proof.

Only proof imports were changed in the item. All existing public imports and the
existing theorem signature are preserved. No source-library module, definition,
target, instance, or other group's module was changed.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.isolated_lci_curve_smoothing`
(`lem-sfb-isolated-lci-curve-smoothing`). The item now has zero `sorry`.

The new theorems
`AlgebraicGeometry.isolated_curve_local_fitting_criterion`
(`lem-sfb-isolated-curve-local-fitting-criterion`) and
`AlgebraicGeometry.isolated_curve_local_algebraization`
(`lem-sfb-isolated-curve-local-algebraization`) are fully proved and have zero holes.
All private helpers in these files are fully proved.

Added exactly one hole:
`AlgebraicGeometry.isolated_curve_local_fitting_bounds`
(`lem-sfb-isolated-curve-local-fitting-bounds`). Its entire proof is the named
public theorem's `by sorry`; there are no holes in definitions or private helpers.
It has a source, a complete proof in words, and a new DAG node.

Thus this packet closes one original hole and adds one strictly smaller source
result: it is a decomposition, with net zero holes closed before the ledger's
proof-dependency baseline accounting. Existing imported declarations are used as
stated, including those whose proofs are still unfinished in the library.

## No longer needed

Removed these unused direct proof imports from the item:

- `WeilConjectures.AlgebraicGeometry.EquidimensionalFibreOpenPartition`
- `WeilConjectures.AlgebraicGeometry.EquidimensionalOpenLocalDimension`
- `WeilConjectures.RingTheory.ClosedPointDimensionLocalRing`
- `Sheaf.AlgebraicGeometry.Morphisms.ProjectiveImpliesProper`
- `Sheaf.RingTheory.PresentationFittingIdeal`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.SmoothFiber`
- `WeilConjectures.AlgebraicGeometry.Modules.Differentials`
- `Sheaf.AlgebraicGeometry.FittingIdealSheaf`

The formal-lifting, algebraization, quotient-flatness and Fitting calculations are
recorded at the helper nodes that actually use them. In particular, moving them
from the parent's direct proof dependencies does not claim they are globally
unused or withdraw their modules.

The direct special argument for a separate zero-dimensional smoothing and a
common projective-space embedding of a disjoint union are unnecessary: the
formal-lifting and algebraization statements already apply in dimension at most
one, and the supplied family is partitioned afterwards. Consequently the direct
uses of `lem-pc-flat-field`,
`lem-weil-pbc-finite-type-noetherian-finite-presentation`, and
`lem-kun-projective-implies-proper` are omitted; the last is also redundant with
the existing `IsHProjective.isProper` instance. `def-kun-projective` remains a
statement dependency but is not an additional proof step. No module is withdrawn.

The following obsolete top-level tool approvals were removed from the parent,
keeping the remaining approval in order. These are direct-route removals; several
remain necessary in the helper proofs:
`lem-pc-flat-field`,
`lem-weil-pbc-finite-type-noetherian-finite-presentation`,
`lem-sbc-cohen-macaulay-equidimensional-fibre-pieces`,
`lem-weil-pbc-closed-immersion-proper`,
`lem-sbc-equidimensional-open-local-dimension`,
`lem-weil-pbc-closed-point-dimension-local-ring`,
`lem-weil-pbc-zariski-lemma`, `lem-weil-pbc-flat-module-base-change`,
`lem-kun-projective-implies-proper`,
`lem-weil-pbc-kahler-differentials-localization`,
`lem-weil-pbc-kahler-differentials-base-change`,
`lem-trf-fitting-ideal-independence-base-change`,
`sbc-lem-smooth-criterion`, `lem-sc-smooth-omega-finite-locally-free`, and
`lem-weil-pbc-finite-type-over-noetherian`.

## Where the brief, the DAG or earlier work was wrong

The original dependency declarations supply the formal deformation system and
its algebraization, but not the glue identifying polynomial truncations with
power-series truncations and preserving the scalar maps on stalks. That glue is
now proved explicitly in the algebraization helper. The remaining local Fitting
argument also required an explicit interface: an abstract ring equivalence alone
would not determine the differential Fitting ideal without its scalar equation.
The new finite-jet bound includes that equation. The CM partition was then
proved from the existing unrestricted fibre CM openness and relative-dimension
partition declarations, using private transport helpers from the now-proved
finite-jet generic-smoothness module through `import all`. Its generic-smoothness
theorem is not used in this partition proof. The unit route is unchanged.

The launcher interrupted this session for a provider failure and later paused it
to shorten the compile queue. The original sandbox reference clock had start
identifier `1792749376.1673694`; after resume the sandbox metadata instead has
start identifier `1792775428.188266`. These metadata were not edited by the worker.
This records the clock reset while proof work continues under the original brief.
The first delivery invocation was refused before pushing by the split-off policy:
the reset clock reported 56 of 120 minutes, with a 72-minute threshold. Afterwards
proof work continued: the uniform exponent was made explicit, and the final
finite-jet witness was constructed in the criterion.

## New nodes

`lem-sfb-isolated-curve-local-algebraization`:
`dag/nodes/sec-six-functors-basics/lem-sfb-isolated-curve-local-algebraization.json`.
A proved extraction of the middle paragraph of Stacks Tag 0E7Y, using the existing
formal-lifting and proper formal-algebraization nodes, with explicit truncation
and stalk transport. Its module has no holes.

`lem-sfb-isolated-curve-local-fitting-criterion`:
`dag/nodes/sec-six-functors-basics/lem-sfb-isolated-curve-local-fitting-criterion.json`.
A proved extraction of the CM dimension partition from the first paragraph of
Tag 0E7Y, followed by application of the separate finite-jet Fitting bound. It
uses properness over the local base twice and transports depth and local
dimension through actual stalk and scheme isomorphisms. It has zero holes.

`lem-sfb-isolated-curve-local-fitting-bounds`:
`dag/nodes/sec-six-functors-basics/lem-sfb-isolated-curve-local-fitting-bounds.json`.
Only the final paragraph of Tag 0E7Y: on given proper pure pieces, finite local
bounds imply global differential Fitting membership on their finite jets. It
has no lci or dimension-bound hypothesis and asserts no partition. This is
the only new hole. The proved criterion also replaces all local exponents
by their sum E, proving uniformity using ideal multiplication. The remaining
lemma takes that uniform exponent and asserts membership on the explicit jet
n=E+1; the criterion proves its positivity and supplies this exact witness. Edge cases
include an empty marked list (the sum is zero and n=1), an empty family, empty pure
pieces and exponent zero. The argument uses no generic-smoothness conclusion.

No existing statement or definition changed, so no change record is needed.

## Second reading by F9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
