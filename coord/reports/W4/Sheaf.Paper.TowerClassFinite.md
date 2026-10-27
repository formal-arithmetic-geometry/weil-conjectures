## What changed

Filled the three proofs in `lean/Sheaf/Paper/TowerClassFinite.lean`, preserving
all theorem statements, public imports, and normalization formulas.
Added the proof-only import `Sheaf.Paper.FiniteTateLineUniversal` for the already
proved tensor universal property. Updated the owning node
`def-sp-tower-class-finite` with the actual three-step argument and dependency.

The forgetful exactness proof uses the existing finite-limit and finite-colimit
instances. The integer quotient is constructed by sheafifying integer casts;
its normalization follows from the sheafification unit equation and uniqueness
from sheafification extensionality. The root map is the transpose of the identity
of the finite Tate line under its existing Hom equivalence. Its scalar-one
formula gives the required pure tensor, and pointwise equality gives uniqueness.
Neither construction assumes a nonempty scheme or a nonzero coefficient ring.

Profiling identified the pre-existing `FiniteChernNormalization` definition
as the slow declaration; the unchanged diagonal consumer also timed out.
The generic `forgetEvaluatedArrow` and `kummerComposite` now explicitly state
their already inferred result types, with unchanged binders and composite
bodies. The normalization binds its compared arrows locally and reuses the
existing `evaluatedChern` definition. Unfolding the wrappers and reducing the
local lets gives exactly the previous normalization formula. A profiled item
check passed in 49.2 seconds. The change record is
`coord/changes/W4-tower-class-finite-normalization-types.md`; it inventories
users and the three direct importers checked against the changed file.

Validation: the final item and all three unchanged direct importers passed
`lcompile.py --all`. The temporary importer copies were then removed. The
delivered item has no development profiling options and no `sorry`.

Searches through msearch LeanFinder, Loogle, and grep found Mathlib's finite-limit
preservation instance. Searching the adopted library found the proved
`SheafOfModules.preservesFiniteColimits_toSheaf` and searching the project found
`finiteTateLine_universal`; these supply the short route. No new statements were
needed, and no unit-level step is bypassed.

## Proved and sorry left

Closed all three original holes (namespace
`AlgebraicGeometry.ProEtale.SpTowerClasses`):

- `finiteForget_exact`;
- `finiteQuotient_existsUnique`;
- `finiteRootMap_existsUnique`.

All belong to `def-sp-tower-class-finite`. Zero holes remain in the item, and
zero holes are added anywhere. The two existing choice-based definitions now
refer to proved unique-characterization theorems. Additional changes annotate
inferred wrapper result types and refactor the
normalization into a definitionally equal expression, as described above.

## No longer needed

None. No import was removed, no module was withdrawn, and the node had no
previous proof dependencies to prune. The projective public import and the
unit's Chern-class route are preserved.

## Where the brief, the DAG or earlier work was wrong

The owning definition node had no recorded proof steps or proof dependencies
for its three auxiliary theorems. Its proof record now describes the existing
forgetful exactness instances, sheafification of integer casts, and the finite
Tate-line universal property. No statement correction was necessary.

## Second reading by W4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
