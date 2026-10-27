## What changed

Proved `AlgebraicGeometry.ProEtale.SpCoordinateAdjunction.tower_coordinate_adjunction`
from the existing `tower_coordinate_adjunction_models`. The latter is already the
Lean attachment of `lem-sp-tower-coordinate-adjunction`. Eliminate its `Nonempty`
proof into the proposition `Construction`, provide all 29 dependent witnesses in
order, and finish with the record's chart-counit equation. All witness types and
the final equation were compared against the existing record: they agree verbatim
apart from the existential/record syntax. No data-valued definition chooses a
witness. The definition and theorem signatures remain unchanged.

Added one private proof import,
`Sheaf.Paper.SmoothPurityTowerCoordinateAdjunctionModels`. All six public imports
are retained. The existing DAG node already records the Models theorem and its
mathematical proof route, which this compatibility theorem reuses; neither that
attachment nor the unit route is changed. There are no new nodes.

Validation: the required remote `lcompile.py` single-file compile passed in
31.0 seconds, exit code 0, with no diagnostics. Lines are at most 100 characters.

## Proved and sorry left

Closed the one local hole in
`AlgebraicGeometry.ProEtale.SpCoordinateAdjunction.tower_coordinate_adjunction`.
The item now has zero `sorry`; zero holes were added or split off.
The existing imported
`AlgebraicGeometry.ProEtale.SpCoordinateAdjunction.tower_coordinate_adjunction_models`
still has its pre-existing hole, owned by `lem-sp-tower-coordinate-adjunction`.
This removes a duplicate local existence obligation and does not claim to prove
the geometric construction independently of that existing theorem.

## No longer needed

Removed these six private imports, since this module's proof only unpacks the
existing Models theorem:

- `Sheaf.Paper.PurityFiniteKummerLevel`
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`
- `Sheaf.Paper.AmbTateRootProjectionReduction`
- `Sheaf.AlgebraicGeometry.FiniteRootSiteComparison`
- `Sheaf.AlgebraicGeometry.FiniteEtaleTwistLine`
- `Sheaf.Paper.RootTowerFiniteTensor`

Their mathematical results remain part of the existing Models theorem's proof
route. No DAG dependency or entire module becomes globally unnecessary. All
normalized witnesses, finite comparisons, successor and zero equations, and
counit equations are retained, including the cases d = 0 and n = 0.

## Where the brief, the DAG or earlier work was wrong

The brief names the older existential-presentation module, but the mathematical
node `lem-sp-tower-coordinate-adjunction` now attaches to
`SmoothPurityTowerCoordinateAdjunctionModels.tower_coordinate_adjunction_models`.
The older module still contained a duplicate existence hole. Reusing the already
stated record theorem is the shortest route. No new renamed existence theorem
was introduced. The definition-owner node
`def-sp-normalized-coordinate-construction` correctly continues to own
`Construction`.

## Second reading by F4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
