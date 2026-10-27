## What changed

Filled the three preliminary theorem proofs in `Sheaf.Paper.ChartTargetOpenDescent`.
The affine integration mate is invertible by the existing affine-line counit theorem,
tower induction and the private affine-unit adjunct theorem imported with `import all`
from `Sheaf.AlgebraicGeometry.VectorIntegrationMate`. No duplicate adjunct or
compactification construction is added. The geometric dictionary comes from
`affineTargetDiagonalDnc`, and the restricted etale chart is constructed by the
universal property of the actual Cartesian affine tower square. The remote delivery compile accepted the proofs in 15.8 seconds; its style warnings
were corrected by using `let` for proposition-valued local instances.
Existing statements,
definitions, public imports and the unit route are unchanged.

## Proved and sorry left

Closed three of the original four holes:

- `WeilConjectures.PurityFiniteSetting.chartTargetAffineMate_isIso`.
- `WeilConjectures.PurityFiniteSetting.chartTargetGeometry`.
- `WeilConjectures.PurityFiniteSetting.chartTargetRestrictedChart`.

One original hole remains, unchanged:
`WeilConjectures.PurityFiniteSetting.chartTargetOpenDescent`
(node `lem-pur-chart-target-open-descent`). Its docstring and node retain the complete
six-step descent argument. No holes are added or split off. These are proofs from
existing library declarations, some of whose transitive dependencies remain open.
The Cartesian construction includes d=0 and empty target/source opens, and the mate
argument imposes no absolute separatedness or positive-rank assumption.

## No longer needed

No mathematical node or module is withdrawn. The five-part final descent theorem
is still open, so its original dependency plan is retained. The three completed
preliminary proofs use existing lower declarations directly. Removed unused direct
proof imports (these are not claims that the pending descent argument has been pruned):

- `Sheaf.Paper.ChartCartesianDomain`.
- `Sheaf.CategoryTheory.LocalizedModuleExactForSystems`.
- `Sheaf.Paper.DualizingSigmaCocycleLocality`.
- `Sheaf.SecSmoothPurity.FiniteEtaleDualizingNormalization`.
- `Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`.
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HomCoverGluing`.


## Where the brief, the DAG or earlier work was wrong

The existing private `affine_unit_adjunct_isIso` already supplies the categorical
integration-mate step, and `affineTraceMap_isPullback` already supplies the tower
Cartesian square. The DAG now records these actual uses for the preliminary
proofs. No statement error or unit-route change was found. This is a partial
module delivery, with the main descent theorem still pending, not a proof of all
five final clauses.

## Second reading by X3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
