## What changed

Proved `WeilConjectures.SfProEtaleProjection.integralDomains` in
`Sheaf.Paper.SfProEtaleProjectionFormula`. The public statement, all definitions,
and all public imports are unchanged. Six private proved helpers supply good
K-flat representatives, tensor-model transport, ordinary pullback transport,
coefficient-prime invertibility, and finite dimension.

The tensor proof compares the supplied model with the existing signed K-flat
model and applies `constructibleTensorCompletion`, completed-tensor
constructibility, and the canonical completion-unit criterion. The pullback
proof identifies the actual scalar maps by their finite projections, transports
module pullback by uniqueness of left adjoints, and uses uniqueness of unbounded
left derived functors. The normalized compact-support realization supplies the
constructible image, without separated structure maps on X or Y.

Updated the sketch node with these domain-proof steps and their dependencies;
retained all planned steps for the still-open projection theorem. No source-library
module was edited and no new public statement or definition was introduced.

Validation: the pruned module compiled cleanly with `lcompile.py` in 40.5 seconds.
All seven new proof imports pass `import_direction.py may`; the node dependency
closure has no cycle. The existing public signatures and definition bodies were
compared against the shared source and are unchanged.

## Proved and sorry left

Closed one of the two original holes:
`WeilConjectures.SfProEtaleProjection.integralDomains`
(node `sk-thm-sf-pf-proetale`).

One original hole remains:
`WeilConjectures.sf_proetale_projection_formula`
(nodes `sk-thm-sf-pf-proetale` and `thm-sf-pf-proetale`). Its statement and proof
placeholder are unchanged. No holes were added or split off. This is a partial
proof delivery, not a claim that all four projection-formula stages are proved.
The imported named results may themselves remain open, as intended in stage 3.

## No longer needed

Removed unused proof imports:

- `Sheaf.AlgebraicGeometry.FiniteCompactProjectionFormula`
- `Sheaf.Paper.BasicOperationsCoefficientReduction`
- `Sheaf.Paper.ComparisonTorAmplitude`
- `Sheaf.Paper.ExchangeProjectionSuppliedDomains`
- `Sheaf.Paper.FiniteTorAmplitudeSites`
- `Sheaf.Paper.IntegralResidueTor`
- `Sheaf.Paper.ProEtaleConstructibleOrigin`
- `Sheaf.Paper.SfIntegralConstructible`
- `Sheaf.Paper.SfRationalizationKaroubi`
- `WeilConjectures.Compactification.Noetherian`
- `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`
- `WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Rational`
- `WeilConjectures.SixFunctors.Etale.Derived.ReductionConservative`

These are not used by the completed domain proof. Some remain available through
required public imports, and several are still mathematical dependencies of the
open projection theorem. Consequently no node or module is withdrawn or claimed
to be globally pruned; the original four-stage proof dependencies and unit route
are retained. The domain proof does not need finite etale-origin witnesses, the
finite projection formula, discrete integral projection, rational projection,
or field localization: it only types the actual integral map.

## Where the brief, the DAG or earlier work was wrong

The existing adic and field projection declarations in the adopted etale source
library use discrete coefficient presentations and do not directly instantiate
the completed coefficient sheaf and map in this module. The completed-domain
proof therefore uses the existing genuine completed tensor, ordinary/completed
pullback, completion-unit locality, and normalized compact-support statements.
No upstream statement is removed or weakened, and the projection theorem is
left open rather than justified by an incompatible discrete statement.

The finite projection transport and its bounded-below endpoints were explored,
but no unfinished private helper is included in the delivery. The outstanding
integral issue is reduction compatibility of the actual normalized projection
arrow; this is distinct from the domain facts proved here.

## Second reading by N4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
