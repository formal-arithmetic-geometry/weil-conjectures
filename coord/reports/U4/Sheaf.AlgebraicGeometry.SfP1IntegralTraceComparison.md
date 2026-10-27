## What changed

Replaced the hole in `AlgebraicGeometry.Etale.SfP1Transport.traceComparison` by a
complete assembly proof. Its signature and public imports are unchanged. The
new proof import is `Sheaf.AlgebraicGeometry.SfP1ProjectionTraceTransport`.

The assembly extracts the trace clause of the supplied base-change hypothesis at
q:P → S. It factors the chart map, composes that equation with the trace over P,
and substitutes the extracted trace equation. Preservation of composition by Li*
and associativity then give the conclusion using transport of inverse exchange.
The local equation `hchart` is proved, not assumed.

Added `SfP1ChartExchange`, which constructs `projectionExchange` explicitly as
inverse twist comparison followed by inverse proper exchange. It also proves
`projectiveProjectionSquare` for both Boolean choices. Its remaining statement
`chartExchange` is an equation before any trace is applied: it has no family d,
base-change hypothesis, trace arrow, isomorphism i or supported class.

Added `SfP1ProjectionTraceTransport`, whose remaining equation is natural in an
arbitrary arrow τ. It contains no chart map, splitting family, splitting trace,
base-change hypothesis or supported class. Thus the two remaining statements are
separate geometric steps, rather than renamed copies of the assigned theorem.
The first compares chart and product exchange before a trace; the second compares
ordinary and compact-support product exchange under a presentation isomorphism.
The actual family base-change step is carried out in the assigned module.

The two new statements and the original node have proof plans matching these
steps. All definitions have explicit bodies. No existing module other than the
assigned module is changed, and no shared interface is changed.

## Proved and sorry left

This is a decomposition, not a closed proof of the geometric comparison.

One original hole is replaced by a complete assembly proof:
`AlgebraicGeometry.Etale.SfP1Transport.traceComparison`
(node `lem-sf-p1-integral-trace-comparison`). There are zero sorries in the
assigned module. The helper `projectiveProjectionSquare` is proved.

Two new holes remain, each the whole proof of a public theorem in its own module:

- `AlgebraicGeometry.Etale.SfP1Transport.chartExchange`
  (`lem-sf-p1-chart-exchange`, `Sheaf.AlgebraicGeometry.SfP1ChartExchange`).
- `AlgebraicGeometry.Etale.SfP1Transport.projectionTraceTransport`
  (`lem-sf-p1-projection-trace-transport`,
  `Sheaf.AlgebraicGeometry.SfP1ProjectionTraceTransport`).

Validation: `lcompile.py --all` succeeds for all three modules. Final single-file
times were 35.6 s, 36.4 s and 36.7 s. The original theorem signature and public
imports were also compared with the shared source and are unchanged.

Counts: one original hole decomposed; two holes added; net holes closed minus
added is -1. No independent original hole is closed without a new obligation.
The empty base, zero coefficient ring and both Boolean projection conventions
were checked against the new statements: the new maps are inverse isomorphisms
and canonical composites, with no nonemptiness or positivity assumption.

## No longer needed

No original import is removed and no module is withdrawn or globally pruned.
The original direct proof dependencies on abstract ringed derived monoidal
comparisons, finite twist pullback and proper torsion-ring base change now occur
in the two geometric steps; they are not claimed to be unnecessary mathematics.
The assigned module directly uses the family base-change definition and the two
new comparison statements. Its node records exactly this assembly route.

## Where the brief, the DAG or earlier work was wrong

The original plan combined several different comparison interfaces in prose.
`ringedDerivedMonoidalComparisons` supplies an abstract ringed-site system; its
statement does not immediately identify the concrete etale shifted-line,
chart-unit and compact-support comparison maps used here. The existing
`isIso_ordinaryFiniteP1Exchange` proves invertibility; its private mate-transport
argument explicitly only needs invertibility and cannot be used as a public
identity of those exchanges. The two explicit remaining equations record the
precise geometric comparisons needed by the assembly.

The apparent alternative `presentedFiniteP1Counit_baseChange` cannot be imported:
`tools/import_direction.py may` reports that its module already reaches this
item and would create a cycle. It also has an extra positive-exponent binder.
No unsupported import or changed hypothesis is used to bypass this.

Searches inspected source cube/pasting equations, ordinary finite twist uniqueness,
and the finite twisted-unit base-change proof, as well as Mathlib adjunction and
mate lemmas. These provide ingredients but no exact existing equation with these
endpoints. The unit route is preserved; no target or unit statement changes.

## New nodes

`lem-sf-p1-chart-exchange` records the chart/product exchange factorization before
any trace, in `SfP1ChartExchange`. Its docstring describes the chart equations,
mate pasting, triangle cancellation and normalized line comparisons.

`lem-sf-p1-projection-trace-transport` records ordinary-to-compact-support product
exchange under the specified isomorphism, natural in any τ, in
`SfP1ProjectionTraceTransport`. Its docstring describes proper forget-supports,
isomorphism and composition comparisons, the second-coordinate correction and
constant-unit endpoints.

Both inherit the original chapter and unit. Blueprint searches found no existing
node stating either exact equation. No change record is needed: existing
statements, definitions, attributes and public imports are unchanged.

## Second reading by U4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
