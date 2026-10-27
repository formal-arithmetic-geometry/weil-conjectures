## What changed

Proved `WeilConjectures.IntegralScalarExchange.rectangle_naturality` in
`Sheaf.Paper.IntegralScalarIsomorphismExchange`. The left-path proof pastes the
naturality squares of its three factors, using functoriality and a proved private
categorical composition lemma. Membership in the two-element set selects the path.

Added the constructed `rightTransformation`, and defined `right` as its component.
Its factors are the original scalar pullback, coefficient comparison and exchange,
in that order. The inserted functor associators have identity components, so its
components are exactly the original three-map composite. The right-path equation
is now this named transformation's naturality.

Made both completed paths' source and target explicit. These three definitions
and the naturality theorem locally select the canonical abelian structure and the
native `proEtaleRingModules_hasDerivedCategory` instance. The native and reduction
instances construct the same standard derived category. No instance registration
for importers changes. The left-path body, all hypotheses and all imports stay
unchanged. No other library module is adapted.

Updated the existing node's Step 6, proof origin and declaration list. No new nodes.
Change record: `coord/changes/H5-integral-scalar-path-naturality.md`.

The complete proof compiled in 20.3 seconds before removal of profiling options.
The final warning-free module and unchanged direct consumer
`Sheaf.Paper.ZlFrameworkOpenExchange` then both passed `lcompile.py --all`
(exit code 0). The temporary consumer copy was removed before delivery.

## Proved and sorry left

Closed one of the seven original holes:
`WeilConjectures.IntegralScalarExchange.rectangle_naturality`.
No holes added and no statements split off.

Six holes remain, all attached to
`lem-pur-integral-scalar-isomorphism-exchange`:

- `WeilConjectures.IntegralScalarExchange.openInverse_isIso`
- `WeilConjectures.IntegralScalarExchange.integralScalarIsomorphismExchange_integral`
- `WeilConjectures.IntegralScalarExchange.integralScalarIsomorphismExchange`
- `WeilConjectures.IntegralScalarExchange.scalarPull_finiteTor`
- `WeilConjectures.IntegralScalarExchange.rectangle_refinement`
- `WeilConjectures.IntegralScalarExchange.Systems.strictScalarIsomorphismExchange`

Their original statements, source citations and complete proof docstrings remain.
This is a partial delivery of the naturality clause; the integral, finite-system,
limit and refinement obligations remain open.

## No longer needed

None. No imports, nodes or modules are withdrawn. The naturality clause uses
natural-transformation operations as planned in Step 6. The remaining clauses
still need their recorded dependencies.

## Where the brief, the DAG or earlier work was wrong

No mathematical discrepancy found in the proved clause. The original right-path
representation led to 78.9–95.7 seconds of kernel checking and a deterministic
timeout, despite subsecond elaboration. The final representation shares the named
transformation between the path definition and proof, with explicit endpoints and
consistent native instances, avoiding the expensive conversion through derived
coefficient and sheafification choices.

Naturality needs no finite-Tor or scheme-isomorphism hypotheses, consistently with
its existing signature. The proof treats both paths separately and does not assume
that they are equal. The full coefficient-exchange and limit clauses remain open.

## Second reading by H5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
