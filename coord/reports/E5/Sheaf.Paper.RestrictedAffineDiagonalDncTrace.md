## What changed

Replaced the body of `WeilConjectures.PurityFiniteSetting.restrictedAffineDiagonalDncTrace`
with a categorical proof combining two distinct compatibility steps. The theorem's signature,
its public import, all existing definitions and the unit route are unchanged. Its new private
proof import is `Sheaf.Paper.RestrictedAffineDiagonalVectorIntegration`.

Added `RestrictedAffineDiagonalDncVectorCoordinates`: the concrete
`vectorModelSectionComparison` composes inverse identity pullback with the existing smooth
section exchange. Its theorem supplies compatible source and normal vector presentations
and a geometric DNC coordinate equation, without integration or beta.

Added `RestrictedAffineDiagonalVectorIntegration`: its theorem identifies the actual local
section trace with zero-section vector integration in any section-preserving vector
presentation, without DNC specialization or beta. Each unfinished component has its own
module, node, source, complete proof in words and explicit edge-case discussion.

The geometric module publicly imports only chart data and affine-trace constructions;
it does not import the restricted trace or the global refinement theorem. The integration
module publicly imports that coordinate API and the existing restricted trace, as required
by its statement. Profiling found subsecond declaration elaboration (541 ms cumulatively
for the geometric module and 97 ms for integration), with no slow declaration to repair.
All profiling options have been removed.

The combining proof obtains the geometric presentations, applies the integration identity,
uses the chart's existing `normalized` field, and cancels the mapped normal-coordinate
isomorphism. It then unfolds the definition of beta and uses its inverse equation.
No arbitrary witness is used to define data: the existential presentations are eliminated
only inside this proof of a proposition.

Validation: the final `lcompile.py --all` passed cleanly for all three delivered modules
(54.5 s geometric coordinates, 51.1 s integration, 43.9 s assigned theorem), with all
profiling options removed. The original theorem signature was also compared verbatim.

## Proved and sorry left

Closed the original hole in
`WeilConjectures.PurityFiniteSetting.restrictedAffineDiagonalDncTrace`
(node `lem-pur-restricted-affine-diagonal-dnc-trace`) by a complete proof from the two
components and `E.normalized`. Zero sorry remain in the assigned module.

Added two holes, each exactly a named public theorem with body `:= by sorry`:

- `WeilConjectures.PurityFiniteSetting.restrictedAffineDiagonalDncVectorCoordinates`
  (`lem-pur-restricted-affine-diagonal-dnc-vector-coordinates`).
- `WeilConjectures.PurityFiniteSetting.restrictedAffineDiagonalVectorIntegration`
  (`lem-pur-restricted-affine-diagonal-vector-integration`).

This is a decomposition, not a sorry-free proof of the underlying mathematics: one old
hole closed, two new holes added, net one additional hole. The new section-comparison
definition has a complete body with no sorry. The two statements are independent portions
of the argument: the first contains no integration, and the second no normal cone or DNC.
Neither assumes a chart beta nor restates the final identity with beta.

## No longer needed

No existing module, declaration or node is withdrawn; no public or private import of the
original assigned module was removed. No global pruning is claimed.

The assigned node now directly depends on the two components and the existing chart-data
node. DNC invariance and section geometry remain needed by the geometric component;
translation, vector integration and zero-section base change remain needed by the
integration component. Their modules are not globally pruned.

The proof no longer calls `diagonalOrientationRefinement` (node
`lem-pur-diagonal-orientation-refinement`) or `vectorBundlePurity` (node
`cor-pur-vector-bundle-purity`) as theorems: it uses the supplied chart's existing
normalization field. Their modules remain in the existing public import closure,
so no removal of those shared interfaces is attempted.
The assembly does not need `E.vectorModel`: its source/normal common presentation is
constructed by the geometric component and normalization applies to that presentation.

## Where the brief, the DAG or earlier work was wrong

The statement is unchanged and no counterexample was found. The DAG's prose omitted the
actual section-exchange coordinate identity and its separate integration identity. The
previous broad descriptions do not directly instantiate these local comparisons.

`AffineDiagonalDncCoordinateIdentity` is similar but concerns the global affine-diagonal
presentation. Import-direction checking reports that it already reaches this item, so
importing it here would close a cycle. It was not used as a circular proof dependency.
The new geometric statement constructs the restricted source and normal presentations
explicitly in its conclusion. The integration step uses the published zero-preserving
bundle base-change statement, which expressly does not require a linear bundle map.

Edge cases checked mathematically: for rank zero every coordinate list is empty and the
comparisons are unit comparisons; for an empty base the same constructions and equations
hold without a nonempty-point argument. Arbitrary allowed t,D are retained. Y need not
be absolutely separated: the geometric hypotheses required over the affine target are
provided by H, exactly as in the existing chart definitions.

## New nodes

`lem-pur-restricted-affine-diagonal-dnc-vector-coordinates` is the standard-pair Rees
calculation and its two section-exchange readings, in the actual restricted affine
coordinates. Its concrete comparison definition is built from existing maps.

`lem-pur-restricted-affine-diagonal-vector-integration` is restriction of the ordered
affine trace under a section-preserving vector presentation, using translation, the
vector-integration affine normalization and zero-preserving bundle base change.

Both retain chapter `sec-smooth-purity`, unit `sk-thm-smooth-purity`, and the ancestor
`thm-pur-diagonal-dualizing-object`. Blueprint searches for DNC and integration and
Mathlib searches with leanfinder, loogle and grep were run. Existing maps and the closest
global coordinate theorem were read; no usable duplicate of the restricted components
was found. No existing shared interface changed, so no change record or forced
adaptation is required.

## Second reading by E5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
