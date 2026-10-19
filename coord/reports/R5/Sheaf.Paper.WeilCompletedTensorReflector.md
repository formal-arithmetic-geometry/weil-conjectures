## What changed

Proved `AlgebraicGeometry.Scheme.wfCompletionMap_laws` in
`Sheaf.Paper.WeilCompletedTensorReflector`. The inverse of the reflector Hom bijection
satisfies its extension equation by `Equiv.apply_symm_apply`. Precomposition with the
completion unit is injective, so the identity and composition laws follow from that
extension equation and associativity. All declaration signatures, definitions, existing
docstrings, and imports are retained.

Rechecked against the current shared source after resuming: the only source difference
is the map-laws proof and its local elaboration option. The module compiles through
`lcompile.py` in 2.4 seconds. No extra axioms or holes were added.

## Proved and sorry left

Closed one of the item's two original holes:
`AlgebraicGeometry.Scheme.wfCompletionMap_laws`.

The one remaining hole is `AlgebraicGeometry.Scheme.wfCompletionReflector`
(blueprint: `lem-weil-pbc-ringed-koszul-completion-reflector`). It is unchanged.
No holes were added, and no statements were split off. The proved map laws depend on
the existing reflector theorem, as intended by the stage-3 dependency discipline.

## No longer needed

None. No imports, nodes, or modules were pruned. The remaining reflector theorem still
needs the general ringed-site completion route and its dependencies. The map laws use
only the already stated Hom bijection and the ordinary equivalence/category APIs.

## Where the brief, the DAG or earlier work was wrong

The item's DAG node describes the general small ringed-site theorem, whereas the item
also specializes to the actual pro-etale site, whose object and morphism universes differ.
Its remaining theorem must identify the transported completed-coefficient mapping fiber
and its exact unit with a strict derived-limit reflector. Reading
`RingedKoszulCompletionReflector`, `RingedKoszulSystem`, `RingedCechKoszulDualLimit`,
`ExtendedCechCompletionModel`, `IntrinsicCompletion`, `IntrinsicCompletionCompleted`,
and the related scalar and quotient comparison interfaces found no declaration that
already supplies this complete comparison. The general theorem fixes equal site object,
Hom, and coefficient universes; it cannot be applied directly to this site. Existing
independent-universe strict-limit results supply the limit functor but do not themselves
identify this fiber and unit. The remaining hole records that mathematical comparison;
this delivery does not change its statement or move it to another theorem.

## Second reading by R5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
